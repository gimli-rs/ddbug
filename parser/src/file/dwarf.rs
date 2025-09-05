use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap};
use std::mem;
use std::sync::Arc;

use gimli::Reader as GimliReader;
use object::{self, ObjectSection, ObjectSymbol};

use crate::cfi::{Cfi, CfiDirective};
use crate::file::{Architecture, Arena, DebugInfo, FileHash};
use crate::function::{
    Function, FunctionCall, FunctionCallIndirectOrigin, FunctionCallKind, FunctionCallOrigin,
    FunctionCallParameter, FunctionDetails, FunctionOffset, InlinedFunction, Parameter,
    ParameterOffset,
};
use crate::location::{Location, Piece, Register};
use crate::namespace::{Namespace, NamespaceKind};
use crate::range::Range;
use crate::source::Source;
use crate::types::{
    ArrayType, BaseType, BaseTypeEncoding, Endianity, EnumerationType, Enumerator, EnumeratorValue,
    FunctionType, Inherit, Member, MemberOffset, ParameterType, PointerToMemberType, StructType,
    SubrangeType, Type, TypeDef, TypeKind, TypeModifier, TypeModifierKind, TypeOffset, UnionType,
    UnspecifiedType, Variant, VariantPart,
};
use crate::unit::Unit;
use crate::variable::{LocalVariable, Variable, VariableOffset};
use crate::{Address, Id, Result, Size};

pub(crate) type RelocationMap = HashMap<usize, object::Relocation>;

fn add_relocations<'input, 'file, Object>(
    relocations: &mut RelocationMap,
    file: &'file Object,
    section: &Object::Section<'file>,
) where
    Object: object::Object<'input>,
{
    for (offset64, mut relocation) in section.relocations() {
        let offset = offset64 as usize;
        if offset as u64 != offset64 {
            continue;
        }
        let target = match relocation.target() {
            object::RelocationTarget::Symbol(index) => {
                if let Ok(symbol) = file.symbol_by_index(index) {
                    symbol.address()
                } else {
                    println!(
                        "Relocation with invalid symbol index {} for section {} at offset 0x{:08x}",
                        index.0,
                        section.name().unwrap(),
                        offset
                    );
                    continue;
                }
            }
            object::RelocationTarget::Section(index) => {
                if let Ok(section) = file.section_by_index(index) {
                    section.address()
                } else {
                    println!(
                        "Relocation with invalid section index {} for section {} at offset 0x{:08x}",
                        index.0,
                        section.name().unwrap(),
                        offset
                    );
                    continue;
                }
            }
            _ => {
                continue;
            }
        };
        match relocation.kind() {
            object::RelocationKind::Absolute => {
                let addend = target.wrapping_add(relocation.addend() as u64);
                relocation.set_addend(addend as i64);
                if relocations.insert(offset, relocation).is_some() {
                    println!(
                        "Multiple relocations for section {} at offset 0x{:08x}",
                        section.name().unwrap(),
                        offset
                    );
                }
            }
            object::RelocationKind::Relative => {
                let addend = target
                    .wrapping_add(relocation.addend() as u64)
                    .wrapping_sub(section.address())
                    .wrapping_sub(offset as u64);
                relocation.set_addend(addend as i64);
                if relocations.insert(offset, relocation).is_some() {
                    println!(
                        "Multiple relocations for section {} at offset 0x{:08x}",
                        section.name().unwrap(),
                        offset
                    );
                }
            }
            _ => {
                println!(
                    "Unsupported relocation for section {} at offset 0x{:08x}",
                    section.name().unwrap(),
                    offset
                );
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Relocate<'a, R: gimli::Reader<Offset = usize>> {
    relocations: &'a RelocationMap,
    section: R,
    reader: R,
}

impl<'a, R: gimli::Reader<Offset = usize>> Relocate<'a, R> {
    fn relocate(&self, offset: usize, value: u64) -> u64 {
        if let Some(relocation) = self.relocations.get(&offset) {
            match relocation.kind() {
                object::RelocationKind::Absolute | object::RelocationKind::Relative => {
                    if relocation.has_implicit_addend() {
                        // Use the explicit addend too, because it may have the symbol value.
                        return value.wrapping_add(relocation.addend() as u64);
                    } else {
                        return relocation.addend() as u64;
                    }
                }
                _ => {}
            }
        };
        value
    }
}

impl<'a, Endian> Relocate<'a, gimli::EndianSlice<'a, Endian>>
where
    Endian: gimli::Endianity,
{
    fn slice(&self) -> &'a [u8] {
        self.reader.slice()
    }
}

impl<'a, R: gimli::Reader<Offset = usize>> gimli::Reader for Relocate<'a, R> {
    type Endian = R::Endian;
    type Offset = R::Offset;

    fn read_address(&mut self, address_size: u8) -> gimli::Result<u64> {
        let offset = self.reader.offset_from(&self.section);
        let value = self.reader.read_address(address_size)?;
        Ok(self.relocate(offset, value))
    }

    fn read_length(&mut self, format: gimli::Format) -> gimli::Result<usize> {
        let offset = self.reader.offset_from(&self.section);
        let value = self.reader.read_length(format)?;
        <usize as gimli::ReaderOffset>::from_u64(self.relocate(offset, value as u64))
    }

    fn read_offset(&mut self, format: gimli::Format) -> gimli::Result<usize> {
        let offset = self.reader.offset_from(&self.section);
        let value = self.reader.read_offset(format)?;
        <usize as gimli::ReaderOffset>::from_u64(self.relocate(offset, value as u64))
    }

    fn read_sized_offset(&mut self, size: u8) -> gimli::Result<usize> {
        let offset = self.reader.offset_from(&self.section);
        let value = self.reader.read_sized_offset(size)?;
        <usize as gimli::ReaderOffset>::from_u64(self.relocate(offset, value as u64))
    }

    #[inline]
    fn split(&mut self, len: Self::Offset) -> gimli::Result<Self> {
        let mut other = self.clone();
        other.reader.truncate(len)?;
        self.reader.skip(len)?;
        Ok(other)
    }

    // All remaining methods simply delegate to `self.reader`.

    #[inline]
    fn endian(&self) -> Self::Endian {
        self.reader.endian()
    }

    #[inline]
    fn len(&self) -> Self::Offset {
        self.reader.len()
    }

    #[inline]
    fn empty(&mut self) {
        self.reader.empty()
    }

    #[inline]
    fn truncate(&mut self, len: Self::Offset) -> gimli::Result<()> {
        self.reader.truncate(len)
    }

    #[inline]
    fn offset_from(&self, base: &Self) -> Self::Offset {
        self.reader.offset_from(&base.reader)
    }

    #[inline]
    fn offset_id(&self) -> gimli::ReaderOffsetId {
        self.reader.offset_id()
    }

    #[inline]
    fn lookup_offset_id(&self, id: gimli::ReaderOffsetId) -> Option<Self::Offset> {
        self.reader.lookup_offset_id(id)
    }

    #[inline]
    fn find(&self, byte: u8) -> gimli::Result<Self::Offset> {
        self.reader.find(byte)
    }

    #[inline]
    fn skip(&mut self, len: Self::Offset) -> gimli::Result<()> {
        self.reader.skip(len)
    }

    #[inline]
    fn to_slice(&self) -> gimli::Result<Cow<[u8]>> {
        self.reader.to_slice()
    }

    #[inline]
    fn to_string(&self) -> gimli::Result<Cow<str>> {
        self.reader.to_string()
    }

    #[inline]
    fn to_string_lossy(&self) -> gimli::Result<Cow<str>> {
        self.reader.to_string_lossy()
    }

    #[inline]
    fn read_slice(&mut self, buf: &mut [u8]) -> gimli::Result<()> {
        self.reader.read_slice(buf)
    }
}

type Reader<'input, Endian> = Relocate<'input, gimli::EndianSlice<'input, Endian>>;

pub(crate) struct DwarfDebugInfo<'input, Endian>
where
    Endian: gimli::Endianity,
{
    endian: Endian,
    read: gimli::Dwarf<Reader<'input, Endian>>,
    frame: DwarfFrame<Reader<'input, Endian>>,
    arena: &'input Arena,
    units: Vec<gimli::Unit<Reader<'input, Endian>, usize>>,
}

impl<'input, Endian> DwarfDebugInfo<'input, Endian>
where
    Endian: gimli::Endianity,
{
    fn string(
        &self,
        dwarf_unit: &DwarfUnit<'input, Endian>,
        value: gimli::AttributeValue<Reader<'input, Endian>>,
    ) -> Option<&'input str> {
        self.read
            .attr_string(dwarf_unit, value)
            .map(|r| self.arena.add_string(r.slice()))
            .ok()
    }

    #[inline]
    fn addr(
        &self,
        dwarf_unit: &DwarfUnit<'input, Endian>,
        value: gimli::AttributeValue<Reader<'input, Endian>>,
    ) -> Option<u64> {
        self.read.attr_address(dwarf_unit, value).ok()?
    }

    #[inline]
    fn rangelist(
        &self,
        dwarf_unit: &DwarfUnit<'input, Endian>,
        value: gimli::AttributeValue<Reader<'input, Endian>>,
    ) -> Option<gimli::RangeListsOffset<usize>> {
        self.read.attr_ranges_offset(dwarf_unit, value).ok()?
    }

    #[inline]
    fn loclist(
        &self,
        dwarf_unit: &DwarfUnit<'input, Endian>,
        value: gimli::AttributeValue<Reader<'input, Endian>>,
    ) -> Option<gimli::LocationListsOffset<usize>> {
        self.read.attr_locations_offset(dwarf_unit, value).ok()?
    }

    fn tree(
        &self,
        offset: gimli::DebugInfoOffset,
    ) -> Option<(
        &DwarfUnit<'input, Endian>,
        gimli::EntriesTree<Reader<'input, Endian>>,
    )> {
        // FIXME: make this more efficient for large numbers of units
        // FIXME: cache lookups
        let offset = gimli::UnitSectionOffset::DebugInfoOffset(offset);
        for unit in &self.units {
            if let Some(offset) = offset.to_unit_offset(unit) {
                let tree = unit.entries_tree(Some(offset)).ok()?;
                return Some((unit, tree));
            }
        }
        None
    }

    fn type_tree(
        &self,
        offset: TypeOffset,
    ) -> Option<(
        &DwarfUnit<'input, Endian>,
        gimli::EntriesTree<Reader<'input, Endian>>,
    )> {
        offset
            .get()
            .and_then(|offset| self.tree(gimli::DebugInfoOffset(offset)))
    }

    fn function_tree(
        &self,
        offset: FunctionOffset,
    ) -> Option<(
        &DwarfUnit<'input, Endian>,
        gimli::EntriesTree<Reader<'input, Endian>>,
    )> {
        offset
            .get()
            .and_then(|offset| self.tree(gimli::DebugInfoOffset(offset)))
    }

    pub(crate) fn get_type(&self, offset: TypeOffset) -> Option<Type<'input>> {
        self.type_tree(offset).and_then(|(unit, mut tree)| {
            let node = tree.root().ok()?;
            parse_unnamed_type(self, unit, node).ok()?
        })
    }

    pub(crate) fn get_enumerators(
        &self,
        offset: TypeOffset,
        encoding: BaseTypeEncoding,
    ) -> Vec<Enumerator<'input>> {
        self.type_tree(offset)
            .and_then(|(unit, mut tree)| {
                let node = tree.root().ok()?;
                parse_enumerators(self, unit, node, encoding).ok()
            })
            .unwrap_or_default()
    }

    pub(crate) fn get_function_details(
        &self,
        offset: FunctionOffset,
        hash: &FileHash<'input>,
    ) -> Option<FunctionDetails<'input>> {
        self.function_tree(offset).and_then(|(unit, mut tree)| {
            let node = tree.root().ok()?;
            parse_subprogram_details(hash, self, unit, node).ok()
        })
    }

    pub(crate) fn get_cfi(&self, range: Range) -> Vec<Cfi> {
        self.frame.get_cfi(range).unwrap_or_default()
    }

    pub(crate) fn get_register_name(
        &self,
        machine: Architecture,
        register: Register,
    ) -> Option<&'static str> {
        let register_name = match machine {
            Architecture::Arm => gimli::Arm::register_name,
            Architecture::I386 => gimli::X86::register_name,
            Architecture::X86_64 => gimli::X86_64::register_name,
            _ => return None,
        };
        register_name(gimli::Register(register.0))
    }
}

type DwarfUnit<'input, Endian> = gimli::Unit<Reader<'input, Endian>>;

struct DwarfSubprogram<'input> {
    offset: gimli::UnitOffset,
    specification: FunctionOffset,
    abstract_origin: bool,
    function: Function<'input>,
}

struct DwarfVariable<'input> {
    offset: gimli::UnitOffset,
    specification: Option<VariableOffset>,
    variable: Variable<'input>,
}

pub(crate) fn parse<'input, Endian, Object>(
    endian: Endian,
    object: &Object,
    arena: &'input Arena,
) -> Result<(Vec<Unit<'input>>, DebugInfo<'input, Endian>)>
where
    Endian: gimli::Endianity,
    Object: object::Object<'input>,
{
    let get_section = |id: gimli::SectionId| -> Result<_> {
        let mut relocations = RelocationMap::default();
        let data = match object.section_by_name(id.name()) {
            Some(section) => {
                add_relocations(&mut relocations, object, &section);
                match section.uncompressed_data()? {
                    Cow::Borrowed(bytes) => bytes,
                    Cow::Owned(bytes) => arena.add_buffer(bytes),
                }
            }
            None => &[],
        };
        let relocations = arena.add_relocations(Box::new(relocations));
        let reader = gimli::EndianSlice::new(data, endian);
        Ok(Relocate {
            relocations,
            section: reader,
            reader,
        })
    };
    let read = gimli::Dwarf::load(get_section)?;

    let debug_frame = get_section(gimli::SectionId::DebugFrame)?;
    let eh_frame = get_section(gimli::SectionId::EhFrame)?;
    let mut bases = gimli::BaseAddresses::default();
    if let Some(section) = object.section_by_name(".eh_frame") {
        bases = bases.set_eh_frame(section.address());
    }
    if let Some(section) = object.section_by_name(".text") {
        bases = bases.set_text(section.address());
    }
    if let Some(section) = object.section_by_name(".got") {
        bases = bases.set_got(section.address());
    }
    let frame = DwarfFrame::new(debug_frame.into(), eh_frame.into(), bases);

    let mut dwarf = DwarfDebugInfo {
        endian,
        read,
        frame,
        arena,
        units: Vec::new(),
    };

    let mut units = Vec::new();
    let mut unit_headers = dwarf.read.units();
    while let Some(unit_header) = unit_headers.next()? {
        let dwarf_unit = dwarf.read.unit(unit_header)?;
        units.push(parse_unit(&mut dwarf, dwarf_unit)?);
    }
    Ok((units, DebugInfo::Dwarf(dwarf)))
}

fn parse_unit<'input, Endian>(
    dwarf: &mut DwarfDebugInfo<'input, Endian>,
    dwarf_unit: DwarfUnit<'input, Endian>,
) -> Result<Unit<'input>>
where
    Endian: gimli::Endianity,
{
    let mut unit = Unit::default();

    let mut subprograms = Vec::new();
    let mut variables = Vec::new();

    let mut tree = dwarf_unit.entries_tree(None)?;
    let root = tree.root()?;

    let entry = root.entry();
    if entry.tag() != gimli::DW_TAG_compile_unit {
        return Err(format!("unknown CU tag: {}", entry.tag()).into());
    }

    let mut ranges = None;
    let mut high_pc = None;
    let mut size = None;
    let mut attrs = entry.attrs();
    let mut found_unknown = false;
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                unit.name = dwarf.string(&dwarf_unit, attr.value()).map(Cow::Borrowed);
            }
            gimli::DW_AT_comp_dir => {
                unit.dir = dwarf.string(&dwarf_unit, attr.value()).map(Cow::Borrowed);
            }
            gimli::DW_AT_language => {
                if let gimli::AttributeValue::Language(language) = attr.value() {
                    unit.language = Some(language);
                }
            }
            gimli::DW_AT_low_pc => {
                unit.low_pc = dwarf.addr(&dwarf_unit, attr.value());
            }
            gimli::DW_AT_high_pc => match attr.value() {
                gimli::AttributeValue::Udata(val) => size = Some(val),
                val => {
                    if let Some(val) = dwarf.addr(&dwarf_unit, attr.value()) {
                        high_pc = Some(val);
                    } else {
                        debug!("unknown CU DW_AT_high_pc: {:?}", val);
                    }
                }
            },
            gimli::DW_AT_ranges => {
                ranges = dwarf.rangelist(&dwarf_unit, attr.value());
            }
            gimli::DW_AT_stmt_list
            | gimli::DW_AT_producer
            | gimli::DW_AT_entry_pc
            | gimli::DW_AT_APPLE_optimized
            | gimli::DW_AT_macro_info
            | gimli::DW_AT_GNU_macros
            | gimli::DW_AT_GNU_pubnames
            | gimli::DW_AT_sibling
            | gimli::DW_AT_str_offsets_base
            | gimli::DW_AT_addr_base
            | gimli::DW_AT_rnglists_base
            | gimli::DW_AT_loclists_base => {}
            _ => {
                debug!("unknown CU attribute: {} {:?}", attr.name(), attr.value());
                found_unknown = true;
            }
        }
    }

    // Find ranges from attributes in order of preference:
    // DW_AT_stmt_list, DW_AT_ranges, DW_AT_high_pc, DW_AT_size.
    // TODO: include variables in ranges.
    // TODO: copy logic from addr2line
    if let Some(program) = dwarf_unit.line_program.clone() {
        let mut rows = program.rows();
        let mut seq_addr = None;
        while let Some((_, row)) = rows.next_row()? {
            let addr = row.address();
            if row.end_sequence() {
                if let Some(seq_addr) = seq_addr {
                    // Sequences starting at 0 are probably invalid.
                    // TODO: is this always desired?
                    if seq_addr != 0 {
                        unit.ranges.push(Range {
                            begin: seq_addr,
                            end: addr,
                        });
                    }
                }
                seq_addr = None;
            } else if seq_addr.is_none() {
                seq_addr = Some(addr);
            }
        }
    } else if let Some(offset) = ranges {
        let mut ranges = dwarf.read.ranges(&dwarf_unit, offset)?;
        while let Some(range) = ranges.next()? {
            if range.begin < range.end {
                unit.ranges.push(Range {
                    begin: range.begin,
                    end: range.end,
                });
            }
        }
    } else if let Some(low_pc) = unit.low_pc {
        if let Some(size) = size {
            if high_pc.is_none() {
                high_pc = low_pc.checked_add(size);
            }
        }
        if let Some(high_pc) = high_pc {
            unit.ranges.push(Range {
                begin: low_pc,
                end: high_pc,
            });
        }
    }
    unit.ranges.sort();
    // Ignore low_pc attribute if there is any range.
    unit.low_pc = unit.ranges.list().first().map(|range| range.begin);

    let namespace = None;
    parse_namespace_children(
        &mut unit,
        dwarf,
        &dwarf_unit,
        &mut subprograms,
        &mut variables,
        &namespace,
        root.children(),
    )?;

    fixup_subprogram_specifications(
        &mut unit,
        dwarf,
        &dwarf_unit,
        &mut subprograms,
        &mut variables,
    )?;
    fixup_variable_specifications(&mut unit, dwarf, &dwarf_unit, &mut variables)?;

    if found_unknown {
        debug!(
            "found one or more unknown CU attributes for unit: {:#?}",
            unit
        );
    }

    dwarf.units.push(dwarf_unit);
    Ok(unit)
}

#[inline(never)]
fn fixup_subprogram_specifications<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    // Convert functions to BTreeMap
    // TODO: it'd be cleaner if parse_subprogram() added functions to a BTreeMap initially,
    // so that we didn't have to keep updating it.
    let mut functions = BTreeMap::new();
    for function in unit.functions.drain(..) {
        functions.insert(function.offset, function);
    }

    let mut defer = Vec::new();

    while !subprograms.is_empty() {
        let mut progress = false;

        mem::swap(&mut defer, subprograms);
        for mut subprogram in defer.drain(..) {
            if inherit_subprogram(
                &functions,
                &mut subprogram.function,
                subprogram.specification,
                subprogram.abstract_origin,
            ) {
                let mut tree = dwarf_unit.entries_tree(Some(subprogram.offset))?;
                parse_subprogram_children(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &mut subprogram.function,
                    tree.root()?.children(),
                )?;
                let offset = subprogram.offset.to_unit_section_offset(dwarf_unit);
                functions.insert(offset.into(), subprogram.function);
                for function in unit.functions.drain(..) {
                    functions.insert(function.offset, function);
                }
                progress = true;
            } else {
                subprograms.push(subprogram);
            }
        }

        if !progress {
            debug!(
                "invalid specification for {} subprograms",
                subprograms.len()
            );
            mem::swap(&mut defer, subprograms);
            for mut subprogram in defer.drain(..) {
                let mut tree = dwarf_unit.entries_tree(Some(subprogram.offset))?;
                parse_subprogram_children(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &mut subprogram.function,
                    tree.root()?.children(),
                )?;
                let offset = subprogram.offset.to_unit_section_offset(dwarf_unit);
                functions.insert(offset.into(), subprogram.function);
                for function in unit.functions.drain(..) {
                    functions.insert(function.offset, function);
                }
            }
            // And keep going, because parse_subprogram_children() may have added more.
        }
    }

    unit.functions = functions.into_values().collect();
    Ok(())
}

#[inline(never)]
fn fixup_variable_specifications<'input, Endian>(
    unit: &mut Unit<'input>,
    _dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    variables: &mut Vec<DwarfVariable<'input>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    // Convert variables to BTreeMap
    let mut variable_map = BTreeMap::new();
    for variable in unit.variables.drain(..) {
        variable_map.insert(variable.offset, variable);
    }

    loop {
        let mut progress = false;
        let mut defer = Vec::new();

        for mut variable in variables.drain(..) {
            match variable.specification.and_then(|v| variable_map.get(&v)) {
                Some(specification) => {
                    let variable = &mut variable.variable;
                    variable.namespace = specification.namespace.clone();
                    if variable.name.is_none() {
                        variable.name = specification.name;
                    }
                    if variable.linkage_name.is_none() {
                        variable.linkage_name = specification.linkage_name;
                    }
                    if variable.ty.is_none() {
                        variable.ty = specification.ty;
                    }
                }
                None => {
                    defer.push(variable);
                    continue;
                }
            }
            let offset = variable.offset.to_unit_section_offset(dwarf_unit);
            variable_map.insert(offset.into(), variable.variable);
            progress = true;
        }

        if defer.is_empty() {
            break;
        }
        if !progress {
            debug!("invalid specification for {} variables", defer.len());
            for variable in variables.drain(..) {
                let offset = variable.offset.to_unit_section_offset(dwarf_unit);
                variable_map.insert(offset.into(), variable.variable);
            }
            break;
        }
        *variables = defer;
    }

    unit.variables = variable_map.into_values().collect();
    Ok(())
}

fn parse_namespace_children<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_namespace => {
                parse_namespace(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_subprogram => {
                parse_subprogram(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_variable => {
                let variable = parse_variable(unit, dwarf, dwarf_unit, namespace.clone(), child)?;
                if variable.specification.is_some() {
                    // Delay handling specification in case it comes later.
                    variables.push(variable);
                } else {
                    unit.variables.push(variable.variable);
                }
            }
            gimli::DW_TAG_dwarf_procedure
            | gimli::DW_TAG_imported_declaration
            | gimli::DW_TAG_imported_module => {}
            tag => {
                if !parse_type(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    namespace,
                    child,
                )? {
                    debug!("unknown namespace child tag: {}", tag);
                }
            }
        }
    }
    Ok(())
}

fn parse_namespace<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut name = None;

    let entry = node.entry();
    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_decl_file | gimli::DW_AT_decl_line | gimli::DW_AT_decl_column => {}
            _ => debug!(
                "unknown namespace attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let namespace = Some(Namespace::new(namespace, name, NamespaceKind::Namespace));
    parse_namespace_children(
        unit,
        dwarf,
        dwarf_unit,
        subprograms,
        variables,
        &namespace,
        node.children(),
    )
}

/*
fn is_type_tag(tag: gimli::DwTag) -> bool {
    match tag {
        gimli::DW_TAG_typedef |
        gimli::DW_TAG_class_type | gimli::DW_TAG_structure_type |
        gimli::DW_TAG_union_type |
        gimli::DW_TAG_enumeration_type |
        gimli::DW_TAG_unspecified_type |
        gimli::DW_TAG_base_type |
        gimli::DW_TAG_array_type |
        gimli::DW_TAG_subroutine_type |
        gimli::DW_TAG_ptr_to_member_type |
        gimli::DW_TAG_pointer_type |
        gimli::DW_TAG_reference_type |
        gimli::DW_TAG_const_type |
        gimli::DW_TAG_packed_type |
        gimli::DW_TAG_volatile_type |
        gimli::DW_TAG_restrict_type |
        gimli::DW_TAG_shared_type |
        gimli::DW_TAG_rvalue_reference_type |
        gimli::DW_TAG_atomic_type => true,
        _ => false,
    }
}
*/

fn parse_type<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<bool>
where
    Endian: gimli::Endianity,
{
    let tag = node.entry().tag();
    let mut ty = Type::default();
    let offset = node.entry().offset();
    let offset = offset.to_unit_section_offset(dwarf_unit);
    ty.offset = offset.into();
    ty.kind = match tag {
        gimli::DW_TAG_base_type => TypeKind::Base(parse_base_type(dwarf, dwarf_unit, node)?),
        gimli::DW_TAG_typedef => TypeKind::Def(parse_typedef(dwarf, dwarf_unit, namespace, node)?),
        // TODO: distinguish between class and structure
        gimli::DW_TAG_class_type | gimli::DW_TAG_structure_type => {
            TypeKind::Struct(parse_structure_type(
                unit,
                dwarf,
                dwarf_unit,
                subprograms,
                variables,
                namespace,
                node,
            )?)
        }
        gimli::DW_TAG_union_type => TypeKind::Union(parse_union_type(
            unit,
            dwarf,
            dwarf_unit,
            subprograms,
            variables,
            namespace,
            node,
        )?),
        gimli::DW_TAG_enumeration_type => TypeKind::Enumeration(parse_enumeration_type(
            ty.offset,
            unit,
            dwarf,
            dwarf_unit,
            subprograms,
            variables,
            namespace,
            node,
        )?),
        gimli::DW_TAG_unspecified_type => {
            TypeKind::Unspecified(parse_unspecified_type(dwarf, dwarf_unit, namespace, node)?)
        }
        // Parse unnamed types for validation, but don't store them.
        _ => return parse_unnamed_type(dwarf, dwarf_unit, node).map(|x| x.is_some()),
    };
    unit.types.push(ty);
    Ok(true)
}

fn parse_unnamed_type<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<Option<Type<'input>>>
where
    Endian: gimli::Endianity,
{
    let tag = node.entry().tag();
    let mut ty = Type::default();
    let offset = node.entry().offset();
    let offset = offset.to_unit_section_offset(dwarf_unit);
    ty.offset = offset.into();
    ty.kind = match tag {
        gimli::DW_TAG_array_type => TypeKind::Array(parse_array_type(dwarf, dwarf_unit, node)?),
        gimli::DW_TAG_subrange_type => {
            TypeKind::Subrange(parse_subrange_type(dwarf, dwarf_unit, node)?)
        }
        gimli::DW_TAG_subroutine_type => {
            TypeKind::Function(parse_subroutine_type(dwarf, dwarf_unit, node)?)
        }
        gimli::DW_TAG_ptr_to_member_type => {
            TypeKind::PointerToMember(parse_pointer_to_member_type(dwarf, dwarf_unit, node)?)
        }
        gimli::DW_TAG_pointer_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Pointer,
        )?),
        gimli::DW_TAG_reference_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Reference,
        )?),
        gimli::DW_TAG_const_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Const,
        )?),
        gimli::DW_TAG_packed_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Packed,
        )?),
        gimli::DW_TAG_volatile_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Volatile,
        )?),
        gimli::DW_TAG_restrict_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Restrict,
        )?),
        gimli::DW_TAG_shared_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Shared,
        )?),
        gimli::DW_TAG_rvalue_reference_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::RvalueReference,
        )?),
        gimli::DW_TAG_atomic_type => TypeKind::Modifier(parse_type_modifier(
            dwarf,
            dwarf_unit,
            node,
            TypeModifierKind::Atomic,
        )?),
        _ => return Ok(None),
    };
    Ok(Some(ty))
}

fn parse_type_modifier<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
    kind: TypeModifierKind,
) -> Result<TypeModifier<'input>>
where
    Endian: gimli::Endianity,
{
    let mut modifier = TypeModifier {
        kind,
        ty: TypeOffset::none(),
        name: None,
        byte_size: Size::none(),
        address_size: Some(u64::from(dwarf_unit.header.address_size())),
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                modifier.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    modifier.ty = offset;
                }
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    modifier.byte_size = Size::new(byte_size);
                }
            }
            gimli::DW_AT_artificial => {}
            _ => debug!(
                "unknown type modifier attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown type modifier child tag: {}", tag);
            }
        }
    }
    Ok(modifier)
}

fn parse_base_type<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<BaseType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = BaseType::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                ty.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    ty.byte_size = Size::new(byte_size);
                }
            }
            gimli::DW_AT_encoding => {
                if let gimli::AttributeValue::Encoding(val) = attr.value() {
                    ty.encoding = match val {
                        gimli::DW_ATE_boolean => BaseTypeEncoding::Boolean,
                        gimli::DW_ATE_address => BaseTypeEncoding::Address,
                        gimli::DW_ATE_signed => BaseTypeEncoding::Signed,
                        gimli::DW_ATE_signed_char => BaseTypeEncoding::SignedChar,
                        gimli::DW_ATE_unsigned => BaseTypeEncoding::Unsigned,
                        gimli::DW_ATE_unsigned_char => BaseTypeEncoding::UnsignedChar,
                        gimli::DW_ATE_float => BaseTypeEncoding::Float,
                        _ => {
                            debug!("unknown base type encoding: {} {:?}", attr.name(), val);
                            BaseTypeEncoding::Other
                        }
                    }
                }
            }
            gimli::DW_AT_endianity => {
                if let gimli::AttributeValue::Endianity(val) = attr.value() {
                    ty.endianity = match val {
                        gimli::DW_END_default => Endianity::Default,
                        gimli::DW_END_big => Endianity::Big,
                        gimli::DW_END_little => Endianity::Little,
                        _ => {
                            debug!("unknown base type endianity: {} {:?}", attr.name(), val);
                            Endianity::Default
                        }
                    }
                }
            }
            gimli::DW_AT_artificial | gimli::DW_AT_decimal_scale => {}
            _ => debug!(
                "unknown base type attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown base type child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_typedef<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<TypeDef<'input>>
where
    Endian: gimli::Endianity,
{
    let mut typedef = TypeDef {
        namespace: namespace.clone(),
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                typedef.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    typedef.ty = offset;
                }
            }
            gimli::DW_AT_decl_file => {
                parse_source_file(dwarf, dwarf_unit, &attr, &mut typedef.source)
            }
            gimli::DW_AT_decl_line => parse_source_line(&attr, &mut typedef.source),
            gimli::DW_AT_decl_column => parse_source_column(&attr, &mut typedef.source),
            gimli::DW_AT_alignment => {}
            _ => debug!(
                "unknown typedef attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown typedef child tag: {}", tag);
            }
        }
    }
    Ok(typedef)
}

fn parse_structure_type<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<StructType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = StructType {
        namespace: namespace.clone(),
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                ty.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    ty.byte_size = Size::new(byte_size);
                }
            }
            gimli::DW_AT_declaration => {
                if let gimli::AttributeValue::Flag(flag) = attr.value() {
                    ty.declaration = flag;
                }
            }
            gimli::DW_AT_decl_file => parse_source_file(dwarf, dwarf_unit, &attr, &mut ty.source),
            gimli::DW_AT_decl_line => parse_source_line(&attr, &mut ty.source),
            gimli::DW_AT_decl_column => parse_source_column(&attr, &mut ty.source),
            gimli::DW_AT_containing_type | gimli::DW_AT_alignment | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown struct attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let namespace = Some(Namespace::new(&ty.namespace, ty.name, NamespaceKind::Type));
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_subprogram => {
                parse_subprogram(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_member => {
                parse_member(&mut ty.members, unit, dwarf, dwarf_unit, &namespace, child)?;
            }
            gimli::DW_TAG_inheritance => {
                parse_inheritance(&mut ty.inherits, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_variant_part => {
                parse_variant_part(
                    &mut ty.members,
                    &mut ty.variant_parts,
                    unit,
                    dwarf,
                    dwarf_unit,
                    &namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_template_type_parameter
            | gimli::DW_TAG_template_value_parameter
            | gimli::DW_TAG_GNU_template_parameter_pack => {}
            tag => {
                if !parse_type(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )? {
                    debug!("unknown struct child tag: {}", tag);
                }
            }
        }
    }
    Ok(ty)
}

fn parse_union_type<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<UnionType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = UnionType {
        namespace: namespace.clone(),
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                ty.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    ty.byte_size = Size::new(byte_size);
                }
            }
            gimli::DW_AT_declaration => {
                if let gimli::AttributeValue::Flag(flag) = attr.value() {
                    ty.declaration = flag;
                }
            }
            gimli::DW_AT_decl_file => parse_source_file(dwarf, dwarf_unit, &attr, &mut ty.source),
            gimli::DW_AT_decl_line => parse_source_line(&attr, &mut ty.source),
            gimli::DW_AT_decl_column => parse_source_column(&attr, &mut ty.source),
            gimli::DW_AT_alignment | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown union attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let namespace = Some(Namespace::new(&ty.namespace, ty.name, NamespaceKind::Type));
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_subprogram => {
                parse_subprogram(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_member => {
                parse_member(&mut ty.members, unit, dwarf, dwarf_unit, &namespace, child)?;
            }
            gimli::DW_TAG_template_type_parameter => {}
            tag => {
                if !parse_type(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )? {
                    debug!("unknown union child tag: {}", tag);
                }
            }
        }
    }
    Ok(ty)
}

fn parse_variant_part<'input, Endian>(
    members: &mut Vec<Member<'input>>,
    variant_parts: &mut Vec<VariantPart<'input>>,
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut variant_part = VariantPart::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_discr => {
                if let Some(offset) = parse_member_offset(dwarf_unit, &attr) {
                    variant_part.discr = offset;
                }
            }
            gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown variant_part attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_member => {
                // Treat any members in the variant_part the same as any other member.
                // TODO: maybe set a field to indicate which variant part it belongs to.
                parse_member(members, unit, dwarf, dwarf_unit, namespace, child)?;
            }
            gimli::DW_TAG_variant => {
                parse_variant(
                    &mut variant_part.variants,
                    unit,
                    dwarf,
                    dwarf_unit,
                    namespace,
                    child,
                )?;
            }
            tag => {
                debug!("unknown variant_part child tag: {}", tag);
            }
        }
    }

    variant_parts.push(variant_part);
    Ok(())
}

fn parse_variant<'input, Endian>(
    variants: &mut Vec<Variant<'input>>,
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut variant = Variant::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_discr_value => {
                if let Some(value) = attr.udata_value() {
                    variant.discr_value = Some(value);
                }
            }
            gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown variant attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_member => {
                parse_member(
                    &mut variant.members,
                    unit,
                    dwarf,
                    dwarf_unit,
                    namespace,
                    child,
                )?;
            }
            // subrange type encountered here for Ada.
            // TODO: not sure which types are valid here.
            // Maybe need to call parse_type(), but don't have all the parameters
            // needed for it yet.
            gimli::DW_TAG_subrange_type => {
                parse_subrange_type(dwarf, dwarf_unit, child)?;
            }
            tag => {
                debug!("unknown variant child tag: {}", tag);
            }
        }
    }

    // Rust uses a single struct member for its variants, and the size of this
    // struct is set to be the same as the size of the enum. This makes it hard
    // to see the exact layout of the enum, so it's more helpful to treat the
    // struct members as being owned by the variant instead.
    if unit.language == Some(gimli::DW_LANG_Rust) && variant.members.len() == 1 {
        if let Some(offset) = variant.members[0].ty.get() {
            let offset = gimli::UnitSectionOffset::DebugInfoOffset(gimli::DebugInfoOffset(offset));
            if let Some(offset) = offset.to_unit_offset(dwarf_unit) {
                let mut tree = dwarf_unit.entries_tree(Some(offset))?;
                let node = tree.root()?;
                if node.entry().tag() == gimli::DW_TAG_structure_type {
                    // Rust gives the struct a name that matches the variant.
                    if let Some(attr) = node.entry().attr_value(gimli::DW_AT_name)? {
                        variant.name = dwarf.string(dwarf_unit, attr);
                    }

                    variant.source = variant.members.pop().unwrap().source;

                    // Parse the struct's members as our own.
                    variant.members.clear();
                    let mut iter = node.children();
                    while let Some(child) = iter.next()? {
                        if child.entry().tag() == gimli::DW_TAG_member {
                            parse_member(
                                &mut variant.members,
                                unit,
                                dwarf,
                                dwarf_unit,
                                namespace,
                                child,
                            )?;
                        }
                    }
                }
            }
        }
    }

    variants.push(variant);
    Ok(())
}

fn parse_member<'input, Endian>(
    members: &mut Vec<Member<'input>>,
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut member = Member::default();
    let offset = node.entry().offset();
    let offset = offset.to_unit_section_offset(dwarf_unit);
    member.offset = offset.into();
    let mut bit_offset = None;
    let mut byte_size = None;
    let mut declaration = false;

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                member.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    member.ty = offset;
                }
            }
            gimli::DW_AT_data_member_location => {
                if let Some(offset) = parse_data_member_location(dwarf, dwarf_unit, &attr) {
                    member.bit_offset = offset;
                }
            }
            gimli::DW_AT_data_bit_offset => {
                if let Some(bit_offset) = attr.udata_value() {
                    member.bit_offset = bit_offset;
                }
            }
            gimli::DW_AT_bit_offset => {
                bit_offset = attr.udata_value();
            }
            gimli::DW_AT_byte_size => {
                byte_size = attr.udata_value();
            }
            gimli::DW_AT_bit_size => {
                if let Some(bit_size) = attr.udata_value() {
                    member.bit_size = Size::new(bit_size);
                }
            }
            gimli::DW_AT_declaration => {
                declaration = true;
            }
            gimli::DW_AT_decl_file => {
                parse_source_file(dwarf, dwarf_unit, &attr, &mut member.source);
            }
            gimli::DW_AT_decl_line => {
                parse_source_line(&attr, &mut member.source);
            }
            gimli::DW_AT_decl_column => {
                parse_source_column(&attr, &mut member.source);
            }
            gimli::DW_AT_external
            | gimli::DW_AT_accessibility
            | gimli::DW_AT_artificial
            | gimli::DW_AT_const_value
            | gimli::DW_AT_alignment
            | gimli::DW_AT_sibling => {}
            _ => {
                debug!(
                    "unknown member attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                );
            }
        }
    }

    if declaration {
        // This is a C++ static data member. Parse it as a variable instead.
        // Note: the DWARF 5 standard says static members should use DW_TAG_variable,
        // but at least clang 3.7.1 uses DW_TAG_member.
        let variable = parse_variable(unit, dwarf, dwarf_unit, namespace.clone(), node)?;
        if variable.specification.is_some() {
            debug!(
                "specification on variable declaration at offset 0x{:x}",
                variable.offset.0
            );
        }
        unit.variables.push(variable.variable);
        return Ok(());
    }

    if let (Some(bit_offset), Some(bit_size)) = (bit_offset, member.bit_size.get()) {
        // DWARF version 2/3, but allowed in later versions for compatibility.
        // The data member is a bit field contained in an anonymous object.
        // member.bit_offset starts as the offset of the anonymous object.
        // byte_size is the size of the anonymous object.
        // bit_offset is the offset from the anonymous object MSB to the bit field MSB.
        // bit_size is the size of the bit field.
        if dwarf.endian.is_big_endian() {
            // For big endian, the MSB is the first bit, so we simply add bit_offset,
            // and byte_size is unneeded.
            member.bit_offset = member.bit_offset.wrapping_add(bit_offset);
        } else {
            // For little endian, we have to work backwards, so we need byte_size.
            if let Some(byte_size) = byte_size {
                // First find the offset of the MSB of the anonymous object.
                member.bit_offset = member.bit_offset.wrapping_add(byte_size * 8);
                // Then go backwards to the LSB of the bit field.
                member.bit_offset = member
                    .bit_offset
                    .wrapping_sub(bit_offset.wrapping_add(bit_size));
            } else {
                // DWARF version 2/3 says the byte_size can be inferred,
                // but it is unclear when this would be useful.
                // Delay implementing this until needed.
                debug!("missing byte_size for bit field offset");
            }
        }
    } else if byte_size.is_some() {
        // TODO: should this set member.bit_size?
        debug!("ignored member byte_size");
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown member child tag: {}", tag);
            }
        }
    }
    members.push(member);
    Ok(())
}

fn parse_inheritance<'input, Endian>(
    inherits: &mut Vec<Inherit>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut inherit = Inherit::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    inherit.ty = offset;
                }
            }
            gimli::DW_AT_data_member_location => {
                if let Some(offset) = parse_data_member_location(dwarf, dwarf_unit, &attr) {
                    inherit.bit_offset = offset;
                }
            }
            gimli::DW_AT_accessibility | gimli::DW_AT_virtuality | gimli::DW_AT_sibling => {}
            _ => {
                debug!(
                    "unknown inheritance attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                );
            }
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown inheritance child tag: {}", tag);
            }
        }
    }
    inherits.push(inherit);
    Ok(())
}

fn parse_data_member_location<Endian>(
    dwarf: &DwarfDebugInfo<'_, Endian>,
    dwarf_unit: &DwarfUnit<'_, Endian>,
    attr: &gimli::Attribute<Reader<Endian>>,
) -> Option<u64>
where
    Endian: gimli::Endianity,
{
    match attr.value() {
        gimli::AttributeValue::Udata(v) => return Some(v * 8),
        gimli::AttributeValue::Sdata(v) => {
            if v >= 0 {
                return Some((v as u64) * 8);
            } else {
                debug!("DW_AT_data_member_location is negative: {}", v)
            }
        }
        gimli::AttributeValue::Exprloc(expr) => {
            if let Some(offset) = evaluate_member_location(dwarf, dwarf_unit, expr) {
                return Some(offset);
            }
        }
        gimli::AttributeValue::LocationListsRef(offset) => {
            if dwarf_unit.header.version() == 3 {
                // HACK: while gimli is technically correct, in my experience this
                // is more likely to be a constant. This can happen for large
                // structs.
                return Some(offset.0 as u64 * 8);
            } else {
                debug!("loclist for member: {:?}", attr.value());
            }
        }
        _ => {
            debug!("unknown DW_AT_data_member_location: {:?}", attr.value());
        }
    }
    None
}

fn parse_enumeration_type<'input, Endian>(
    offset: TypeOffset,
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<EnumerationType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = EnumerationType {
        offset,
        namespace: namespace.clone(),
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                ty.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    ty.ty = offset;
                }
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    ty.byte_size = Size::new(byte_size);
                }
            }
            gimli::DW_AT_declaration => {
                if let gimli::AttributeValue::Flag(flag) = attr.value() {
                    ty.declaration = flag;
                }
            }
            gimli::DW_AT_decl_file => parse_source_file(dwarf, dwarf_unit, &attr, &mut ty.source),
            gimli::DW_AT_decl_line => parse_source_line(&attr, &mut ty.source),
            gimli::DW_AT_decl_column => parse_source_column(&attr, &mut ty.source),
            gimli::DW_AT_sibling
            | gimli::DW_AT_encoding
            | gimli::DW_AT_alignment
            | gimli::DW_AT_enum_class => {}
            _ => debug!(
                "unknown enumeration attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let namespace = Some(Namespace::new(&ty.namespace, ty.name, NamespaceKind::Type));
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_subprogram => {
                parse_subprogram(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_enumerator => {}
            tag => {
                debug!("unknown enumeration child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_enumerators<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
    encoding: BaseTypeEncoding,
) -> Result<Vec<Enumerator<'input>>>
where
    Endian: gimli::Endianity,
{
    let mut enumerators = Vec::new();
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_enumerator => {
                enumerators.push(parse_enumerator(dwarf, dwarf_unit, child, encoding)?);
            }
            _ => {}
        }
    }
    Ok(enumerators)
}

fn parse_enumerator<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
    encoding: BaseTypeEncoding,
) -> Result<Enumerator<'input>>
where
    Endian: gimli::Endianity,
{
    let mut enumerator = Enumerator::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                enumerator.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_const_value => {
                let value = if encoding.is_unsigned() {
                    attr.udata_value().map(EnumeratorValue::Unsigned)
                } else {
                    attr.sdata_value().map(EnumeratorValue::Signed)
                };
                if let Some(value) = value {
                    enumerator.value = value;
                } else {
                    debug!("unknown enumerator const_value: {:?}", attr.value());
                }
            }
            _ => debug!(
                "unknown enumerator attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown enumerator child tag: {}", tag);
            }
        }
    }
    Ok(enumerator)
}

fn parse_array_type<'input, Endian>(
    _dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<ArrayType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut array = ArrayType::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    array.ty = offset;
                }
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    array.byte_size = Size::new(byte_size);
                }
            }
            gimli::DW_AT_name | gimli::DW_AT_GNU_vector | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown array attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut counts = Vec::new();
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_subrange_type => {
                let mut count = None;
                let mut lower = None;
                let mut upper = None;
                let mut attrs = child.entry().attrs();
                while let Some(attr) = attrs.next()? {
                    match attr.name() {
                        gimli::DW_AT_count => {
                            count = attr.udata_value();
                        }
                        gimli::DW_AT_lower_bound => {
                            lower = attr.udata_value();
                        }
                        gimli::DW_AT_upper_bound => {
                            upper = attr.udata_value();
                        }
                        gimli::DW_AT_type => {}
                        _ => debug!(
                            "unknown array subrange attribute: {} {:?}",
                            attr.name(),
                            attr.value()
                        ),
                    }
                }
                if count.is_none() {
                    if let Some(upper) = upper {
                        // TODO: use default lower bound for language
                        let lower = lower.unwrap_or(0);
                        count = u64::checked_sub(upper, lower)
                            .and_then(|count| u64::checked_add(count, 1));
                        if count.is_none() {
                            debug!("overflow for array bound: {}", upper);
                        }
                    }
                }
                if let Some(count) = count {
                    counts.push(Size::new(count));
                } else {
                    // Unknown dimensions.
                    counts.push(Size::none());
                }
            }
            tag => {
                debug!("unknown array child tag: {}", tag);
            }
        }
    }
    if counts.len() == 1 {
        array.count = counts[0];
    } else if !counts.is_empty() {
        array.counts = counts.into_boxed_slice();
    }
    Ok(array)
}

fn parse_subrange_type<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<SubrangeType<'input>>
where
    Endian: gimli::Endianity,
{
    // TODO: lower bound default should depend on language
    let mut subrange = SubrangeType::default();
    let mut count = None;

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                subrange.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    subrange.ty = offset;
                }
            }
            gimli::DW_AT_lower_bound => {
                if let Some(lower) = attr.udata_value() {
                    subrange.lower = Some(lower);
                }
            }
            gimli::DW_AT_upper_bound => {
                if let Some(upper) = attr.udata_value() {
                    subrange.upper = Some(upper);
                }
            }
            gimli::DW_AT_count => {
                if let Some(v) = attr.udata_value() {
                    count = Some(v);
                }
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    subrange.byte_size = Size::new(byte_size);
                }
            }
            gimli::DW_AT_artificial => {}
            _ => debug!(
                "unknown subrange attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    if let (Some(lower), Some(count)) = (subrange.lower, count) {
        subrange.upper = Some(lower + count);
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown subrange child tag: {}", tag);
            }
        }
    }
    Ok(subrange)
}

fn parse_subroutine_type<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<FunctionType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut function = FunctionType {
        // Go treats subroutine types as pointers.
        // Not sure if this is valid for all languages.
        byte_size: Size::new(u64::from(dwarf_unit.header.address_size())),
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    function.return_type = offset;
                }
            }
            gimli::DW_AT_name | gimli::DW_AT_prototyped | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown subroutine attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter => {
                parse_parameter_type(&mut function.parameters, dwarf, dwarf_unit, child)?;
            }
            tag => {
                debug!("unknown subroutine child tag: {}", tag);
            }
        }
    }
    Ok(function)
}

fn parse_unspecified_type<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<UnspecifiedType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = UnspecifiedType {
        namespace: namespace.clone(),
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                ty.name = dwarf.string(dwarf_unit, attr.value());
            }
            _ => debug!(
                "unknown unspecified type attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown unspecified type child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_pointer_to_member_type<'input, Endian>(
    _dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<PointerToMemberType>
where
    Endian: gimli::Endianity,
{
    let mut ty = PointerToMemberType {
        address_size: Some(u64::from(dwarf_unit.header.address_size())),
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    ty.ty = offset;
                }
            }
            gimli::DW_AT_containing_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    ty.containing_ty = offset;
                }
            }
            gimli::DW_AT_byte_size => {
                if let Some(byte_size) = attr.udata_value() {
                    ty.byte_size = Size::new(byte_size);
                }
            }
            _ => debug!(
                "unknown ptr_to_member type attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown ptr_to_member type child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_subprogram<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let offset = node.entry().offset();
    let mut function = Function {
        id: Id::new(0),
        offset: offset.to_unit_section_offset(dwarf_unit).into(),
        namespace: namespace.clone(),
        name: None,
        symbol_name: None,
        linkage_name: None,
        source: Source::default(),
        address: Address::none(),
        size: Size::none(),
        ranges: Vec::new(),
        inline: false,
        declaration: false,
        parameters: Vec::new(),
        return_type: TypeOffset::none(),
    };

    let mut specification = None;
    let mut abstract_origin = false;
    let mut high_pc = None;
    let mut size = None;
    let mut ranges = None;

    let entry = node.entry();
    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                function.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_linkage_name | gimli::DW_AT_MIPS_linkage_name => {
                function.linkage_name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_decl_file => {
                parse_source_file(dwarf, dwarf_unit, &attr, &mut function.source)
            }
            gimli::DW_AT_decl_line => parse_source_line(&attr, &mut function.source),
            gimli::DW_AT_decl_column => parse_source_column(&attr, &mut function.source),
            gimli::DW_AT_inline => {
                if let gimli::AttributeValue::Inline(val) = attr.value() {
                    match val {
                        gimli::DW_INL_inlined | gimli::DW_INL_declared_inlined => {
                            function.inline = true
                        }
                        _ => function.inline = false,
                    }
                }
            }
            gimli::DW_AT_low_pc => {
                let val = attr.value();
                if let Some(addr) = dwarf.addr(dwarf_unit, val) {
                    if addr != 0 || unit.low_pc == Some(0) {
                        function.address = Address::new(addr);
                    }
                } else {
                    debug!("found subprogram low_pc with unknown address: {:?}", val);
                }
            }
            gimli::DW_AT_high_pc => match attr.value() {
                gimli::AttributeValue::Udata(val) => {
                    if val != 0 {
                        size = Some(val);
                    }
                }
                val => {
                    high_pc = dwarf.addr(dwarf_unit, val);
                }
            },
            gimli::DW_AT_ranges => {
                ranges = dwarf.rangelist(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    function.return_type = offset;
                }
            }
            gimli::DW_AT_specification | gimli::DW_AT_abstract_origin => {
                if let Some(offset) = parse_function_offset(dwarf_unit, &attr) {
                    specification = Some(offset);
                    abstract_origin = attr.name() == gimli::DW_AT_abstract_origin;
                }
            }
            gimli::DW_AT_declaration => {
                if let gimli::AttributeValue::Flag(flag) = attr.value() {
                    function.declaration = flag;
                }
            }
            gimli::DW_AT_frame_base => {
                // FIXME / TODO
            }
            gimli::DW_AT_calling_convention => {
                // FIXME / TODO
            }
            gimli::DW_AT_external
            | gimli::DW_AT_call_all_calls
            | gimli::DW_AT_call_all_tail_calls
            | gimli::DW_AT_GNU_all_call_sites
            | gimli::DW_AT_GNU_all_tail_call_sites
            | gimli::DW_AT_prototyped
            | gimli::DW_AT_accessibility
            | gimli::DW_AT_explicit
            | gimli::DW_AT_artificial
            | gimli::DW_AT_object_pointer
            | gimli::DW_AT_virtuality
            | gimli::DW_AT_vtable_elem_location
            | gimli::DW_AT_containing_type
            | gimli::DW_AT_main_subprogram
            | gimli::DW_AT_noreturn
            | gimli::DW_AT_APPLE_optimized
            | gimli::DW_AT_APPLE_omit_frame_ptr
            | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown subprogram attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    if let Some(offset) = ranges {
        let mut ranges = dwarf.read.ranges(dwarf_unit, offset)?;
        let mut size = 0;
        while let Some(range) = ranges.next()? {
            if range.end > range.begin {
                size += range.end - range.begin;
                function.ranges.push(Range {
                    begin: range.begin,
                    end: range.end,
                });
            }
        }
        function.size = Size::new(size);
        function.address = Address::new(function.ranges.first().map(|r| r.begin).unwrap_or(0));
    } else if let Some(address) = function.address.get() {
        if let Some(high_pc) = high_pc {
            if high_pc > address {
                function.size = Size::new(high_pc - address);
                function.ranges.push(Range {
                    begin: address,
                    end: high_pc,
                });
            }
        } else if let Some(size) = size {
            function.size = Size::new(size);
            function.ranges.push(Range {
                begin: address,
                end: address.wrapping_add(size),
            });
        }
    }

    if let Some(specification) = specification {
        subprograms.push(DwarfSubprogram {
            offset,
            specification,
            abstract_origin,
            function,
        });
        return Ok(());
    }

    parse_subprogram_children(
        unit,
        dwarf,
        dwarf_unit,
        subprograms,
        variables,
        &mut function,
        node.children(),
    )?;
    unit.functions.push(function);
    Ok(())
}

fn inherit_subprogram<'input>(
    functions: &BTreeMap<FunctionOffset, Function<'input>>,
    function: &mut Function<'input>,
    specification: FunctionOffset,
    abstract_origin: bool,
) -> bool {
    let specification = match functions.get(&specification) {
        Some(val) => val,
        None => return false,
    };

    function.namespace = specification.namespace.clone();
    if function.name.is_none() {
        function.name = specification.name;
    }
    if function.linkage_name.is_none() {
        function.linkage_name = specification.linkage_name;
    }
    if function.source.is_none() {
        function.source = specification.source.clone();
    }
    if function.return_type.is_none() {
        function.return_type = specification.return_type;
    }
    if abstract_origin {
        // We inherit all children, and then extend them when parsing our children.
        function.parameters = specification.parameters.clone();
    } else {
        // TODO: inherit children from specifications?
    }

    true
}

fn parse_subprogram_children<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    function: &mut Function<'input>,
    mut iter: gimli::EntriesTreeIter<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let namespace = Some(Namespace::new(
        &function.namespace,
        function.name,
        NamespaceKind::Function,
    ));
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter => {
                parse_parameter_type(&mut function.parameters, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_variable => {
                // Handled in details.
            }
            gimli::DW_TAG_inlined_subroutine => {
                parse_inlined_subroutine(child)?;
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_subprogram => {
                parse_subprogram(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_unspecified_parameters
            | gimli::DW_TAG_template_type_parameter
            | gimli::DW_TAG_template_value_parameter
            | gimli::DW_TAG_GNU_template_parameter_pack
            | gimli::DW_TAG_label
            | gimli::DW_TAG_imported_declaration
            | gimli::DW_TAG_imported_module
            | gimli::DW_TAG_call_site
            | gimli::DW_TAG_GNU_call_site => {}
            tag => {
                if !parse_type(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )? {
                    debug!("unknown subprogram child tag: {}", tag);
                }
            }
        }
    }
    Ok(())
}

fn parse_parameter_type<'input, Endian>(
    parameters: &mut Vec<ParameterType<'input>>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut parameter = ParameterType::default();
    let offset = node.entry().offset();
    let offset = offset.to_unit_section_offset(dwarf_unit);
    parameter.offset = offset.into();
    let mut abstract_origin = None;

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_abstract_origin => {
                if let Some(offset) = parse_parameter_offset(dwarf_unit, &attr) {
                    abstract_origin = Some(offset);
                }
            }
            gimli::DW_AT_name => {
                parameter.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    parameter.ty = offset;
                }
            }
            gimli::DW_AT_location
            | gimli::DW_AT_decl_file
            | gimli::DW_AT_decl_line
            | gimli::DW_AT_decl_column
            | gimli::DW_AT_artificial
            | gimli::DW_AT_const_value
            | gimli::DW_AT_GNU_locviews
            | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown parameter attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown parameter child tag: {}", tag);
            }
        }
    }

    if let Some(abstract_origin) = abstract_origin {
        // TODO: use a hash?
        if let Some(index) = parameters.iter().position(|x| x.offset == abstract_origin) {
            let p = &mut parameters[index];
            if parameter.name.is_some() {
                p.name = parameter.name;
            }
            if parameter.ty.is_some() {
                p.ty = parameter.ty;
            }
            return Ok(());
        } else {
            let unit_offset = offset
                .to_unit_offset(dwarf_unit)
                .unwrap_or(gimli::UnitOffset(0));
            let offset = match offset {
                gimli::UnitSectionOffset::DebugInfoOffset(offset) => offset.0,
                _ => panic!("unexpected offset"),
            };
            let header_offset = match dwarf_unit.header.offset() {
                gimli::UnitSectionOffset::DebugInfoOffset(offset) => offset.0,
                _ => panic!("unexpected offset"),
            };
            debug!(
                "missing parameter abstract origin: 0x{:08x}(0x{:08x}+0x{:08x})",
                offset, header_offset, unit_offset.0
            );
        }
    }

    parameters.push(parameter);
    Ok(())
}

fn parse_parameter<'input, Endian>(
    parameters: &mut Vec<Parameter<'input>>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut parameter = Parameter::default();
    let offset = node.entry().offset();
    let offset = offset.to_unit_section_offset(dwarf_unit);
    parameter.offset = offset.into();
    let mut abstract_origin = None;

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_abstract_origin => {
                if let Some(offset) = parse_parameter_offset(dwarf_unit, &attr) {
                    abstract_origin = Some(offset);
                }
            }
            gimli::DW_AT_name => {
                parameter.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    parameter.ty = offset;
                }
            }
            gimli::DW_AT_location => {
                match attr.value() {
                    gimli::AttributeValue::Exprloc(expr) => {
                        evaluate_parameter_location(
                            dwarf,
                            dwarf_unit,
                            Range::all(),
                            expr,
                            &mut parameter,
                        );
                    }
                    val => {
                        if let Some(offset) = dwarf.loclist(dwarf_unit, val) {
                            let mut locations = dwarf.read.locations(dwarf_unit, offset)?;
                            while let Some(location) = locations.next()? {
                                // TODO: use location.range too
                                evaluate_parameter_location(
                                    dwarf,
                                    dwarf_unit,
                                    location.range.into(),
                                    location.data,
                                    &mut parameter,
                                );
                            }
                        } else {
                            debug!("unknown parameter DW_AT_location: {:?}", attr.value());
                        }
                    }
                }
            }
            gimli::DW_AT_decl_file
            | gimli::DW_AT_decl_line
            | gimli::DW_AT_decl_column
            | gimli::DW_AT_artificial
            | gimli::DW_AT_const_value
            | gimli::DW_AT_GNU_locviews
            | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown parameter attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown parameter child tag: {}", tag);
            }
        }
    }

    if let Some(abstract_origin) = abstract_origin {
        // TODO: use a hash?
        if let Some(index) = parameters.iter().position(|x| x.offset == abstract_origin) {
            let p = &mut parameters[index];
            if parameter.name.is_some() {
                p.name = parameter.name;
            }
            if parameter.ty.is_some() {
                p.ty = parameter.ty;
            }
            if !parameter.locations.is_empty() {
                p.locations.extend(&parameter.locations);
            }
            return Ok(());
        } else {
            let unit_offset = offset
                .to_unit_offset(dwarf_unit)
                .unwrap_or(gimli::UnitOffset(0));
            let offset = match offset {
                gimli::UnitSectionOffset::DebugInfoOffset(offset) => offset.0,
                _ => panic!("unexpected offset"),
            };
            let header_offset = match dwarf_unit.header.offset() {
                gimli::UnitSectionOffset::DebugInfoOffset(offset) => offset.0,
                _ => panic!("unexpected offset"),
            };
            debug!(
                "missing parameter abstract origin: 0x{:08x}(0x{:08x}+0x{:08x})",
                offset, header_offset, unit_offset.0
            );
        }
    }

    parameters.push(parameter);
    Ok(())
}

fn parse_lexical_block<'input, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_low_pc
            | gimli::DW_AT_high_pc
            | gimli::DW_AT_ranges
            | gimli::DW_AT_abstract_origin
            | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown lexical_block attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_variable => {
                // Handled in details.
            }
            gimli::DW_TAG_inlined_subroutine => {
                parse_inlined_subroutine(child)?;
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_subprogram => {
                parse_subprogram(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_formal_parameter
            | gimli::DW_TAG_label
            | gimli::DW_TAG_imported_declaration
            | gimli::DW_TAG_imported_module
            | gimli::DW_TAG_call_site
            | gimli::DW_TAG_GNU_call_site => {}
            tag => {
                if !parse_type(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    namespace,
                    child,
                )? {
                    debug!("unknown lexical_block child tag: {}", tag);
                }
            }
        }
    }
    Ok(())
}

// Only checks for unknown attributes and tags.
fn parse_inlined_subroutine<Endian>(node: gimli::EntriesTreeNode<Reader<Endian>>) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter | gimli::DW_TAG_variable => {
                // Handled in details.
            }
            gimli::DW_TAG_inlined_subroutine => {
                parse_inlined_subroutine(child)?;
            }
            gimli::DW_TAG_lexical_block => {
                parse_inlined_lexical_block(child)?;
            }
            gimli::DW_TAG_label | gimli::DW_TAG_call_site | gimli::DW_TAG_GNU_call_site => {}
            tag => {
                debug!("unknown inlined_subroutine child tag: {}", tag);
            }
        }
    }
    Ok(())
}

// Only checks for unknown attributes and tags.
fn parse_inlined_lexical_block<Endian>(node: gimli::EntriesTreeNode<Reader<Endian>>) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_low_pc
            | gimli::DW_AT_high_pc
            | gimli::DW_AT_ranges
            | gimli::DW_AT_abstract_origin
            | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown inlined lexical_block attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_inlined_subroutine => {
                parse_inlined_subroutine(child)?;
            }
            gimli::DW_TAG_lexical_block => {
                parse_inlined_lexical_block(child)?;
            }
            gimli::DW_TAG_formal_parameter
            | gimli::DW_TAG_variable
            | gimli::DW_TAG_label
            | gimli::DW_TAG_call_site
            | gimli::DW_TAG_GNU_call_site
            | gimli::DW_TAG_imported_module => {}
            tag => {
                debug!("unknown inlined lexical_block child tag: {}", tag);
            }
        }
    }
    Ok(())
}

fn parse_subprogram_details<'input, Endian>(
    hash: &FileHash<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<FunctionDetails<'input>>
where
    Endian: gimli::Endianity,
{
    let mut abstract_origin = None;

    let entry = node.entry();
    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_abstract_origin => {
                if let Some(offset) = parse_function_offset(dwarf_unit, &attr) {
                    abstract_origin = Some(offset);
                }
            }
            _ => {}
        }
    }

    // FIXME: limit recursion
    let mut details = abstract_origin
        .and_then(|offset| dwarf.get_function_details(offset, hash))
        .unwrap_or_else(|| FunctionDetails {
            parameters: Vec::new(),
            variables: Vec::new(),
            inlined_functions: Vec::new(),
            calls: Vec::new(),
        });

    parse_subprogram_children_details(hash, dwarf, dwarf_unit, &mut details, node.children())?;
    Ok(details)
}

fn parse_subprogram_children_details<'input, Endian>(
    hash: &FileHash<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    function: &mut FunctionDetails<'input>,
    mut iter: gimli::EntriesTreeIter<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter => {
                parse_parameter(&mut function.parameters, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_variable => {
                parse_local_variable(&mut function.variables, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_inlined_subroutine => {
                function
                    .inlined_functions
                    .push(parse_inlined_subroutine_details(
                        hash, dwarf, dwarf_unit, child,
                    )?);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block_details(
                    &mut function.inlined_functions,
                    &mut function.variables,
                    &mut function.calls,
                    hash,
                    dwarf,
                    dwarf_unit,
                    child,
                )?;
            }
            gimli::DW_TAG_call_site => {
                parse_call_site(&mut function.calls, hash, dwarf, dwarf_unit, child, false)?;
            }
            gimli::DW_TAG_GNU_call_site => {
                parse_call_site(&mut function.calls, hash, dwarf, dwarf_unit, child, true)?;
            }
            // Checking for unknown tags is done in `parse_subprogram_children`.
            _ => {}
        }
    }
    Ok(())
}

fn parse_lexical_block_details<'input, Endian>(
    inlined_functions: &mut Vec<InlinedFunction<'input>>,
    local_variables: &mut Vec<LocalVariable<'input>>,
    calls: &mut Vec<FunctionCall<'input>>,
    hash: &FileHash<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    // Checking for unknown attributes is done in `parse_lexical_block`.

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_variable => {
                parse_local_variable(local_variables, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_inlined_subroutine => {
                inlined_functions.push(parse_inlined_subroutine_details(
                    hash, dwarf, dwarf_unit, child,
                )?);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block_details(
                    inlined_functions,
                    local_variables,
                    calls,
                    hash,
                    dwarf,
                    dwarf_unit,
                    child,
                )?;
            }
            gimli::DW_TAG_call_site => {
                parse_call_site(calls, hash, dwarf, dwarf_unit, child, false)?;
            }
            gimli::DW_TAG_GNU_call_site => {
                parse_call_site(calls, hash, dwarf, dwarf_unit, child, true)?;
            }
            // Checking for unknown tags is done in `parse_lexical_block`.
            _ => {}
        }
    }
    Ok(())
}

fn parse_inlined_subroutine_details<'input, Endian>(
    hash: &FileHash<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<InlinedFunction<'input>>
where
    Endian: gimli::Endianity,
{
    let mut function = InlinedFunction::default();
    let mut low_pc = None;
    let mut high_pc = None;
    let mut size = None;
    let mut ranges = None;
    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_abstract_origin => {
                if let Some(offset) = parse_function_offset(dwarf_unit, &attr) {
                    function.abstract_origin = offset;
                }
            }
            gimli::DW_AT_low_pc => {
                low_pc = dwarf.addr(dwarf_unit, attr.value());
            }
            gimli::DW_AT_high_pc => match attr.value() {
                gimli::AttributeValue::Udata(val) => size = Some(val),
                val => {
                    high_pc = dwarf.addr(dwarf_unit, val);
                }
            },
            gimli::DW_AT_ranges => {
                ranges = dwarf.rangelist(dwarf_unit, attr.value());
            }
            gimli::DW_AT_call_file => {
                parse_source_file(dwarf, dwarf_unit, &attr, &mut function.call_source)
            }
            gimli::DW_AT_call_line => parse_source_line(&attr, &mut function.call_source),
            gimli::DW_AT_call_column => parse_source_column(&attr, &mut function.call_source),
            gimli::DW_AT_entry_pc | gimli::DW_AT_sibling => {}
            _ => debug!(
                "unknown inlined_subroutine attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    if function.abstract_origin.is_some() {
        if let Some(details) = dwarf.get_function_details(function.abstract_origin, hash) {
            function.parameters = details.parameters;
            function.variables = details.variables;
            if !function.inlined_functions.is_empty() {
                debug!("abstract origin with inlined functions");
            }
        } else {
            debug!("inlined_subroutine with invalid abstract origin");
        }
    } else {
        debug!("inlined_subroutine with no abstract origin");
    }

    if let Some(offset) = ranges {
        let mut size = 0;
        let mut ranges = dwarf.read.ranges(dwarf_unit, offset)?;
        while let Some(range) = ranges.next()? {
            if range.end > range.begin {
                size += range.end.wrapping_sub(range.begin);
                function.ranges.push(Range {
                    begin: range.begin,
                    end: range.end,
                });
            }
        }
        function.size = Size::new(size);
    } else if let Some(size) = size {
        if let Some(low_pc) = low_pc {
            function.ranges.push(Range {
                begin: low_pc,
                end: low_pc.wrapping_add(size),
            });
        }
        function.size = Size::new(size);
    } else if let (Some(low_pc), Some(high_pc)) = (low_pc, high_pc) {
        if high_pc > low_pc {
            function.ranges.push(Range {
                begin: low_pc,
                end: high_pc,
            });
        }
        function.size = Size::new(high_pc.wrapping_sub(low_pc));
    } else {
        debug!("unknown inlined_subroutine size");
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter => {
                parse_parameter(&mut function.parameters, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_variable => {
                parse_local_variable(&mut function.variables, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_inlined_subroutine => {
                function
                    .inlined_functions
                    .push(parse_inlined_subroutine_details(
                        hash, dwarf, dwarf_unit, child,
                    )?);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block_details(
                    &mut function.inlined_functions,
                    &mut function.variables,
                    &mut function.calls,
                    hash,
                    dwarf,
                    dwarf_unit,
                    child,
                )?;
            }
            gimli::DW_TAG_call_site => {
                parse_call_site(&mut function.calls, hash, dwarf, dwarf_unit, child, false)?;
            }
            gimli::DW_TAG_GNU_call_site => {
                parse_call_site(&mut function.calls, hash, dwarf, dwarf_unit, child, true)?;
            }
            gimli::DW_TAG_label => {}
            tag => {
                debug!("unknown inlined_subroutine child tag: {}", tag);
            }
        }
    }
    Ok(function)
}

fn parse_variable<'input, Endian>(
    _unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: Option<Arc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<DwarfVariable<'input>>
where
    Endian: gimli::Endianity,
{
    let offset = node.entry().offset();
    let mut specification = None;
    let mut variable = Variable {
        offset: offset.to_unit_section_offset(dwarf_unit).into(),
        namespace,
        ..Default::default()
    };

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                variable.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_linkage_name | gimli::DW_AT_MIPS_linkage_name => {
                variable.linkage_name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    variable.ty = offset;
                }
            }
            gimli::DW_AT_specification => {
                if let Some(offset) = parse_variable_offset(dwarf_unit, &attr) {
                    specification = Some(offset);
                }
            }
            gimli::DW_AT_declaration => {
                if let gimli::AttributeValue::Flag(flag) = attr.value() {
                    variable.declaration = flag;
                }
            }
            gimli::DW_AT_decl_file => {
                parse_source_file(dwarf, dwarf_unit, &attr, &mut variable.source)
            }
            gimli::DW_AT_decl_line => parse_source_line(&attr, &mut variable.source),
            gimli::DW_AT_decl_column => parse_source_column(&attr, &mut variable.source),
            gimli::DW_AT_location => match attr.value() {
                gimli::AttributeValue::Exprloc(expr) => {
                    if let Some((address, size)) =
                        evaluate_variable_location(dwarf, dwarf_unit, expr)
                    {
                        variable.address = address;
                        if size.is_some() {
                            variable.size = size;
                        }
                    }
                }
                gimli::AttributeValue::LocationListsRef(..) => {
                    debug!("loclist for variable: {:?}", attr.value());
                }
                _ => {
                    debug!("unknown variable DW_AT_location: {:?}", attr.value());
                }
            },
            gimli::DW_AT_abstract_origin
            | gimli::DW_AT_artificial
            | gimli::DW_AT_const_value
            | gimli::DW_AT_external
            | gimli::DW_AT_accessibility
            | gimli::DW_AT_alignment => {}
            _ => debug!(
                "unknown variable attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown variable child tag: {}", tag);
            }
        }
    }

    Ok(DwarfVariable {
        offset,
        specification,
        variable,
    })
}

fn parse_local_variable<'input, Endian>(
    variables: &mut Vec<LocalVariable<'input>>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut variable = LocalVariable::default();
    let offset = node.entry().offset();
    let offset = offset.to_unit_section_offset(dwarf_unit);
    variable.offset = offset.into();
    let mut abstract_origin = None;

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_abstract_origin => {
                if let Some(offset) = parse_variable_offset(dwarf_unit, &attr) {
                    abstract_origin = Some(offset);
                }
            }
            gimli::DW_AT_name => {
                variable.name = dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    variable.ty = offset;
                }
            }
            gimli::DW_AT_decl_file => {
                parse_source_file(dwarf, dwarf_unit, &attr, &mut variable.source)
            }
            gimli::DW_AT_decl_line => parse_source_line(&attr, &mut variable.source),
            gimli::DW_AT_decl_column => parse_source_column(&attr, &mut variable.source),
            gimli::DW_AT_location => {
                match attr.value() {
                    gimli::AttributeValue::Exprloc(expr) => {
                        evaluate_local_variable_location(
                            dwarf,
                            dwarf_unit,
                            Range::all(),
                            expr,
                            &mut variable,
                        );
                    }
                    val => {
                        if let Some(offset) = dwarf.loclist(dwarf_unit, val) {
                            let mut locations = dwarf.read.locations(dwarf_unit, offset)?;
                            while let Some(location) = locations.next()? {
                                // TODO: use location.range too
                                evaluate_local_variable_location(
                                    dwarf,
                                    dwarf_unit,
                                    location.range.into(),
                                    location.data,
                                    &mut variable,
                                );
                            }
                        } else {
                            debug!("unknown local variable DW_AT_location: {:?}", attr.value());
                        }
                    }
                }
            }
            gimli::DW_AT_alignment
            | gimli::DW_AT_artificial
            | gimli::DW_AT_const_value
            | gimli::DW_AT_external
            | gimli::DW_AT_GNU_locviews => {}
            _ => debug!(
                "unknown local variable attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            tag => {
                debug!("unknown variable child tag: {}", tag);
            }
        }
    }

    if let Some(abstract_origin) = abstract_origin {
        // TODO: use a hash?
        if let Some(index) = variables.iter().position(|x| x.offset == abstract_origin) {
            let v = &mut variables[index];
            if variable.name.is_some() {
                v.name = variable.name;
            }
            if variable.ty.is_some() {
                v.ty = variable.ty;
            }
            if variable.source.is_some() {
                v.source = variable.source;
            }
            if variable.address.is_some() {
                v.address = variable.address;
            }
            if variable.size.is_some() {
                v.size = variable.size;
            }
            if !variable.locations.is_empty() {
                v.locations.extend(&variable.locations);
            }
            return Ok(());
        } else {
            let unit_offset = offset
                .to_unit_offset(dwarf_unit)
                .unwrap_or(gimli::UnitOffset(0));
            let offset = match offset {
                gimli::UnitSectionOffset::DebugInfoOffset(offset) => offset.0,
                _ => panic!("unexpected offset"),
            };
            let header_offset = match dwarf_unit.header.offset() {
                gimli::UnitSectionOffset::DebugInfoOffset(offset) => offset.0,
                _ => panic!("unexpected offset"),
            };
            debug!(
                "missing variable abstract origin: 0x{:08x}(0x{:08x}+0x{:08x})",
                offset, header_offset, unit_offset.0
            );
        }
    }

    variables.push(variable);
    Ok(())
}

fn parse_call_site<'input, Endian>(
    calls: &mut Vec<FunctionCall<'input>>,
    hash: &FileHash<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
    is_gnu: bool,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut call = FunctionCall::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        let name = attr.name();
        match name {
            gimli::DW_AT_call_origin | gimli::DW_AT_abstract_origin => {
                if let Some(offset) =
                    parse_function_call_origin_offset(hash, dwarf, dwarf_unit, &attr)
                {
                    call.origin = Some(offset);
                }
            }
            gimli::DW_AT_GNU_tail_call | gimli::DW_AT_call_tail_call => {
                call.kind = FunctionCallKind::Tail;
            }
            gimli::DW_AT_GNU_call_site_target
            | gimli::DW_AT_GNU_call_site_target_clobbered
            | gimli::DW_AT_call_target
            | gimli::DW_AT_call_target_clobbered => {
                match attr.value() {
                    gimli::AttributeValue::Exprloc(expr) => {
                        if let Some(l) = evaluate_single_location(dwarf, dwarf_unit, expr) {
                            call.target_locations =
                                l.into_iter().map(|p| (Range::all(), p)).collect();
                        }
                    }
                    gimli::AttributeValue::LocationListsRef(..) => {
                        debug!(
                            "loclist for call_site_parameter location: {:?}",
                            attr.value()
                        );
                    }
                    _ => {
                        debug!("unknown variable DW_AT_location: {:?}", attr.value());
                    }
                }

                if matches!(
                    name,
                    gimli::DW_AT_GNU_call_site_target_clobbered
                        | gimli::DW_AT_call_target_clobbered
                ) {
                    call.target_is_clobbered = true;
                }
            }
            gimli::DW_AT_low_pc => {
                if is_gnu {
                    if let Some(addr) = dwarf.addr(dwarf_unit, attr.value()) {
                        // (the current value is the next address, so fill in the return addr with this address).
                        // The called_from address can be derived as the instruction prior to this one.
                        call.return_address = Some(addr);
                    }
                } else {
                    debug!("non-GNU call_site using DW_AT_low_pc: {:?}", attr.value());
                }
            }
            gimli::DW_AT_call_return_pc => {
                call.return_address = dwarf.addr(dwarf_unit, attr.value());
            }
            gimli::DW_AT_call_pc => {
                call.called_from_address = dwarf.addr(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    call.called_function_ty = Some(offset);
                }
            }
            gimli::DW_AT_call_file => {
                parse_source_file(dwarf, dwarf_unit, &attr, &mut call.called_from_source)
            }
            gimli::DW_AT_call_line => {
                parse_source_line(&attr, &mut call.called_from_source);
            }
            gimli::DW_AT_call_column => {
                parse_source_column(&attr, &mut call.called_from_source);
            }
            _ => debug!(
                "unknown call_site attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    // visit the call site's children (parameters)
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_GNU_call_site_parameter | gimli::DW_TAG_call_site_parameter => {
                parse_call_site_parameter(&mut call.parameter_inputs, dwarf, dwarf_unit, child)?;
            }
            tag => debug!("unknown call_site child tag: {}", tag),
        }
    }

    calls.push(call);
    Ok(())
}

fn parse_call_site_parameter<'input, Endian>(
    call_site_parameters: &mut Vec<FunctionCallParameter<'input>>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut parameter = FunctionCallParameter::default();

    let mut attrs = node.entry().attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_location => match attr.value() {
                gimli::AttributeValue::Exprloc(expr) => {
                    if let Some(l) = evaluate_single_location(dwarf, dwarf_unit, expr) {
                        parameter.locations = l.into_iter().map(|p| (Range::all(), p)).collect();
                    }
                }
                gimli::AttributeValue::LocationListsRef(..) => {
                    debug!(
                        "loclist for call_site_parameter location: {:?}",
                        attr.value()
                    );
                }
                _ => {
                    debug!("unknown variable DW_AT_location: {:?}", attr.value());
                }
            },
            gimli::DW_AT_GNU_call_site_value | gimli::DW_AT_call_value => match attr.value() {
                gimli::AttributeValue::Exprloc(expr) => {
                    if let Some(l) = evaluate_single_location(dwarf, dwarf_unit, expr) {
                        parameter.value_locations =
                            l.into_iter().map(|p| (Range::all(), p)).collect();
                    }
                }
                gimli::AttributeValue::LocationListsRef(..) => {
                    debug!("loclist for call_site_parameter value: {:?}", attr.value());
                }
                _ => {
                    debug!("unknown variable DW_AT_location: {:?}", attr.value());
                }
            },
            gimli::DW_AT_call_data_location => match attr.value() {
                gimli::AttributeValue::Exprloc(expr) => {
                    if let Some(l) = evaluate_single_location(dwarf, dwarf_unit, expr) {
                        parameter.dataref_locations =
                            l.into_iter().map(|p| (Range::all(), p)).collect();
                    }
                }
                gimli::AttributeValue::LocationListsRef(..) => {
                    debug!(
                        "loclist for call_site_parameter data location: {:?}",
                        attr.value()
                    );
                }
                _ => {
                    debug!("unknown variable DW_AT_location: {:?}", attr.value());
                }
            },
            gimli::DW_AT_call_data_value => match attr.value() {
                gimli::AttributeValue::Exprloc(expr) => {
                    if let Some(l) = evaluate_single_location(dwarf, dwarf_unit, expr) {
                        parameter.dataref_value_locations =
                            l.into_iter().map(|p| (Range::all(), p)).collect();
                    }
                }
                gimli::AttributeValue::LocationListsRef(..) => {
                    debug!(
                        "loclist for call_site_parameter data value: {:?}",
                        attr.value()
                    );
                }
                _ => {
                    debug!("unknown variable DW_AT_location: {:?}", attr.value());
                }
            },
            gimli::DW_AT_call_parameter => {
                if let Some(offset) = parse_parameter_offset(dwarf_unit, &attr) {
                    parameter.parameter.get_or_insert_default().offset = offset;
                }
            }
            gimli::DW_AT_name => {
                parameter.parameter.get_or_insert_default().name =
                    dwarf.string(dwarf_unit, attr.value());
            }
            gimli::DW_AT_type => {
                if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    parameter.parameter.get_or_insert_default().ty = offset;
                }
            }
            _ => debug!(
                "unknown call_site_parameter attribute: {} {:?}",
                attr.name(),
                attr.value()
            ),
        }
    }

    call_site_parameters.push(parameter);
    Ok(())
}

fn evaluate_member_location<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    expression: gimli::Expression<Reader<'input, Endian>>,
) -> Option<u64>
where
    Endian: gimli::Endianity,
{
    let pieces = evaluate(dwarf, dwarf_unit, expression, true);
    if pieces.len() != 1 {
        debug!("unsupported number of evaluation pieces: {:?}", pieces);
        return None;
    }
    match pieces[0].location {
        gimli::Location::Address { address } => Some(address * 8),
        gimli::Location::Register { .. } => None,
        _ => {
            debug!("unknown DW_AT_data_member_location result: {:?}", pieces);
            None
        }
    }
}

fn evaluate_variable_location<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    expression: gimli::Expression<Reader<'input, Endian>>,
) -> Option<(Address, Size)>
where
    Endian: gimli::Endianity,
{
    let pieces = evaluate(dwarf, dwarf_unit, expression, false);
    let mut result = None;
    for piece in &*pieces {
        match piece.location {
            gimli::Location::Address { address } => {
                if result.is_some() {
                    debug!(
                        "unsupported DW_AT_location with multiple addresses: {:?}",
                        pieces
                    );
                } else {
                    let address = Address::new(address);
                    let size = match piece.size_in_bits.map(|x| x.div_ceil(8)) {
                        Some(size) => Size::new(size),
                        None => Size::none(),
                    };
                    result = Some((address, size));
                }
            }
            gimli::Location::Empty
            | gimli::Location::Register { .. }
            | gimli::Location::Value { .. }
            | gimli::Location::ImplicitPointer { .. } => {}
            _ => debug!("unknown DW_AT_location piece: {:?}", piece),
        }
    }
    result
}

fn evaluate_local_variable_location<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    range: Range,
    expression: gimli::Expression<Reader<'input, Endian>>,
    variable: &mut LocalVariable<'input>,
) where
    Endian: gimli::Endianity,
{
    let pieces = match evaluate_simple(dwarf, dwarf_unit, expression, false) {
        Ok(locations) => locations,
        Err(_e) => {
            // This happens a lot, not sure if bugs or bad DWARF.
            //debug!("simple evaluation failed: {}: {:?}", _e, expression.0);
            return;
        }
    };

    for piece in &pieces {
        if piece.is_value {
            continue;
        }
        // Can this be Literal too?
        if let Location::Address { address } = piece.location {
            if variable.address.is_some() {
                if address != variable.address {
                    // TODO: combine address ranges?
                    debug!(
                        "unsupported DW_AT_location with multiple addresses: {:?}",
                        pieces
                    );
                }
            } else {
                variable.address = address;
                if let Some(bit_size) = piece.bit_size.get() {
                    variable.size = Size::new(bit_size.div_ceil(8));
                }
            }
        }
    }

    variable
        .locations
        .extend(pieces.into_iter().map(|piece| (range, piece)));
}

fn evaluate_parameter_location<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    range: Range,
    expression: gimli::Expression<Reader<'input, Endian>>,
    parameter: &mut Parameter<'input>,
) where
    Endian: gimli::Endianity,
{
    let pieces = match evaluate_simple(dwarf, dwarf_unit, expression, false) {
        Ok(locations) => locations,
        Err(_e) => {
            // This happens a lot, not sure if bugs or bad DWARF.
            //debug!("simple evaluation failed: {}: {:?}", _e, expression.0);
            return;
        }
    };

    parameter
        .locations
        .extend(pieces.into_iter().map(|piece| (range, piece)));
}

fn evaluate_single_location<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    expression: gimli::Expression<Reader<'input, Endian>>,
) -> Option<Vec<Piece>>
where
    Endian: gimli::Endianity,
{
    let pieces = match evaluate_simple(dwarf, dwarf_unit, expression, false) {
        Ok(locations) => locations,
        Err(_e) => {
            // This happens a lot, not sure if bugs or bad DWARF.
            //debug!("simple evaluation failed: {}: {:?}", _e, expression.0);
            return None;
        }
    };

    Some(pieces)
}

fn evaluate_simple<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    expression: gimli::Expression<Reader<'input, Endian>>,
    _object_address: bool,
) -> Result<Vec<Piece>>
where
    Endian: gimli::Endianity + 'input,
{
    let unit = &dwarf_unit.header;
    let encoding = unit.encoding();
    let addr_mask = if encoding.address_size == 8 {
        !0u64
    } else {
        (1 << (8 * u64::from(encoding.address_size))) - 1
    };
    let mut bytes = expression.0;

    let mut pieces = Vec::new();
    let mut next_bit_offset = 0;
    let mut add_piece = |pieces: &mut Vec<Piece>,
                         location: Location,
                         location_offset: u64,
                         is_value: bool,
                         bit_size: Size| {
        let bit_offset = next_bit_offset;
        next_bit_offset += bit_size.get().unwrap_or(0);
        pieces.push(Piece {
            bit_offset,
            bit_size,
            location,
            location_offset,
            is_value,
        });
    };

    let mut stack = Vec::new();
    let pop = |stack: &mut Vec<Location>| match stack.pop() {
        Some(value) => Ok(value),
        None => Err(gimli::Error::NotEnoughStackItems),
    };

    let mut location = None;
    while !bytes.is_empty() {
        match gimli::Operation::parse(&mut bytes, encoding)? {
            gimli::Operation::Nop => {}
            gimli::Operation::Register { register } => {
                location = Some((
                    Location::Register {
                        register: register.into(),
                    },
                    false,
                ));
            }
            gimli::Operation::ImplicitValue { .. } => {
                // Unimplemented.
                location = Some((Location::Other, true));
            }
            gimli::Operation::ImplicitPointer { .. } => {
                // Unimplemented.
                location = Some((Location::Other, false));
            }
            gimli::Operation::StackValue => {
                location = Some((pop(&mut stack)?, true));
            }
            gimli::Operation::EntryValue { .. }
            | gimli::Operation::ParameterRef { .. }
            | gimli::Operation::TypedLiteral { .. }
            | gimli::Operation::PushObjectAddress => {
                // Unimplemented.
                stack.push(Location::Other);
            }
            gimli::Operation::UnsignedConstant { value } => {
                stack.push(Location::Literal { value });
            }
            gimli::Operation::SignedConstant { value } => {
                stack.push(Location::Literal {
                    value: value as u64,
                });
            }
            gimli::Operation::RegisterOffset {
                register, offset, ..
            } => {
                // TODO: compare this against CFA, and push CfaOffset instead if it matches
                stack.push(Location::RegisterOffset {
                    register: register.into(),
                    offset,
                });
            }
            gimli::Operation::FrameOffset { offset } => {
                stack.push(Location::FrameOffset { offset });
            }
            gimli::Operation::CallFrameCFA => {
                stack.push(Location::CfaOffset { offset: 0 });
            }
            gimli::Operation::Address { address } => {
                stack.push(Location::Address {
                    address: Address::new(address),
                });
            }
            gimli::Operation::AddressIndex { index } => {
                if let Ok(address) = dwarf.read.address(dwarf_unit, index) {
                    stack.push(Location::Address {
                        address: Address::new(address),
                    });
                } else {
                    stack.push(Location::Other);
                }
            }
            gimli::Operation::ConstantIndex { .. } => {
                // Unimplemented.
                stack.push(Location::Other);
            }
            gimli::Operation::TLS => {
                let location = match pop(&mut stack)? {
                    Location::Literal { value } => Location::TlsOffset { offset: value },
                    Location::Other => Location::Other,
                    location => {
                        debug!("unsupported TLS: {:?}", location);
                        Location::Other
                    }
                };
                stack.push(location);
            }
            gimli::Operation::Piece {
                size_in_bits,
                bit_offset,
            } => {
                let location = stack.pop().unwrap_or(Location::Empty);
                add_piece(
                    &mut pieces,
                    location,
                    bit_offset.unwrap_or(0),
                    false,
                    Size::new(size_in_bits),
                );
            }
            gimli::Operation::Drop => {
                pop(&mut stack)?;
            }
            gimli::Operation::Swap => {
                let one = pop(&mut stack)?;
                let two = pop(&mut stack)?;
                stack.push(one);
                stack.push(two);
            }
            gimli::Operation::Rot => {
                let one = pop(&mut stack)?;
                let two = pop(&mut stack)?;
                let three = pop(&mut stack)?;
                stack.push(one);
                stack.push(three);
                stack.push(two);
            }
            gimli::Operation::Pick { index } => {
                let index = index as usize;
                if index >= stack.len() {
                    return Err(gimli::Error::NotEnoughStackItems.into());
                }
                let location = stack[stack.len() - index - 1];
                stack.push(location);
            }
            gimli::Operation::PlusConstant { value: constant } => {
                let location = match pop(&mut stack)? {
                    Location::Literal { value } => {
                        let value = value.wrapping_add(constant) & addr_mask;
                        Location::Literal { value }
                    }
                    Location::RegisterOffset { register, offset } => {
                        let offset = ((offset as u64).wrapping_add(constant) & addr_mask) as i64;
                        Location::RegisterOffset { register, offset }
                    }
                    Location::FrameOffset { offset } => {
                        let offset = ((offset as u64).wrapping_add(constant) & addr_mask) as i64;
                        Location::FrameOffset { offset }
                    }
                    Location::CfaOffset { offset } => {
                        let offset = ((offset as u64).wrapping_add(constant) & addr_mask) as i64;
                        Location::CfaOffset { offset }
                    }
                    Location::Other => Location::Other,
                    location => {
                        debug!("unsupported PlusConstant: {:?}", location);
                        Location::Other
                    }
                };
                stack.push(location);
            }
            gimli::Operation::Plus => {
                let one = pop(&mut stack)?;
                let two = pop(&mut stack)?;
                match (one, two) {
                    (Location::Other, _) | (_, Location::Other) => Location::Other,
                    (Location::RegisterOffset { .. }, Location::RegisterOffset { .. }) => {
                        // Seen in practice, but we can't handle this yet.
                        Location::Other
                    }
                    location => {
                        debug!("unsupported Plus: {:?}", location);
                        Location::Other
                    }
                };
            }
            gimli::Operation::Minus => {
                let one = pop(&mut stack)?;
                let two = pop(&mut stack)?;
                match (one, two) {
                    (Location::Other, _) | (_, Location::Other) => Location::Other,
                    (Location::RegisterOffset { .. }, Location::RegisterOffset { .. }) => {
                        // Seen in practice, but we can't handle this yet.
                        Location::Other
                    }
                    (Location::Literal { value }, Location::FrameOffset { offset }) => {
                        Location::FrameOffset {
                            offset: offset - value as i64,
                        }
                    }
                    location => {
                        debug!("unsupported Minus: {:?}", location);
                        Location::Other
                    }
                };
            }
            gimli::Operation::Neg
            | gimli::Operation::Not
            | gimli::Operation::Abs
            | gimli::Operation::Convert { .. }
            | gimli::Operation::Reinterpret { .. } => {
                // Unimplemented unary operations.
                pop(&mut stack)?;
                stack.push(Location::Other);
            }
            gimli::Operation::Mul
            | gimli::Operation::Div
            | gimli::Operation::Mod
            | gimli::Operation::Shl
            | gimli::Operation::Shr
            | gimli::Operation::Shra
            | gimli::Operation::And
            | gimli::Operation::Or
            | gimli::Operation::Xor
            | gimli::Operation::Eq
            | gimli::Operation::Ne
            | gimli::Operation::Gt
            | gimli::Operation::Ge
            | gimli::Operation::Lt
            | gimli::Operation::Le => {
                // Unimplemented binary operations.
                pop(&mut stack)?;
                pop(&mut stack)?;
                stack.push(Location::Other);
            }
            gimli::Operation::Deref { space, .. } => {
                // Unimplemented.
                pop(&mut stack)?;
                if space {
                    pop(&mut stack)?;
                }
                stack.push(Location::Other);
            }
            gimli::Operation::Bra { .. }
            | gimli::Operation::Skip { .. }
            | gimli::Operation::Call { .. } => {
                // Unimplemented.
                // We can't even push Location::Other for Bra.
                // Skip and Call could be implemented if needed.
                return Ok(pieces);
            }
            gimli::Operation::WasmLocal { .. }
            | gimli::Operation::WasmGlobal { .. }
            | gimli::Operation::WasmStack { .. } => {
                // Unimplemented.
                location = Some((Location::Other, false));
            }
        }
        if let Some((location, is_value)) = location {
            if bytes.is_empty() {
                if !pieces.is_empty() {
                    return Err(gimli::Error::InvalidPiece.into());
                }
                add_piece(&mut pieces, location, 0, is_value, Size::none());
            } else {
                match gimli::Operation::parse(&mut bytes, encoding)? {
                    gimli::Operation::Piece {
                        size_in_bits,
                        bit_offset,
                    } => {
                        add_piece(
                            &mut pieces,
                            location,
                            bit_offset.unwrap_or(0),
                            is_value,
                            Size::new(size_in_bits),
                        );
                    }
                    _ => {
                        return Err(gimli::Error::InvalidPiece.into());
                    }
                }
            }
        }
        location = None;
    }
    if pieces.is_empty() {
        if let Some(location) = stack.pop() {
            add_piece(&mut pieces, location, 0, false, Size::none());
        }
    }
    Ok(pieces)
}

fn evaluate<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    expression: gimli::Expression<Reader<'input, Endian>>,
    object_address: bool,
) -> Vec<gimli::Piece<Reader<'input, Endian>>>
where
    Endian: gimli::Endianity + 'input,
{
    let unit = &dwarf_unit.header;
    let mut evaluation = expression.evaluation(unit.encoding());
    if object_address {
        evaluation.set_object_address(0);
        evaluation.set_initial_value(0);
    }
    let mut result = evaluation.evaluate();
    loop {
        match result {
            Ok(gimli::EvaluationResult::Complete) => {
                return evaluation.result();
            }
            Ok(gimli::EvaluationResult::RequiresRelocatedAddress(address)) => {
                result = evaluation.resume_with_relocated_address(address);
            }
            Ok(gimli::EvaluationResult::RequiresIndexedAddress { index, relocate: _ }) => {
                if let Ok(address) = dwarf.read.address(dwarf_unit, index) {
                    result = evaluation.resume_with_indexed_address(address);
                }
            }
            Ok(_x) => {
                debug!("incomplete evaluation: {:?}", _x);
                return Vec::new();
            }
            Err(e) => {
                debug!("evaluation failed: {}", e);
                return Vec::new();
            }
        }
    }
}

impl From<gimli::Range> for Range {
    #[inline]
    fn from(range: gimli::Range) -> Range {
        Range {
            begin: range.begin,
            end: range.end,
        }
    }
}

impl From<gimli::Register> for Register {
    #[inline]
    fn from(register: gimli::Register) -> Register {
        Register(register.0)
    }
}

impl From<gimli::UnitSectionOffset> for FunctionOffset {
    #[inline]
    fn from(o: gimli::UnitSectionOffset) -> FunctionOffset {
        let o = match o {
            gimli::UnitSectionOffset::DebugInfoOffset(o) => o,
            _ => panic!("unexpected offset {:?}", o),
        };
        FunctionOffset::new(o.0)
    }
}

impl From<gimli::UnitSectionOffset> for ParameterOffset {
    #[inline]
    fn from(o: gimli::UnitSectionOffset) -> ParameterOffset {
        let o = match o {
            gimli::UnitSectionOffset::DebugInfoOffset(o) => o,
            _ => panic!("unexpected offset {:?}", o),
        };
        ParameterOffset::new(o.0)
    }
}

impl From<gimli::UnitSectionOffset> for MemberOffset {
    #[inline]
    fn from(o: gimli::UnitSectionOffset) -> MemberOffset {
        let o = match o {
            gimli::UnitSectionOffset::DebugInfoOffset(o) => o,
            _ => panic!("unexpected offset {:?}", o),
        };
        MemberOffset::new(o.0)
    }
}

impl From<gimli::UnitSectionOffset> for TypeOffset {
    #[inline]
    fn from(o: gimli::UnitSectionOffset) -> TypeOffset {
        let o = match o {
            gimli::UnitSectionOffset::DebugInfoOffset(o) => o,
            _ => panic!("unexpected offset {:?}", o),
        };
        TypeOffset::new(o.0)
    }
}

impl From<gimli::UnitSectionOffset> for VariableOffset {
    #[inline]
    fn from(o: gimli::UnitSectionOffset) -> VariableOffset {
        let o = match o {
            gimli::UnitSectionOffset::DebugInfoOffset(o) => o,
            _ => panic!("unexpected offset {:?}", o),
        };
        VariableOffset::new(o.0)
    }
}

fn parse_debug_info_offset<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<gimli::UnitSectionOffset>
where
    Endian: gimli::Endianity,
{
    match attr.value() {
        gimli::AttributeValue::UnitRef(offset) => Some(offset.to_unit_section_offset(dwarf_unit)),
        gimli::AttributeValue::DebugInfoRef(offset) => {
            Some(gimli::UnitSectionOffset::DebugInfoOffset(offset))
        }
        other => {
            debug!("unknown offset: {:?}", other);
            None
        }
    }
}

fn parse_function_offset<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<FunctionOffset>
where
    Endian: gimli::Endianity,
{
    parse_debug_info_offset(dwarf_unit, attr).map(|x| x.into())
}

fn parse_parameter_offset<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<ParameterOffset>
where
    Endian: gimli::Endianity,
{
    parse_debug_info_offset(dwarf_unit, attr).map(|x| x.into())
}

fn parse_member_offset<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<MemberOffset>
where
    Endian: gimli::Endianity,
{
    parse_debug_info_offset(dwarf_unit, attr).map(|x| x.into())
}

fn parse_type_offset<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<TypeOffset>
where
    Endian: gimli::Endianity,
{
    parse_debug_info_offset(dwarf_unit, attr).map(|x| x.into())
}

fn parse_variable_offset<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<VariableOffset>
where
    Endian: gimli::Endianity,
{
    parse_debug_info_offset(dwarf_unit, attr).map(|x| x.into())
}

fn parse_function_call_origin_offset<'input, Endian>(
    hash: &FileHash<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<FunctionCallOrigin<'input>>
where
    Endian: gimli::Endianity,
{
    if let Some(unit_section_offset) = parse_debug_info_offset(dwarf_unit, attr) {
        // now parse the DIE at this offset to discover its type
        let entry = match unit_section_offset {
            gimli::UnitSectionOffset::DebugInfoOffset(offset) => {
                if let Some((target_dwarf_unit, _)) = dwarf.tree(offset) {
                    let unit_offset = if let Some(unit_offset) =
                        unit_section_offset.to_unit_offset(target_dwarf_unit)
                    {
                        unit_offset
                    } else {
                        panic!(
                            "failed to convert unit_section offset {:?} to unit offset",
                            unit_section_offset
                        );
                    };
                    let entry = if let Ok(entry) = target_dwarf_unit.entry(unit_offset) {
                        entry
                    } else {
                        panic!("failed to find DIE entry at offset: {:?}", unit_offset);
                    };

                    Some(entry)
                } else {
                    None
                }
            }
            _ => {
                debug!(
                    "while parsing call_site origin, found unknown DIE offset: {:?}",
                    unit_section_offset
                );
                None
            }
        };

        if let Some(entry) = entry {
            match entry.tag() {
                gimli::DW_TAG_subprogram => {
                    let offset: FunctionOffset = unit_section_offset.into();
                    Function::from_offset(hash, offset).map(FunctionCallOrigin::Direct)
                }
                gimli::DW_TAG_variable => {
                    // check if this is a global variable
                    let offset: VariableOffset = unit_section_offset.into();
                    if let Some(v) = Variable::from_offset(hash, offset) {
                        Some(FunctionCallOrigin::Indirect(
                            FunctionCallIndirectOrigin::Variable(v),
                        ))
                    } else {
                        // Have the caller check the local variables (they can use a function hash if they are interested)
                        Some(FunctionCallOrigin::Indirect(
                            FunctionCallIndirectOrigin::LocalVariable(offset),
                        ))
                    }
                }
                gimli::DW_TAG_formal_parameter => {
                    // Have the caller check their parameters (they can use a function hash if they are interested)
                    Some(FunctionCallOrigin::Indirect(
                        FunctionCallIndirectOrigin::Parameter(unit_section_offset.into()),
                    ))
                }
                gimli::DW_TAG_member => {
                    // this can be viewed as a vtable or a class method
                    Some(FunctionCallOrigin::Indirect(
                        FunctionCallIndirectOrigin::Member(unit_section_offset.into()),
                    ))
                }
                tag => {
                    debug!("uknown tag for call site origin at offset: {}", tag);
                    None
                }
            }
        } else {
            None
        }
    } else {
        None
    }
}

fn parse_source_file<'input, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
    source: &mut Source<'input>,
) where
    Endian: gimli::Endianity,
{
    match attr.value() {
        gimli::AttributeValue::FileIndex(val) => {
            if val != 0 {
                if let Some(line) = &dwarf_unit.line_program {
                    if let Some(entry) = line.header().file(val) {
                        source.file = dwarf.string(dwarf_unit, entry.path_name());
                        if let Some(directory) = entry.directory(line.header()) {
                            source.directory = dwarf.string(dwarf_unit, directory);
                        } else {
                            debug!("invalid directory index {}", entry.directory_index());
                        }
                    } else {
                        debug!("invalid file index {}", val);
                    }
                }
            }
        }
        val => {
            debug!("unknown DW_AT_decl_file attribute value: {:?}", val);
        }
    }
}

fn parse_source_line<Endian>(attr: &gimli::Attribute<Reader<Endian>>, source: &mut Source)
where
    Endian: gimli::Endianity,
{
    match attr.value() {
        gimli::AttributeValue::Udata(val) => {
            if val != 0 {
                if val <= u64::from(u32::MAX) {
                    source.line = val as u32;
                } else {
                    debug!("large source line: {}", val);
                }
            }
        }
        val => {
            debug!("unknown DW_AT_decl_line attribute value: {:?}", val);
        }
    }
}

fn parse_source_column<Endian>(attr: &gimli::Attribute<Reader<Endian>>, source: &mut Source)
where
    Endian: gimli::Endianity,
{
    match attr.value() {
        gimli::AttributeValue::Udata(val) => {
            if val != 0 {
                if val <= u64::from(u32::MAX) {
                    source.column = val as u32;
                } else {
                    debug!("large source column: {}", val);
                }
            }
        }
        val => {
            debug!("unknown DW_AT_decl_column attribute value: {:?}", val);
        }
    }
}

struct DwarfFrame<R: gimli::Reader<Offset = usize>> {
    debug_frame: DebugFrameTable<R>,
    eh_frame: EhFrameTable<R>,
}

impl<R: gimli::Reader<Offset = usize>> DwarfFrame<R> {
    fn new(
        debug_frame: gimli::DebugFrame<R>,
        eh_frame: gimli::EhFrame<R>,
        bases: gimli::BaseAddresses,
    ) -> Self {
        DwarfFrame {
            debug_frame: DebugFrameTable::new(debug_frame),
            eh_frame: EhFrameTable::new(eh_frame, bases),
        }
    }

    fn get_cfi(&self, range: Range) -> Option<Vec<Cfi>> {
        let cfi = self
            .eh_frame
            .get_cfi(range)
            .or_else(|| self.debug_frame.get_cfi(range));
        if cfi.is_none() {
            debug!("no FDE for 0x{:x}[0x{:x}]", range.begin, range.size());
        }
        cfi
    }
}

struct DebugFrameTable<R: gimli::Reader<Offset = usize>> {
    debug_frame: gimli::DebugFrame<R>,
    bases: gimli::BaseAddresses,
    fdes: FdeOffsetTable,
}

impl<R: gimli::Reader<Offset = usize>> DebugFrameTable<R> {
    fn new(debug_frame: gimli::DebugFrame<R>) -> Self {
        let bases = gimli::BaseAddresses::default();
        let fdes = FdeOffsetTable::new(&debug_frame, &bases);
        DebugFrameTable {
            debug_frame,
            bases,
            fdes,
        }
    }

    fn get_cfi(&self, range: Range) -> Option<Vec<Cfi>> {
        get_cfi(&self.debug_frame, &self.bases, &self.fdes, range)
    }
}

struct EhFrameTable<R: gimli::Reader<Offset = usize>> {
    eh_frame: gimli::EhFrame<R>,
    bases: gimli::BaseAddresses,
    fdes: FdeOffsetTable,
}

impl<R: gimli::Reader<Offset = usize>> EhFrameTable<R> {
    fn new(eh_frame: gimli::EhFrame<R>, bases: gimli::BaseAddresses) -> Self {
        let fdes = FdeOffsetTable::new(&eh_frame, &bases);
        EhFrameTable {
            eh_frame,
            bases,
            fdes,
        }
    }

    fn get_cfi(&self, range: Range) -> Option<Vec<Cfi>> {
        get_cfi(&self.eh_frame, &self.bases, &self.fdes, range)
    }
}

struct FdeOffsetTable {
    offsets: Vec<(Range, usize)>,
}

impl FdeOffsetTable {
    fn new<R: gimli::Reader<Offset = usize>, S: gimli::UnwindSection<R>>(
        section: &S,
        bases: &gimli::BaseAddresses,
    ) -> Self
    where
        S::Offset: gimli::UnwindOffset,
    {
        let mut offsets = Vec::new();
        let mut entries = section.entries(bases);
        while let Ok(Some(entry)) = entries.next() {
            match entry {
                gimli::CieOrFde::Cie(_) => {}
                gimli::CieOrFde::Fde(partial) => {
                    if let Ok(fde) = partial.parse(S::cie_from_offset) {
                        let range = Range {
                            begin: fde.initial_address(),
                            end: fde.initial_address() + fde.len(),
                        };
                        offsets.push((range, fde.offset()));
                    }
                }
            }
        }
        offsets.sort_by_key(|x| x.0);
        FdeOffsetTable { offsets }
    }

    fn find(&self, address: u64) -> Option<usize> {
        // FIXME: doesn't handle overlapping
        let index = match self.offsets.binary_search_by_key(&address, |x| x.0.begin) {
            Ok(x) => Some(x),
            Err(x) => {
                if x > 0 {
                    Some(x - 1)
                } else {
                    None
                }
            }
        };
        if let Some(index) = index {
            let (range, offset) = self.offsets[index];
            if range.begin <= address && range.end > address {
                return Some(offset);
            }
        }
        None
    }
}

fn get_cfi<R: gimli::Reader, S: gimli::UnwindSection<R>>(
    section: &S,
    bases: &gimli::BaseAddresses,
    fdes: &FdeOffsetTable,
    range: Range,
) -> Option<Vec<Cfi>>
where
    S::Offset: gimli::UnwindOffset,
{
    let address = range.begin;
    let size = range.size();
    let fde_offset = S::Offset::from(fdes.find(address)?);
    let fde = section
        .fde_from_offset(bases, fde_offset, S::cie_from_offset)
        .ok()?;

    if (address, size) != (fde.initial_address(), fde.len()) {
        debug!(
            "FDE address mismatch: want function 0x{:x}[0x{:x}], found FDE 0x{:x}[0x{:x}]",
            address,
            size,
            fde.initial_address(),
            fde.len(),
        );
    }

    let mut cfi = Vec::new();
    cfi.push((Address::none(), CfiDirective::StartProc));
    if let Some(personality) = fde.personality() {
        // TODO: better handling of indirect
        let address = match personality {
            gimli::Pointer::Direct(x) => Address::new(x),
            gimli::Pointer::Indirect(x) => Address::new(x),
        };
        cfi.push((Address::none(), CfiDirective::Personality(address)));
    }
    if let Some(lsda) = fde.lsda() {
        // TODO: better handling of indirect
        let address = match lsda {
            gimli::Pointer::Direct(x) => Address::new(x),
            gimli::Pointer::Indirect(x) => Address::new(x),
        };
        cfi.push((Address::none(), CfiDirective::Lsda(address)));
    }
    if fde.is_signal_trampoline() {
        cfi.push((Address::none(), CfiDirective::SignalFrame));
    }

    let cie = fde.cie();
    let mut address = 0;
    let mut instructions = cie.instructions(section, bases);
    while let Ok(Some(instruction)) = instructions.next() {
        if let Some(directive) = convert_cfi(cie, instruction, &mut address) {
            cfi.push((Address::none(), directive))
        }
    }

    let mut address = fde.initial_address();
    let mut instructions = fde.instructions(section, bases);
    while let Ok(Some(instruction)) = instructions.next() {
        if let Some(directive) = convert_cfi(cie, instruction, &mut address) {
            cfi.push((Address::new(address), directive))
        }
    }

    cfi.push((
        Address::new(fde.initial_address() + fde.len()),
        CfiDirective::EndProc,
    ));
    Some(cfi)
}

fn convert_cfi<R: gimli::Reader>(
    cie: &gimli::CommonInformationEntry<R>,
    instruction: gimli::CallFrameInstruction<R::Offset>,
    loc: &mut u64,
) -> Option<CfiDirective> {
    match instruction {
        gimli::CallFrameInstruction::SetLoc { address } => {
            *loc = address;
            None
        }
        gimli::CallFrameInstruction::AdvanceLoc { delta } => {
            *loc += delta as u64 * cie.code_alignment_factor();
            None
        }
        gimli::CallFrameInstruction::DefCfa { register, offset } => {
            Some(CfiDirective::DefCfa(register.into(), offset as i64))
        }
        gimli::CallFrameInstruction::DefCfaSf {
            register,
            factored_offset,
        } => {
            let offset = factored_offset * cie.data_alignment_factor();
            Some(CfiDirective::DefCfa(register.into(), offset))
        }
        gimli::CallFrameInstruction::DefCfaRegister { register } => {
            Some(CfiDirective::DefCfaRegister(register.into()))
        }
        gimli::CallFrameInstruction::DefCfaOffset { offset } => {
            Some(CfiDirective::DefCfaOffset(offset as i64))
        }
        gimli::CallFrameInstruction::DefCfaOffsetSf { factored_offset } => {
            let offset = factored_offset * cie.data_alignment_factor();
            Some(CfiDirective::DefCfaOffset(offset))
        }
        gimli::CallFrameInstruction::Offset {
            register,
            factored_offset,
        } => {
            let offset = factored_offset as i64 * cie.data_alignment_factor();
            Some(CfiDirective::Offset(register.into(), offset))
        }
        gimli::CallFrameInstruction::OffsetExtendedSf {
            register,
            factored_offset,
        } => {
            let offset = factored_offset * cie.data_alignment_factor();
            Some(CfiDirective::Offset(register.into(), offset))
        }
        gimli::CallFrameInstruction::ValOffset {
            register,
            factored_offset,
        } => {
            let offset = factored_offset as i64 * cie.data_alignment_factor();
            Some(CfiDirective::ValOffset(register.into(), offset))
        }
        gimli::CallFrameInstruction::ValOffsetSf {
            register,
            factored_offset,
        } => {
            let offset = factored_offset * cie.data_alignment_factor();
            Some(CfiDirective::ValOffset(register.into(), offset))
        }
        gimli::CallFrameInstruction::Register {
            dest_register,
            src_register,
        } => Some(CfiDirective::Register(
            dest_register.into(),
            src_register.into(),
        )),
        gimli::CallFrameInstruction::Undefined { register } => {
            Some(CfiDirective::Undefined(register.into()))
        }
        gimli::CallFrameInstruction::SameValue { register } => {
            Some(CfiDirective::SameValue(register.into()))
        }
        gimli::CallFrameInstruction::Restore { register } => {
            Some(CfiDirective::Restore(register.into()))
        }
        gimli::CallFrameInstruction::RememberState => Some(CfiDirective::RememberState),
        gimli::CallFrameInstruction::RestoreState => Some(CfiDirective::RestoreState),
        gimli::CallFrameInstruction::Nop => None,
        _ => {
            debug!("Unhandled CFI: {:?}", instruction);
            Some(CfiDirective::Other)
        }
    }
}
