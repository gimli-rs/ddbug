use std::borrow::Cow;
use std::cell::Cell;
use std::collections::BTreeMap;
use std::mem;
use std::rc::Rc;

use gimli;
use object;

use Result;
use file::DebugInfo;
use function::{Function, FunctionOffset, InlinedFunction, Parameter, ParameterOffset};
use namespace::{Namespace, NamespaceKind};
use range::Range;
use source::Source;
use types::{ArrayType, BaseType, EnumerationType, Enumerator, FunctionType, Member,
            PointerToMemberType, StructType, Type, TypeDef, TypeKind, TypeModifier,
            TypeModifierKind, TypeOffset, UnionType, UnspecifiedType};
use unit::Unit;
use variable::{LocalVariable, Variable, VariableOffset};

type Reader<'input, Endian> = gimli::EndianSlice<'input, Endian>;

struct DwarfDebugInfo<'input, Endian>
where
    Endian: gimli::Endianity,
{
    endian: Endian,
    debug_abbrev: gimli::DebugAbbrev<Reader<'input, Endian>>,
    debug_info: gimli::DebugInfo<Reader<'input, Endian>>,
    debug_line: gimli::DebugLine<Reader<'input, Endian>>,
    debug_str: gimli::DebugStr<Reader<'input, Endian>>,
    range_lists: gimli::RangeLists<Reader<'input, Endian>>,
    units: Vec<DwarfUnit<'input, Endian>>,
}

impl<'input, Endian> DebugInfo for DwarfDebugInfo<'input, Endian>
where
    Endian: gimli::Endianity,
{
    fn type_from_offset(&self, offset: TypeOffset) -> Option<Type> {
        let offset = match offset.get() {
            None => return None,
            Some(offset) => gimli::DebugInfoOffset(offset),
        };
        // FIXME: make this more efficient for large numbers of units
        // FIXME: cache lookups
        for unit in &self.units {
            if let Some(offset) = offset.to_unit_offset(&unit.header) {
                let mut tree = unit.header.entries_tree(&unit.abbrev, Some(offset)).ok()?;
                let node = tree.root().ok()?;
                return parse_unnamed_type(self, unit, node).ok()?;
            }
        }
        None
    }
}

struct DwarfUnit<'input, Endian>
where
    Endian: gimli::Endianity,
{
    header: gimli::CompilationUnitHeader<Reader<'input, Endian>>,
    abbrev: gimli::Abbreviations,
    line: Option<
        gimli::StateMachine<
            Reader<'input, Endian>,
            gimli::IncompleteLineNumberProgram<Reader<'input, Endian>>,
        >,
    >,
}

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

pub(crate) fn parse<'input, 'file, Endian, Object, Cb>(
    endian: Endian,
    object: &Object,
    cb: Cb,
) -> Result<()>
where
    Endian: gimli::Endianity,
    Object: object::Object<'input, 'file>,
    Cb: FnOnce(Vec<Unit>, &DebugInfo) -> Result<()>,
{
    let get_section = |name| {
        object
            .section_data_by_name(name)
            .unwrap_or(Cow::Borrowed(&[]))
    };
    let debug_abbrev = get_section(".debug_abbrev");
    let debug_abbrev = gimli::DebugAbbrev::new(&debug_abbrev, endian);
    let debug_info = get_section(".debug_info");
    let debug_info = gimli::DebugInfo::new(&debug_info, endian);
    let debug_line = get_section(".debug_line");
    let debug_line = gimli::DebugLine::new(&debug_line, endian);
    let debug_str = get_section(".debug_str");
    let debug_str = gimli::DebugStr::new(&debug_str, endian);
    let debug_ranges = get_section(".debug_ranges");
    let debug_ranges = gimli::DebugRanges::new(&debug_ranges, endian);
    let debug_rnglists = get_section(".debug_rnglists");
    let debug_rnglists = gimli::DebugRngLists::new(&debug_rnglists, endian);
    let range_lists = gimli::RangeLists::new(debug_ranges, debug_rnglists)?;

    let mut dwarf = DwarfDebugInfo {
        endian,
        debug_abbrev,
        debug_info,
        debug_line,
        debug_str,
        range_lists,
        units: Vec::new(),
    };

    let mut units = Vec::new();
    let mut unit_headers = dwarf.debug_info.units();
    while let Some(unit_header) = unit_headers.next()? {
        units.push(parse_unit(&mut dwarf, unit_header)?);
    }
    cb(units, &dwarf)
}

fn parse_unit<'input, Endian>(
    dwarf: &mut DwarfDebugInfo<'input, Endian>,
    unit_header: gimli::CompilationUnitHeader<Reader<'input, Endian>>,
) -> Result<Unit<'input>>
where
    Endian: gimli::Endianity,
{
    let abbrev = unit_header.abbreviations(&dwarf.debug_abbrev)?;
    let mut dwarf_unit = DwarfUnit {
        header: unit_header,
        abbrev,
        line: None,
    };

    let mut unit = Unit::default();
    unit.address_size = Some(u64::from(unit_header.address_size()));

    let mut subprograms = Vec::new();
    let mut variables = Vec::new();

    {
        let mut tree = unit_header.entries_tree(&dwarf_unit.abbrev, None)?;
        let root = tree.root()?;

        let mut comp_name = None;
        let mut comp_dir = None;
        {
            let entry = root.entry();
            if entry.tag() != gimli::DW_TAG_compile_unit {
                return Err(format!("unknown CU tag: {}", entry.tag()).into());
            }
            let mut attrs = entry.attrs();
            let mut stmt_list = None;
            let mut ranges = None;
            let mut high_pc = None;
            let mut size = None;
            while let Some(attr) = attrs.next()? {
                match attr.name() {
                    gimli::DW_AT_name => {
                        comp_name = attr.string_value(&dwarf.debug_str);
                        unit.name = comp_name.map(|s| s.to_string_lossy());
                    }
                    gimli::DW_AT_comp_dir => {
                        comp_dir = attr.string_value(&dwarf.debug_str);
                        unit.dir = comp_dir.map(|s| s.to_string_lossy());
                    }
                    gimli::DW_AT_language => {
                        if let gimli::AttributeValue::Language(language) = attr.value() {
                            unit.language = Some(language);
                        }
                    }
                    gimli::DW_AT_low_pc => {
                        if let gimli::AttributeValue::Addr(addr) = attr.value() {
                            // TODO: is address 0 ever valid?
                            if addr != 0 {
                                unit.low_pc = Some(addr);
                            }
                        }
                    }
                    gimli::DW_AT_high_pc => match attr.value() {
                        gimli::AttributeValue::Addr(val) => high_pc = Some(val),
                        gimli::AttributeValue::Udata(val) => size = Some(val),
                        val => debug!("unknown CU DW_AT_high_pc: {:?}", val),
                    },
                    gimli::DW_AT_stmt_list => {
                        if let gimli::AttributeValue::DebugLineRef(val) = attr.value() {
                            stmt_list = Some(val);
                        }
                    }
                    gimli::DW_AT_ranges => {
                        if let gimli::AttributeValue::RangeListsRef(val) = attr.value() {
                            ranges = Some(val);
                        }
                    }
                    gimli::DW_AT_producer
                    | gimli::DW_AT_entry_pc
                    | gimli::DW_AT_APPLE_optimized
                    | gimli::DW_AT_macro_info
                    | gimli::DW_AT_GNU_macros
                    | gimli::DW_AT_sibling => {}
                    _ => debug!("unknown CU attribute: {} {:?}", attr.name(), attr.value()),
                }
            }

            // Find ranges from attributes in order of preference:
            // DW_AT_stmt_list, DW_AT_ranges, DW_AT_high_pc, DW_AT_size.
            // TODO: include variables in ranges.
            if let Some(offset) = stmt_list {
                let mut rows = dwarf
                    .debug_line
                    .program(
                        offset,
                        dwarf_unit.header.address_size(),
                        comp_name,
                        comp_dir,
                    )?
                    .rows();
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
                dwarf_unit.line = Some(rows);
            } else if let Some(offset) = ranges {
                let low_pc = unit.low_pc.unwrap_or(0);
                let mut ranges = dwarf.range_lists.ranges(
                    offset,
                    dwarf_unit.header.version(),
                    dwarf_unit.header.address_size(),
                    low_pc,
                )?;
                while let Some(range) = ranges.next()? {
                    // Ranges starting at 0 are probably invalid.
                    // TODO: is this always desired?
                    if range.begin != 0 {
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
        };

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
    }

    fixup_subprogram_specifications(
        &mut unit,
        dwarf,
        &dwarf_unit,
        &mut subprograms,
        &mut variables,
    )?;
    fixup_variable_specifications(&mut unit, dwarf, &dwarf_unit, &mut variables)?;

    dwarf.units.push(dwarf_unit);
    Ok(unit)
}

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
                let mut tree = dwarf_unit
                    .header
                    .entries_tree(&dwarf_unit.abbrev, Some(subprogram.offset))?;
                parse_subprogram_children(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &mut subprogram.function,
                    tree.root()?.children(),
                )?;
                let offset = subprogram.offset.to_debug_info_offset(&dwarf_unit.header);
                functions.insert(offset.into(), subprogram.function);
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
                let mut tree = dwarf_unit
                    .header
                    .entries_tree(&dwarf_unit.abbrev, Some(subprogram.offset))?;
                parse_subprogram_children(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &mut subprogram.function,
                    tree.root()?.children(),
                )?;
                let offset = subprogram.offset.to_debug_info_offset(&dwarf_unit.header);
                functions.insert(offset.into(), subprogram.function);
            }
            break;
        }
    }

    unit.functions = functions.into_iter().map(|(_, x)| x).collect();
    Ok(())
}

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
                        variable.name = specification.name.clone();
                    }
                    if variable.linkage_name.is_none() {
                        variable.linkage_name = specification.linkage_name.clone();
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
            let offset = variable.offset.to_debug_info_offset(&dwarf_unit.header);
            variable_map.insert(offset.into(), variable.variable);
            progress = true;
        }

        if defer.is_empty() {
            break;
        }
        if !progress {
            debug!("invalid specification for {} variables", defer.len());
            for variable in variables.drain(..) {
                let offset = variable.offset.to_debug_info_offset(&dwarf_unit.header);
                variable_map.insert(offset.into(), variable.variable);
            }
            break;
        }
        *variables = defer;
    }

    unit.variables = variable_map.into_iter().map(|(_, x)| x).collect();
    Ok(())
}

fn parse_namespace_children<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    mut iter: gimli::EntriesTreeIter<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
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
            gimli::DW_TAG_imported_declaration | gimli::DW_TAG_imported_module => {}
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

fn parse_namespace<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut name = None;

    {
        let entry = node.entry();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_decl_file | gimli::DW_AT_decl_line | gimli::DW_AT_decl_column => {}
                _ => debug!(
                    "unknown namespace attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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

fn parse_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<bool>
where
    Endian: gimli::Endianity,
{
    let tag = node.entry().tag();
    let offset = node.entry().offset();
    let kind = match tag {
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
    let mut ty = Type::default();
    let offset = offset.to_debug_info_offset(&dwarf_unit.header);
    ty.offset = offset.into();
    ty.kind = kind;
    unit.types.push(ty);
    Ok(true)
}

fn parse_unnamed_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<Option<Type<'input>>>
where
    Endian: gimli::Endianity,
{
    let tag = node.entry().tag();
    let mut ty = Type::default();
    let offset = node.entry().offset();
    let offset = offset.to_debug_info_offset(&dwarf_unit.header);
    ty.offset = offset.into();
    ty.kind = match tag {
        gimli::DW_TAG_base_type => TypeKind::Base(parse_base_type(dwarf, dwarf_unit, node)?),
        gimli::DW_TAG_array_type => TypeKind::Array(parse_array_type(dwarf, dwarf_unit, node)?),
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

fn parse_type_modifier<'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
    kind: TypeModifierKind,
) -> Result<TypeModifier<'input>>
where
    Endian: gimli::Endianity,
{
    let mut modifier = TypeModifier {
        kind,
        ty: TypeOffset::none(),
        name: None,
        byte_size: None,
        address_size: Some(u64::from(dwarf_unit.header.address_size())),
    };

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    modifier.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    modifier.ty = offset;
                },
                gimli::DW_AT_byte_size => {
                    modifier.byte_size = attr.udata_value();
                }
                _ => debug!(
                    "unknown type modifier attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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

fn parse_base_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    _unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<BaseType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = BaseType::default();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_encoding => {}
                _ => debug!(
                    "unknown base type attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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

fn parse_typedef<'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<TypeDef<'input>>
where
    Endian: gimli::Endianity,
{
    let mut typedef = TypeDef::default();
    typedef.namespace = namespace.clone();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    typedef.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    typedef.ty = offset;
                },
                gimli::DW_AT_decl_file => parse_source_file(dwarf_unit, &attr, &mut typedef.source),
                gimli::DW_AT_decl_line => parse_source_line(&attr, &mut typedef.source),
                gimli::DW_AT_decl_column => parse_source_column(&attr, &mut typedef.source),
                _ => debug!(
                    "unknown typedef attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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

fn parse_structure_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<StructType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = StructType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => if let gimli::AttributeValue::Flag(flag) = attr.value()
                {
                    ty.declaration = flag;
                },
                gimli::DW_AT_decl_file => parse_source_file(dwarf_unit, &attr, &mut ty.source),
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
    }

    let namespace = Some(Namespace::new(
        &ty.namespace,
        ty.name.clone(),
        NamespaceKind::Type,
    ));
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
            gimli::DW_TAG_inheritance
            | gimli::DW_TAG_template_type_parameter
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
    ty.members.sort_by_key(|v| v.bit_offset);
    let mut bit_offset = ty.byte_size.map(|v| v * 8);
    for member in ty.members.iter_mut().rev() {
        member.next_bit_offset = bit_offset;
        bit_offset = Some(member.bit_offset);
    }
    Ok(ty)
}

fn parse_union_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<UnionType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = UnionType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => if let gimli::AttributeValue::Flag(flag) = attr.value()
                {
                    ty.declaration = flag;
                },
                gimli::DW_AT_decl_file => parse_source_file(dwarf_unit, &attr, &mut ty.source),
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
    }

    let namespace = Some(Namespace::new(
        &ty.namespace,
        ty.name.clone(),
        NamespaceKind::Type,
    ));
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

fn parse_member<'input, 'abbrev, 'unit, 'tree, Endian>(
    members: &mut Vec<Member<'input>>,
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut member = Member::default();
    let mut bit_offset = None;
    let mut byte_size = None;
    let mut declaration = false;

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    member.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    member.ty = offset;
                },
                gimli::DW_AT_data_member_location => {
                    match attr.value() {
                        gimli::AttributeValue::Udata(v) => member.bit_offset = v * 8,
                        gimli::AttributeValue::Sdata(v) => if v >= 0 {
                            member.bit_offset = (v as u64) * 8;
                        } else {
                            debug!("DW_AT_data_member_location is negative: {}", v)
                        },
                        gimli::AttributeValue::Exprloc(expr) => if let Some(offset) =
                            evaluate_member_location(&dwarf_unit.header, expr)
                        {
                            member.bit_offset = offset;
                        },
                        gimli::AttributeValue::LocationListsRef(..) => {
                            // TODO
                        }
                        _ => {
                            debug!("unknown DW_AT_data_member_location: {:?}", attr.value());
                        }
                    }
                }
                gimli::DW_AT_data_bit_offset => if let Some(bit_offset) = attr.udata_value() {
                    member.bit_offset = bit_offset;
                },
                gimli::DW_AT_bit_offset => {
                    bit_offset = attr.udata_value();
                }
                gimli::DW_AT_byte_size => {
                    byte_size = attr.udata_value();
                }
                gimli::DW_AT_bit_size => {
                    member.bit_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => {
                    declaration = true;
                }
                gimli::DW_AT_decl_file
                | gimli::DW_AT_decl_line
                | gimli::DW_AT_decl_column
                | gimli::DW_AT_external
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

    if let (Some(bit_offset), Some(bit_size)) = (bit_offset, member.bit_size) {
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

fn parse_enumeration_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<EnumerationType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = EnumerationType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                gimli::DW_AT_declaration => if let gimli::AttributeValue::Flag(flag) = attr.value()
                {
                    ty.declaration = flag;
                },
                gimli::DW_AT_decl_file => parse_source_file(dwarf_unit, &attr, &mut ty.source),
                gimli::DW_AT_decl_line => parse_source_line(&attr, &mut ty.source),
                gimli::DW_AT_decl_column => parse_source_column(&attr, &mut ty.source),
                gimli::DW_AT_sibling
                | gimli::DW_AT_type
                | gimli::DW_AT_alignment
                | gimli::DW_AT_enum_class => {}
                _ => debug!(
                    "unknown enumeration attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
        }
    }

    let namespace = Some(Namespace::new(
        &ty.namespace,
        ty.name.clone(),
        NamespaceKind::Type,
    ));
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_enumerator => {
                ty.enumerators
                    .push(parse_enumerator(dwarf, dwarf_unit, &namespace, child)?);
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
            tag => {
                debug!("unknown enumeration child tag: {}", tag);
            }
        }
    }
    Ok(ty)
}

fn parse_enumerator<'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    _dwarf_unit: &DwarfUnit<'input, Endian>,
    _namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<Enumerator<'input>>
where
    Endian: gimli::Endianity,
{
    let mut enumerator = Enumerator::default();

    {
        let mut attrs = node.entry().attrs();
        while let Some(ref attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    enumerator.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_const_value => if let Some(value) = attr.sdata_value() {
                    enumerator.value = Some(value);
                } else {
                    debug!("unknown enumerator const_value: {:?}", attr.value());
                },
                _ => debug!(
                    "unknown enumerator attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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

fn parse_array_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    _dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<ArrayType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut array = ArrayType::default();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    array.ty = offset;
                },
                gimli::DW_AT_byte_size => {
                    array.byte_size = attr.udata_value();
                }
                gimli::DW_AT_name | gimli::DW_AT_GNU_vector | gimli::DW_AT_sibling => {}
                _ => debug!(
                    "unknown array attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_subrange_type => {
                let mut attrs = child.entry().attrs();
                while let Some(attr) = attrs.next()? {
                    match attr.name() {
                        gimli::DW_AT_count => {
                            array.count = attr.udata_value();
                        }
                        gimli::DW_AT_upper_bound => {
                            // byte_size takes precedence over upper_bound when
                            // determining the count.
                            if array.byte_size.is_none() {
                                if let Some(upper_bound) = attr.udata_value() {
                                    // TODO: use AT_lower_bound too (and default lower bound)
                                    if let Some(count) = u64::checked_add(upper_bound, 1) {
                                        array.count = Some(count);
                                    } else {
                                        debug!("overflow for array upper bound: {}", upper_bound);
                                    }
                                }
                            }
                        }
                        gimli::DW_AT_type | gimli::DW_AT_lower_bound => {}
                        _ => debug!(
                            "unknown array subrange attribute: {} {:?}",
                            attr.name(),
                            attr.value()
                        ),
                    }
                }
            }
            tag => {
                debug!("unknown array child tag: {}", tag);
            }
        }
    }
    Ok(array)
}

fn parse_subroutine_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<FunctionType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut function = FunctionType {
        // Go treats subroutine types as pointers.
        // Not sure if this is valid for all languages.
        byte_size: Some(u64::from(dwarf_unit.header.address_size())),
        ..Default::default()
    };

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    function.return_type = offset;
                },
                gimli::DW_AT_name | gimli::DW_AT_prototyped | gimli::DW_AT_sibling => {}
                _ => debug!(
                    "unknown subroutine attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter => {
                parse_parameter(&mut function.parameters, dwarf, dwarf_unit, child)?;
            }
            tag => {
                debug!("unknown subroutine child tag: {}", tag);
            }
        }
    }
    Ok(function)
}

fn parse_unspecified_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfDebugInfo<'input, Endian>,
    _dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<UnspecifiedType<'input>>
where
    Endian: gimli::Endianity,
{
    let mut ty = UnspecifiedType::default();
    ty.namespace = namespace.clone();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    ty.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                _ => debug!(
                    "unknown unspecified type attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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

fn parse_pointer_to_member_type<'input, 'abbrev, 'unit, 'tree, Endian>(
    _dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<PointerToMemberType>
where
    Endian: gimli::Endianity,
{
    let mut ty = PointerToMemberType::default();

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    ty.ty = offset;
                },
                gimli::DW_AT_containing_type => {
                    if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                        ty.containing_ty = offset;
                    }
                }
                gimli::DW_AT_byte_size => {
                    ty.byte_size = attr.udata_value();
                }
                _ => debug!(
                    "unknown ptr_to_member type attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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

fn parse_subprogram<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let offset = node.entry().offset();
    let mut function = Function {
        id: Cell::new(0),
        offset: offset.to_debug_info_offset(&dwarf_unit.header).into(),
        namespace: namespace.clone(),
        name: None,
        symbol_name: None,
        linkage_name: None,
        source: Source::default(),
        address: None,
        size: None,
        inline: false,
        declaration: false,
        parameters: Vec::new(),
        return_type: TypeOffset::none(),
        inlined_functions: Vec::new(),
        variables: Vec::new(),
    };

    let mut specification = None;
    let mut abstract_origin = false;
    let mut high_pc = None;

    {
        let entry = node.entry();
        let mut attrs = entry.attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    function.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_linkage_name | gimli::DW_AT_MIPS_linkage_name => {
                    function.linkage_name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_decl_file => {
                    parse_source_file(dwarf_unit, &attr, &mut function.source)
                }
                gimli::DW_AT_decl_line => parse_source_line(&attr, &mut function.source),
                gimli::DW_AT_decl_column => parse_source_column(&attr, &mut function.source),
                gimli::DW_AT_inline => if let gimli::AttributeValue::Inline(val) = attr.value() {
                    match val {
                        gimli::DW_INL_inlined | gimli::DW_INL_declared_inlined => {
                            function.inline = true
                        }
                        _ => function.inline = false,
                    }
                },
                gimli::DW_AT_low_pc => if let gimli::AttributeValue::Addr(addr) = attr.value() {
                    // TODO: is address 0 ever valid?
                    if addr != 0 {
                        function.address = Some(addr);
                    }
                },
                gimli::DW_AT_high_pc => match attr.value() {
                    gimli::AttributeValue::Addr(addr) => high_pc = Some(addr),
                    gimli::AttributeValue::Udata(val) => if val != 0 {
                        function.size = Some(val);
                    },
                    _ => {}
                },
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    function.return_type = offset;
                },
                gimli::DW_AT_specification | gimli::DW_AT_abstract_origin => {
                    if let Some(offset) = parse_function_offset(dwarf_unit, &attr) {
                        specification = Some(offset);
                        abstract_origin = attr.name() == gimli::DW_AT_abstract_origin;
                    }
                }
                gimli::DW_AT_declaration => if let gimli::AttributeValue::Flag(flag) = attr.value()
                {
                    function.declaration = flag;
                },
                gimli::DW_AT_frame_base
                | gimli::DW_AT_external
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

        if let (Some(address), Some(high_pc)) = (function.address, high_pc) {
            if high_pc > address {
                function.size = Some(high_pc - address);
            }
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
        function.name = specification.name.clone();
    }
    if function.linkage_name.is_none() {
        function.linkage_name = specification.linkage_name.clone();
    }
    if function.source.is_none() {
        function.source = specification.source.clone();
    }
    if function.return_type.is_none() {
        function.return_type = specification.return_type;
    }
    if specification.inline {
        function.inline = true;
    }
    if abstract_origin {
        // We inherit all children, and then extend them when parsing our children.
        function.parameters = specification.parameters.clone();
        function.variables = specification.variables.clone();
    } else {
        // TODO: inherit children from specifications?
    }

    true
}

fn parse_subprogram_children<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    function: &mut Function<'input>,
    mut iter: gimli::EntriesTreeIter<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let namespace = Some(Namespace::new(
        &function.namespace,
        function.name.clone(),
        NamespaceKind::Function,
    ));
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter => {
                parse_parameter(&mut function.parameters, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_variable => {
                parse_local_variable(&mut function.variables, unit, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_inlined_subroutine => {
                function.inlined_functions.push(parse_inlined_subroutine(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    child,
                )?);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(
                    &mut function.inlined_functions,
                    &mut function.variables,
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

fn parse_parameter<'input, 'abbrev, 'unit, 'tree, Endian>(
    parameters: &mut Vec<Parameter<'input>>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut parameter = Parameter::default();
    let offset = node.entry().offset();
    let offset = offset.to_debug_info_offset(&dwarf_unit.header);
    parameter.offset = offset.into();
    let mut abstract_origin = None;

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_abstract_origin => {
                    if let Some(offset) = parse_parameter_offset(dwarf_unit, &attr) {
                        abstract_origin = Some(offset);
                    }
                }
                gimli::DW_AT_name => {
                    parameter.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    parameter.ty = offset;
                },
                gimli::DW_AT_decl_file
                | gimli::DW_AT_decl_line
                | gimli::DW_AT_decl_column
                | gimli::DW_AT_location
                | gimli::DW_AT_artificial
                | gimli::DW_AT_const_value
                | gimli::DW_AT_sibling => {}
                _ => debug!(
                    "unknown parameter attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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
            // TODO: enable this once we handle parameters in inlined subroutines
            //debug!("missing parameter abstract origin: 0x{:08x}", abstract_origin.0);
        }
    }

    parameters.push(parameter);
    Ok(())
}

fn parse_lexical_block<'input, 'abbrev, 'unit, 'tree, Endian>(
    inlined_functions: &mut Vec<InlinedFunction<'input>>,
    local_variables: &mut Vec<LocalVariable<'input>>,
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    namespace: &Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_low_pc
                | gimli::DW_AT_high_pc
                | gimli::DW_AT_ranges
                | gimli::DW_AT_sibling => {}
                _ => debug!(
                    "unknown lexical_block attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
        }
    }

    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_variable => {
                parse_local_variable(local_variables, unit, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_inlined_subroutine => {
                inlined_functions.push(parse_inlined_subroutine(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    child,
                )?);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(
                    inlined_functions,
                    local_variables,
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

fn parse_inlined_subroutine<'input, 'abbrev, 'unit, 'tree, Endian>(
    unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    subprograms: &mut Vec<DwarfSubprogram<'input>>,
    variables: &mut Vec<DwarfVariable<'input>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<InlinedFunction<'input>>
where
    Endian: gimli::Endianity,
{
    let mut function = InlinedFunction::default();
    let mut low_pc = None;
    let mut high_pc = None;
    let mut size = None;
    let mut ranges = None;
    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_abstract_origin => {
                    if let Some(offset) = parse_function_offset(dwarf_unit, &attr) {
                        function.abstract_origin = offset;
                    }
                }
                gimli::DW_AT_low_pc => if let gimli::AttributeValue::Addr(addr) = attr.value() {
                    low_pc = Some(addr);
                },
                gimli::DW_AT_high_pc => match attr.value() {
                    gimli::AttributeValue::Addr(addr) => high_pc = Some(addr),
                    gimli::AttributeValue::Udata(val) => size = Some(val),
                    _ => {}
                },
                gimli::DW_AT_ranges => {
                    if let gimli::AttributeValue::RangeListsRef(val) = attr.value() {
                        ranges = Some(val);
                    }
                }
                gimli::DW_AT_call_file => {
                    parse_source_file(dwarf_unit, &attr, &mut function.call_source)
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
    }

    if function.abstract_origin.is_none() {
        debug!("inlined_subroutine with no abstract origin");
    }

    if let Some(offset) = ranges {
        let mut size = 0;
        let low_pc = low_pc.unwrap_or(0);
        let mut ranges = dwarf.range_lists.ranges(
            offset,
            dwarf_unit.header.version(),
            dwarf_unit.header.address_size(),
            low_pc,
        )?;
        while let Some(range) = ranges.next()? {
            size += range.end.wrapping_sub(range.begin);
        }
        function.size = Some(size);
    } else if let Some(size) = size {
        function.size = Some(size);
    } else if let (Some(low_pc), Some(high_pc)) = (low_pc, high_pc) {
        function.size = Some(high_pc.wrapping_sub(low_pc));
    } else {
        debug!("unknown inlined_subroutine size");
    }

    // TODO: get the namespace from the abstract origin.
    // However, not sure if this if ever actually used in practice.
    let namespace = None;

    // TODO: handle abstract origin in all children
    // - we should start by inheriting all children from our abstract_origin
    // - then update the inherited children if they are pointed to by
    //   an abstract origin in one of our children
    let mut iter = node.children();
    while let Some(child) = iter.next()? {
        match child.entry().tag() {
            gimli::DW_TAG_formal_parameter => {
                parse_parameter(&mut function.parameters, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_variable => {
                parse_local_variable(&mut function.variables, unit, dwarf, dwarf_unit, child)?;
            }
            gimli::DW_TAG_inlined_subroutine => {
                function.inlined_functions.push(parse_inlined_subroutine(
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    child,
                )?);
            }
            gimli::DW_TAG_lexical_block => {
                parse_lexical_block(
                    &mut function.inlined_functions,
                    &mut function.variables,
                    unit,
                    dwarf,
                    dwarf_unit,
                    subprograms,
                    variables,
                    &namespace,
                    child,
                )?;
            }
            gimli::DW_TAG_GNU_call_site => {}
            tag => {
                debug!("unknown inlined_subroutine child tag: {}", tag);
            }
        }
    }
    Ok(function)
}

fn parse_variable<'input, 'abbrev, 'unit, 'tree, Endian>(
    _unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    namespace: Option<Rc<Namespace<'input>>>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<DwarfVariable<'input>>
where
    Endian: gimli::Endianity,
{
    let offset = node.entry().offset();
    let mut specification = None;
    let mut variable = Variable {
        offset: offset.to_debug_info_offset(&dwarf_unit.header).into(),
        namespace,
        ..Default::default()
    };

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_name => {
                    variable.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_linkage_name | gimli::DW_AT_MIPS_linkage_name => {
                    variable.linkage_name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    variable.ty = offset;
                },
                gimli::DW_AT_specification => {
                    if let Some(offset) = parse_variable_offset(dwarf_unit, &attr) {
                        specification = Some(offset);
                    }
                }
                gimli::DW_AT_declaration => if let gimli::AttributeValue::Flag(flag) = attr.value()
                {
                    variable.declaration = flag;
                },
                gimli::DW_AT_decl_file => {
                    parse_source_file(dwarf_unit, &attr, &mut variable.source)
                }
                gimli::DW_AT_decl_line => parse_source_line(&attr, &mut variable.source),
                gimli::DW_AT_decl_column => parse_source_column(&attr, &mut variable.source),
                gimli::DW_AT_location => {
                    match attr.value() {
                        gimli::AttributeValue::Exprloc(expr) => if let Some((address, size)) =
                            evaluate_variable_location(&dwarf_unit.header, expr)
                        {
                            variable.address = Some(address);
                            if size.is_some() {
                                variable.size = size;
                            }
                        },
                        gimli::AttributeValue::LocationListsRef(..) => {
                            // TODO
                        }
                        _ => {
                            debug!("unknown DW_AT_location: {:?}", attr.value());
                        }
                    }
                }
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

fn parse_local_variable<'input, 'abbrev, 'unit, 'tree, Endian>(
    variables: &mut Vec<LocalVariable<'input>>,
    _unit: &mut Unit<'input>,
    dwarf: &DwarfDebugInfo<'input, Endian>,
    dwarf_unit: &DwarfUnit<'input, Endian>,
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, Reader<'input, Endian>>,
) -> Result<()>
where
    Endian: gimli::Endianity,
{
    let mut variable = LocalVariable::default();
    let offset = node.entry().offset();
    let offset = offset.to_debug_info_offset(&dwarf_unit.header);
    variable.offset = offset.into();
    let mut abstract_origin = None;

    {
        let mut attrs = node.entry().attrs();
        while let Some(attr) = attrs.next()? {
            match attr.name() {
                gimli::DW_AT_abstract_origin => {
                    if let Some(offset) = parse_variable_offset(dwarf_unit, &attr) {
                        abstract_origin = Some(offset);
                    }
                }
                gimli::DW_AT_name => {
                    variable.name = attr.string_value(&dwarf.debug_str)
                        .map(|s| s.to_string_lossy());
                }
                gimli::DW_AT_type => if let Some(offset) = parse_type_offset(dwarf_unit, &attr) {
                    variable.ty = offset;
                },
                gimli::DW_AT_decl_file => {
                    parse_source_file(dwarf_unit, &attr, &mut variable.source)
                }
                gimli::DW_AT_decl_line => parse_source_line(&attr, &mut variable.source),
                gimli::DW_AT_decl_column => parse_source_column(&attr, &mut variable.source),
                gimli::DW_AT_location => {
                    match attr.value() {
                        gimli::AttributeValue::Exprloc(expr) => if let Some((address, size)) =
                            evaluate_variable_location(&dwarf_unit.header, expr)
                        {
                            variable.address = Some(address);
                            if size.is_some() {
                                variable.size = size;
                            }
                        },
                        gimli::AttributeValue::LocationListsRef(..) => {
                            // TODO
                        }
                        _ => {
                            debug!("unknown DW_AT_location: {:?}", attr.value());
                        }
                    }
                }
                gimli::DW_AT_alignment
                | gimli::DW_AT_artificial
                | gimli::DW_AT_const_value
                | gimli::DW_AT_external => {}
                _ => debug!(
                    "unknown local variable attribute: {} {:?}",
                    attr.name(),
                    attr.value()
                ),
            }
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
            if variable.address.is_some() {
                v.address = variable.address;
            }
            return Ok(());
        } else {
            // TODO: enable this once we handle variables in inlined subroutines
            //debug!("missing variable abstract origin: 0x{:08x}", abstract_origin.0);
        }
    }

    variables.push(variable);
    Ok(())
}

fn evaluate_member_location<'input, Endian>(
    unit: &gimli::CompilationUnitHeader<Reader<'input, Endian>>,
    expression: gimli::Expression<Reader<'input, Endian>>,
) -> Option<u64>
where
    Endian: gimli::Endianity + 'input,
{
    let pieces = evaluate(unit, expression, true);
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
    unit: &gimli::CompilationUnitHeader<Reader<'input, Endian>>,
    expression: gimli::Expression<Reader<'input, Endian>>,
) -> Option<(u64, Option<u64>)>
where
    Endian: gimli::Endianity + 'input,
{
    let pieces = evaluate(unit, expression, false);
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
                    // TODO: is address 0 ever valid?
                    if address != 0 {
                        result = Some((address, piece.size_in_bits.map(|x| (x + 7) / 8)));
                    }
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

fn evaluate<'input, Endian>(
    unit: &gimli::CompilationUnitHeader<Reader<'input, Endian>>,
    expression: gimli::Expression<Reader<'input, Endian>>,
    object_address: bool,
) -> Vec<gimli::Piece<Reader<'input, Endian>>>
where
    Endian: gimli::Endianity + 'input,
{
    let mut evaluation = expression.evaluation(unit.address_size(), unit.format());
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
            Ok(gimli::EvaluationResult::RequiresTextBase) => {
                result = evaluation.resume_with_text_base(0);
            }
            Ok(_x) => {
                //debug!("incomplete evaluation: {:?}", _x);
                return Vec::new();
            }
            Err(e) => {
                debug!("evaluation failed: {}", e);
                return Vec::new();
            }
        }
    }
}

impl From<gimli::DebugInfoOffset> for FunctionOffset {
    fn from(o: gimli::DebugInfoOffset) -> FunctionOffset {
        FunctionOffset::new(o.0)
    }
}

impl From<gimli::DebugInfoOffset> for ParameterOffset {
    fn from(o: gimli::DebugInfoOffset) -> ParameterOffset {
        ParameterOffset::new(o.0)
    }
}

impl From<gimli::DebugInfoOffset> for TypeOffset {
    fn from(o: gimli::DebugInfoOffset) -> TypeOffset {
        TypeOffset::new(o.0)
    }
}

impl From<gimli::DebugInfoOffset> for VariableOffset {
    fn from(o: gimli::DebugInfoOffset) -> VariableOffset {
        VariableOffset::new(o.0)
    }
}

fn parse_debug_info_offset<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
) -> Option<gimli::DebugInfoOffset>
where
    Endian: gimli::Endianity,
{
    match attr.value() {
        gimli::AttributeValue::UnitRef(offset) => {
            Some(offset.to_debug_info_offset(&dwarf_unit.header))
        }
        gimli::AttributeValue::DebugInfoRef(offset) => Some(offset),
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

fn parse_source_file<'input, Endian>(
    dwarf_unit: &DwarfUnit<'input, Endian>,
    attr: &gimli::Attribute<Reader<'input, Endian>>,
    source: &mut Source<'input>,
) where
    Endian: gimli::Endianity,
{
    match attr.value() {
        gimli::AttributeValue::FileIndex(val) => if val != 0 {
            if let Some(ref line) = dwarf_unit.line {
                if let Some(entry) = line.header().file(val) {
                    source.file = Some(entry.path_name().to_string_lossy());
                    if let Some(directory) = entry.directory(line.header()) {
                        source.directory = Some(directory.to_string_lossy());
                    } else {
                        debug!("invalid directory index {}", entry.directory_index());
                    }
                } else {
                    debug!("invalid file index {}", val);
                }
            }
        },
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
        gimli::AttributeValue::Udata(val) => if val != 0 {
            source.line = val;
        },
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
        gimli::AttributeValue::Udata(val) => if val != 0 {
            source.column = val;
        },
        val => {
            debug!("unknown DW_AT_decl_column attribute value: {:?}", val);
        }
    }
}
