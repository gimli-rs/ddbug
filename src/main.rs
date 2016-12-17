extern crate env_logger;
extern crate getopts;
extern crate gimli;
#[macro_use]
extern crate log;
extern crate memmap;
extern crate xmas_elf;
extern crate panopticon;

use std::borrow::Borrow;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::env;
use std::error;
use std::fmt;
use std::fmt::Debug;
use std::fs;
use std::ffi;
use std::io;
use std::io::Write;
use std::result;

use panopticon::amd64;

#[derive(Debug)]
pub struct Error(pub Cow<'static, str>);

impl error::Error for Error {
    fn description(&self) -> &str {
        self.0.borrow()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&'static str> for Error {
    fn from(s: &'static str) -> Error {
        Error(Cow::Borrowed(s))
    }
}

impl From<String> for Error {
    fn from(s: String) -> Error {
        Error(Cow::Owned(s))
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Error {
        Error(Cow::Owned(format!("IO error: {}", e)))
    }
}

impl From<gimli::Error> for Error {
    fn from(e: gimli::Error) -> Error {
        Error(Cow::Owned(format!("DWARF error: {}", e)))
    }
}

pub type Result<T> = result::Result<T, Error>;

struct Flags {
    calls: bool,
    inline_depth: usize,
}

fn main() {
    env_logger::init().ok();

    let mut opts = getopts::Options::new();
    opts.optflag("", "calls", "print subprogram calls");
    opts.optopt("",
                "inline-depth",
                "depth of inlined subroutine calls (0 to disable)",
                "DEPTH");

    let matches = match opts.parse(env::args().skip(1)) {
        Ok(m) => m,
        Err(e) => {
            error!("{}", e);
            print_usage(&opts);
        }
    };
    if matches.free.is_empty() {
        print_usage(&opts);
    }

    let mut flags = Flags {
        calls: false,
        inline_depth: 1,
    };
    if matches.opt_present("calls") {
        flags.calls = true;
    }
    if let Some(inline_depth) = matches.opt_str("inline-depth") {
        flags.inline_depth = match inline_depth.parse::<usize>() {
            Ok(inline_depth) => inline_depth,
            Err(e) => {
                error!("Invalid Argument '{}' to option 'inline-depth': {}",
                       inline_depth,
                       e);
                print_usage(&opts);
            }
        }
    }

    for path in &matches.free {
        if let Err(e) = handle_file(path, &flags) {
            error!("{}: {}", path, e);
        }
    }
}

fn print_usage(opts: &getopts::Options) -> ! {
    let brief = format!("Usage: {} <options> <file>", env::args().next().unwrap());
    write!(&mut io::stderr(), "{}", opts.usage(&brief)).ok();
    std::process::exit(1);
}

struct PrintState<'a, 'input>
    where 'input: 'a
{
    // TODO: use format independent machine type
    machine: xmas_elf::header::Machine,
    region: panopticon::Region,
    // All subprograms by address.
    all_subprograms: HashMap<u64, &'a Subprogram<'input>>,
    // Unit subprograms by offset.
    subprograms: HashMap<usize, &'a Subprogram<'input>>,
    // Unit types by offset.
    types: HashMap<usize, &'a Type<'input>>,
    address_size: Option<u64>,
    flags: &'a Flags,
}

fn handle_file(path: &str, flags: &Flags) -> Result<()> {
    let file = match fs::File::open(path) {
        Ok(file) => file,
        Err(e) => {
            return Err(format!("open failed: {}", e).into());
        }
    };

    let file = match memmap::Mmap::open(&file, memmap::Protection::Read) {
        Ok(file) => file,
        Err(e) => {
            return Err(format!("memmap failed: {}", e).into());
        }
    };

    let input = unsafe { file.as_slice() };
    let elf = xmas_elf::ElfFile::new(input);
    let machine = try!(elf.header.pt2).machine();
    let mut region = match machine {
        xmas_elf::header::Machine::X86_64 => {
            panopticon::Region::undefined("RAM".to_string(), 0xFFFF_FFFF_FFFF_FFFF)
        }
        machine => return Err(format!("Unsupported machine: {:?}", machine).into()),
    };

    for ph in elf.program_iter() {
        if ph.get_type() == Ok(xmas_elf::program::Type::Load) {
            let offset = ph.offset();
            let size = ph.file_size();
            let addr = ph.virtual_addr();
            if offset as usize <= elf.input.len() {
                let input = &elf.input[offset as usize..];
                if size as usize <= input.len() {
                    let bound = panopticon::Bound::new(addr, addr + size);
                    let layer = panopticon::Layer::wrap(input[..size as usize].to_vec());
                    region.cover(bound, layer);
                    debug!("loaded program header addr {:#x} size {:#x}", addr, size);
                } else {
                    debug!("invalid program header size {}", size);
                }
            } else {
                debug!("invalid program header offset {}", offset);
            }
        }
    }

    let units = match elf.header.pt1.data {
        xmas_elf::header::Data::LittleEndian => try!(parse_dwarf::<gimli::LittleEndian>(&elf)),
        xmas_elf::header::Data::BigEndian => try!(parse_dwarf::<gimli::BigEndian>(&elf)),
        _ => {
            return Err("Unknown endianity".into());
        }
    };

    let mut all_subprograms = HashMap::new();
    // TODO: insert symbol table names too
    for unit in units.iter() {
        for type_ in unit.types.iter() {
            match type_.kind {
                TypeKind::Struct(StructType { ref subprograms, .. }) |
                TypeKind::Union(UnionType { ref subprograms, .. }) |
                TypeKind::Enumeration(EnumerationType { ref subprograms, .. }) => {
                    for subprogram in subprograms.iter() {
                        if let Some(low_pc) = subprogram.low_pc {
                            all_subprograms.insert(low_pc, subprogram);
                        }
                    }
                }
                TypeKind::Base(_) |
                TypeKind::TypeDef(_) |
                TypeKind::Array(_) |
                TypeKind::Subroutine(_) |
                TypeKind::Modifier(_) |
                TypeKind::Unimplemented(_) => {}
            }
        }
        for subprogram in unit.subprograms.iter() {
            if let Some(low_pc) = subprogram.low_pc {
                all_subprograms.insert(low_pc, subprogram);
            }
        }
    }

    let stdout = std::io::stdout();
    let mut writer = stdout.lock();
    let mut state = PrintState {
        machine: machine,
        region: region,
        all_subprograms: all_subprograms,
        subprograms: HashMap::new(),
        types: HashMap::new(),
        address_size: None,
        flags: flags,
    };

    for unit in units.iter() {
        state.types.clear();
        state.subprograms.clear();
        for type_ in unit.types.iter() {
            state.types.insert(type_.offset.0, type_);
            match type_.kind {
                TypeKind::Struct(StructType { ref subprograms, .. }) |
                TypeKind::Union(UnionType { ref subprograms, .. }) |
                TypeKind::Enumeration(EnumerationType { ref subprograms, .. }) => {
                    for subprogram in subprograms.iter() {
                        state.subprograms.insert(subprogram.offset.0, subprogram);
                    }
                }
                TypeKind::Base(_) |
                TypeKind::TypeDef(_) |
                TypeKind::Array(_) |
                TypeKind::Subroutine(_) |
                TypeKind::Modifier(_) |
                TypeKind::Unimplemented(_) => {}
            }
        }
        for subprogram in unit.subprograms.iter() {
            state.subprograms.insert(subprogram.offset.0, subprogram);
        }
        state.address_size = unit.address_size;
        unit.print(&mut writer, &state)?;
    }
    Ok(())
}

struct DwarfFileState<'input, Endian>
    where Endian: gimli::Endianity
{
    debug_abbrev: gimli::DebugAbbrev<'input, Endian>,
    debug_info: gimli::DebugInfo<'input, Endian>,
    debug_str: gimli::DebugStr<'input, Endian>,
    debug_ranges: gimli::DebugRanges<'input, Endian>,
}

fn parse_dwarf<'input, Endian>(elf: &xmas_elf::ElfFile<'input>) -> Result<Vec<Unit<'input>>>
    where Endian: gimli::Endianity
{
    let debug_abbrev = elf.find_section_by_name(".debug_abbrev").map(|s| s.raw_data(elf));
    let debug_abbrev = gimli::DebugAbbrev::<Endian>::new(debug_abbrev.unwrap_or(&[]));
    let debug_info = elf.find_section_by_name(".debug_info").map(|s| s.raw_data(elf));
    let debug_info = gimli::DebugInfo::<Endian>::new(debug_info.unwrap_or(&[]));
    let debug_str = elf.find_section_by_name(".debug_str").map(|s| s.raw_data(elf));
    let debug_str = gimli::DebugStr::<Endian>::new(debug_str.unwrap_or(&[]));
    let debug_ranges = elf.find_section_by_name(".debug_ranges").map(|s| s.raw_data(elf));
    let debug_ranges = gimli::DebugRanges::<Endian>::new(debug_ranges.unwrap_or(&[]));

    let dwarf = DwarfFileState {
        debug_abbrev: debug_abbrev,
        debug_info: debug_info,
        debug_str: debug_str,
        debug_ranges: debug_ranges,
    };

    let mut units = Vec::new();
    let mut unit_headers = dwarf.debug_info.units();
    while let Some(unit_header) = try!(unit_headers.next()) {
        units.push(try!(Unit::parse_dwarf(&dwarf, &unit_header)));
    }
    Ok(units)
}

struct DwarfUnitState<'state, 'input, Endian>
    where Endian: 'state + gimli::Endianity,
          'input: 'state
{
    header: &'state gimli::CompilationUnitHeader<'input, Endian>,
    _abbrev: &'state gimli::Abbreviations,
    line: Option<gimli::DebugLineOffset>,
    ranges: Option<gimli::DebugRangesOffset>,
    namespaces: Vec<Option<&'input ffi::CStr>>,
}

#[derive(Debug, Default)]
struct Unit<'input> {
    dir: Option<&'input ffi::CStr>,
    name: Option<&'input ffi::CStr>,
    language: Option<gimli::DwLang>,
    address_size: Option<u64>,
    low_pc: Option<u64>,
    high_pc: Option<u64>,
    size: Option<u64>,
    types: Vec<Type<'input>>,
    subprograms: Vec<Subprogram<'input>>,
}

impl<'input> Unit<'input> {
    fn parse_dwarf<Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit_header: &gimli::CompilationUnitHeader<'input, Endian>
    ) -> Result<Unit<'input>>
        where Endian: gimli::Endianity
    {
        let abbrev = &try!(unit_header.abbreviations(dwarf.debug_abbrev));
        let mut unit_state = DwarfUnitState {
            header: unit_header,
            _abbrev: abbrev,
            line: None,
            ranges: None,
            namespaces: Vec::new(),
        };

        let mut tree = try!(unit_header.entries_tree(abbrev, None));
        let iter = tree.iter();

        let mut unit = Unit::default();
        unit.address_size = Some(unit_header.address_size() as u64);
        if let Some(entry) = iter.entry() {
            if entry.tag() != gimli::DW_TAG_compile_unit {
                return Err(format!("unknown CU tag: {}", entry.tag()).into());
            }
            let mut attrs = entry.attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_producer => {}
                    gimli::DW_AT_name => unit.name = attr.string_value(&dwarf.debug_str),
                    gimli::DW_AT_comp_dir => unit.dir = attr.string_value(&dwarf.debug_str),
                    gimli::DW_AT_language => {
                        if let gimli::AttributeValue::Language(language) = attr.value() {
                            unit.language = Some(language);
                        }
                    }
                    gimli::DW_AT_low_pc => {
                        if let gimli::AttributeValue::Addr(addr) = attr.value() {
                            unit.low_pc = Some(addr);
                        }
                    }
                    gimli::DW_AT_high_pc => {
                        match attr.value() {
                            gimli::AttributeValue::Addr(addr) => unit.high_pc = Some(addr),
                            gimli::AttributeValue::Udata(size) => unit.size = Some(size),
                            _ => {}
                        }
                    }
                    gimli::DW_AT_stmt_list => {
                        if let gimli::AttributeValue::DebugLineRef(line) = attr.value() {
                            unit_state.line = Some(line);
                        }
                    }
                    gimli::DW_AT_ranges => {
                        if let gimli::AttributeValue::DebugRangesRef(ranges) = attr.value() {
                            unit_state.ranges = Some(ranges);
                        }
                    }
                    gimli::DW_AT_entry_pc => {}
                    _ => debug!("unknown CU attribute: {} {:?}", attr.name(), attr.value()),
                }
            }
            debug!("{:?}", unit);
        } else {
            return Err("missing CU entry".into());
        };

        try!(unit.parse_dwarf_children(&dwarf, &mut unit_state, iter));
        Ok(unit)
    }

    fn parse_dwarf_children<'state, 'abbrev, 'unit, 'tree, Endian>(
        &mut self,
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<()>
        where Endian: gimli::Endianity
    {
        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_namespace => {
                    try!(self.parse_dwarf_namespace(dwarf, unit, child));
                }
                gimli::DW_TAG_subprogram => {
                    self.subprograms.push(try!(Subprogram::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_variable => {}
                gimli::DW_TAG_base_type |
                gimli::DW_TAG_structure_type |
                gimli::DW_TAG_union_type |
                gimli::DW_TAG_enumeration_type |
                gimli::DW_TAG_array_type |
                gimli::DW_TAG_subroutine_type |
                gimli::DW_TAG_typedef |
                gimli::DW_TAG_const_type |
                gimli::DW_TAG_pointer_type |
                gimli::DW_TAG_restrict_type => {
                    self.types.push(try!(Type::parse_dwarf(dwarf, unit, child)));
                }
                tag => {
                    debug!("unknown namespace child tag: {}", tag);
                }
            }
        }
        Ok(())
    }

    fn parse_dwarf_namespace<'state, 'abbrev, 'unit, 'tree, Endian>(
        &mut self,
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<()>
        where Endian: gimli::Endianity
    {
        let mut name = None;

        {
            let entry = iter.entry().unwrap();
            let mut attrs = entry.attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line => {}
                    _ => {
                        debug!("unknown namespace attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        unit.namespaces.push(name);
        let ret = self.parse_dwarf_children(dwarf, unit, iter);
        unit.namespaces.pop();
        ret
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        // The offsets of types that are unnamed struct and union members.
        let mut anon_members = HashSet::new();
        for type_ in self.types.iter() {
            type_.visit_members(&mut |t| {
                if t.is_anon() {
                    if let Some(offset) = t.type_ {
                        anon_members.insert(offset.0);
                    }
                }
            });
        }

        for type_ in self.types.iter() {
            // We print unnamed struct and union members inline, so no need
            // to print them again.
            //
            // Also don't print anonymous types. Normally these will have also
            // been printed inline (eg in a TypeDef). We don't actually check
            // that they have been printed already, but in future we could.
            if !type_.is_anon() && !anon_members.contains(&type_.offset.0) {
                type_.print(w, state)?;
            }
        }
        for subprogram in self.subprograms.iter() {
            subprogram.print(w, state)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct Type<'input> {
    offset: gimli::UnitOffset,
    kind: TypeKind<'input>,
}

#[derive(Debug)]
enum TypeKind<'input> {
    Base(BaseType<'input>),
    TypeDef(TypeDef<'input>),
    Struct(StructType<'input>),
    Union(UnionType<'input>),
    Enumeration(EnumerationType<'input>),
    Array(ArrayType<'input>),
    Subroutine(SubroutineType<'input>),
    Modifier(TypeModifier<'input>),
    Unimplemented(gimli::DwTag),
}

impl<'input> Default for Type<'input> {
    fn default() -> Self {
        Type {
            offset: gimli::UnitOffset(0),
            kind: TypeKind::Unimplemented(gimli::DwTag(0)),
        }
    }
}

impl<'input> Type<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<Type<'input>>
        where Endian: gimli::Endianity
    {
        let tag = iter.entry().unwrap().tag();
        let mut type_ = Type::default();
        type_.offset = iter.entry().unwrap().offset();
        type_.kind = match tag {
            gimli::DW_TAG_base_type => {
                TypeKind::Base(try!(BaseType::parse_dwarf(dwarf, unit, iter)))
            }
            gimli::DW_TAG_typedef => {
                TypeKind::TypeDef(try!(TypeDef::parse_dwarf(dwarf, unit, iter)))
            }
            gimli::DW_TAG_structure_type => {
                TypeKind::Struct(try!(StructType::parse_dwarf(dwarf, unit, iter)))
            }
            gimli::DW_TAG_union_type => {
                TypeKind::Union(try!(UnionType::parse_dwarf(dwarf, unit, iter)))
            }
            gimli::DW_TAG_enumeration_type => {
                TypeKind::Enumeration(try!(EnumerationType::parse_dwarf(dwarf, unit, iter)))
            }
            gimli::DW_TAG_array_type => {
                TypeKind::Array(try!(ArrayType::parse_dwarf(dwarf, unit, iter)))
            }
            gimli::DW_TAG_subroutine_type => {
                TypeKind::Subroutine(try!(SubroutineType::parse_dwarf(dwarf, unit, iter)))
            }
            gimli::DW_TAG_const_type => {
                TypeKind::Modifier(try!(TypeModifier::parse_dwarf(dwarf,
                                                                  unit,
                                                                  iter,
                                                                  TypeModifierKind::Const)))
            }
            gimli::DW_TAG_pointer_type => {
                TypeKind::Modifier(try!(TypeModifier::parse_dwarf(dwarf,
                                                                  unit,
                                                                  iter,
                                                                  TypeModifierKind::Pointer)))
            }
            gimli::DW_TAG_restrict_type => {
                TypeKind::Modifier(try!(TypeModifier::parse_dwarf(dwarf,
                                                                  unit,
                                                                  iter,
                                                                  TypeModifierKind::Restrict)))
            }
            _ => TypeKind::Unimplemented(tag),
        };
        Ok(type_)
    }

    fn from_offset<'a>(
        state: &PrintState<'a, 'input>,
        offset: gimli::UnitOffset
    ) -> Option<&'a Type<'input>> {
        state.types.get(&offset.0).map(|v| *v)
    }

    fn bit_size(&self, state: &PrintState) -> Option<u64> {
        match self.kind {
            TypeKind::Base(ref val) => val.bit_size(state),
            TypeKind::TypeDef(ref val) => val.bit_size(state),
            TypeKind::Struct(ref val) => val.bit_size(state),
            TypeKind::Union(ref val) => val.bit_size(state),
            TypeKind::Enumeration(ref val) => val.bit_size(state),
            TypeKind::Array(ref val) => val.bit_size(state),
            TypeKind::Subroutine(ref val) => val.bit_size(state),
            TypeKind::Modifier(ref val) => val.bit_size(state),
            TypeKind::Unimplemented(_) => None,
        }
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        match self.kind {
            TypeKind::Struct(ref val) => val.visit_members(f),
            TypeKind::Union(ref val) => val.visit_members(f),
            TypeKind::Enumeration(..) |
            TypeKind::TypeDef(..) |
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Subroutine(..) |
            TypeKind::Modifier(..) |
            TypeKind::Unimplemented(_) => {}
        }
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        match self.kind {
            TypeKind::TypeDef(ref val) => val.print(w, state)?,
            TypeKind::Struct(ref val) => val.print(w, state)?,
            TypeKind::Union(ref val) => val.print(w, state)?,
            TypeKind::Enumeration(ref val) => val.print(w, state)?,
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Subroutine(..) |
            TypeKind::Modifier(..) => {}
            TypeKind::Unimplemented(_) => {
                self.print_name(w, state)?;
                writeln!(w, "")?;
            }
        }
        Ok(())
    }

    fn print_name(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        match self.kind {
            TypeKind::Base(ref val) => val.print_name(w)?,
            TypeKind::TypeDef(ref val) => val.print_name(w)?,
            TypeKind::Struct(ref val) => val.print_name(w)?,
            TypeKind::Union(ref val) => val.print_name(w)?,
            TypeKind::Enumeration(ref val) => val.print_name(w)?,
            TypeKind::Array(ref val) => val.print_name(w, state)?,
            TypeKind::Subroutine(ref val) => val.print_name(w, state)?,
            TypeKind::Modifier(ref val) => val.print_name(w, state)?,
            TypeKind::Unimplemented(ref tag) => write!(w, "<unimplemented {}>", tag)?,
        }
        Ok(())
    }

    fn print_offset_name(
        w: &mut Write,
        state: &PrintState,
        offset: gimli::UnitOffset
    ) -> Result<()> {
        match Type::from_offset(state, offset) {
            Some(type_) => type_.print_name(w, state)?,
            None => write!(w, "<invalid-type>")?,
        }
        Ok(())
    }

    fn is_anon(&self) -> bool {
        match self.kind {
            TypeKind::Struct(ref val) => val.is_anon(),
            TypeKind::Union(ref val) => val.is_anon(),
            TypeKind::Base(..) |
            TypeKind::TypeDef(..) |
            TypeKind::Enumeration(..) |
            TypeKind::Array(..) |
            TypeKind::Subroutine(..) |
            TypeKind::Modifier(..) |
            TypeKind::Unimplemented(..) => false,
        }
    }
}

#[derive(Debug)]
struct TypeModifier<'input> {
    kind: TypeModifierKind,
    type_: Option<gimli::UnitOffset>,
    namespace: Vec<Option<&'input ffi::CStr>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
}

#[derive(Debug)]
enum TypeModifierKind {
    Const,
    Pointer,
    Restrict,
}

impl<'input> TypeModifier<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>,
        kind: TypeModifierKind
    ) -> Result<TypeModifier<'input>>
        where Endian: gimli::Endianity
    {
        let mut modifier = TypeModifier {
            kind: kind,
            type_: None,
            namespace: Vec::new(),
            name: None,
            byte_size: None,
        };

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        modifier.namespace = unit.namespaces.clone();
                        modifier.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            modifier.type_ = Some(offset);
                        }
                    }
                    gimli::DW_AT_byte_size => {
                        modifier.byte_size = attr.udata_value();
                    }
                    _ => {
                        debug!("unknown type modifier attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                tag => {
                    debug!("unknown type modifier child tag: {}", tag);
                }
            }
        }
        Ok(modifier)
    }

    fn bit_size(&self, state: &PrintState) -> Option<u64> {
        if let Some(byte_size) = self.byte_size {
            return Some(byte_size * 8);
        }
        match self.kind {
            TypeModifierKind::Const |
            TypeModifierKind::Restrict => {
                self.type_
                    .and_then(|v| Type::from_offset(state, v))
                    .and_then(|v| v.bit_size(state))
            }
            TypeModifierKind::Pointer => state.address_size.map(|v| v * 8),
        }
    }

    fn print_name(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        if let Some(name) = self.name {
            // Not sure namespace is required here.
            for namespace in self.namespace.iter() {
                match *namespace {
                    Some(ref name) => write!(w, "{}::", name.to_string_lossy())?,
                    None => write!(w, "<anon>")?,
                }
            }
            write!(w, "{}", name.to_string_lossy())?;
        } else {
            match self.kind {
                TypeModifierKind::Const => write!(w, "const ")?,
                TypeModifierKind::Pointer => write!(w, "* ")?,
                TypeModifierKind::Restrict => write!(w, "restrict ")?,
            }
            match self.type_ {
                Some(type_) => Type::print_offset_name(w, state, type_)?,
                None => write!(w, "<unknown-type>")?,
            }
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct BaseType<'input> {
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
}

impl<'input> BaseType<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        _unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<BaseType<'input>>
        where Endian: gimli::Endianity
    {
        let mut type_ = BaseType::default();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        type_.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_byte_size => {
                        type_.byte_size = attr.udata_value();
                    }
                    gimli::DW_AT_encoding => {}
                    _ => {
                        debug!("unknown base type attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                tag => {
                    debug!("unknown base type child tag: {}", tag);
                }
            }
        }
        Ok(type_)
    }

    fn bit_size(&self, _state: &PrintState) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon-base-type>")?,
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct TypeDef<'input> {
    name: Option<&'input ffi::CStr>,
    type_: Option<gimli::UnitOffset>,
}

impl<'input> TypeDef<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        _unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<TypeDef<'input>>
        where Endian: gimli::Endianity
    {
        let mut typedef = TypeDef::default();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        typedef.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            typedef.type_ = Some(offset);
                        }
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line => {}
                    _ => {
                        debug!("unknown typedef attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                tag => {
                    debug!("unknown typedef child tag: {}", tag);
                }
            }
        }
        Ok(typedef)
    }

    fn bit_size(&self, state: &PrintState) -> Option<u64> {
        self.type_.and_then(|t| Type::from_offset(state, t)).and_then(|v| v.bit_size(state))
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        write!(w, "type ")?;
        self.print_name(w)?;
        if let Some(type_) = self.type_.and_then(|t| Type::from_offset(state, t)) {
            write!(w, " = ")?;
            if type_.is_anon() {
                type_.print(w, state)?;
            } else {
                type_.print_name(w, state)?;
                writeln!(w, "")?;
            }
        } else {
            writeln!(w, "")?;
        }
        if let Some(bit_size) = self.bit_size(state) {
            writeln!(w, "\tsize: {}", format_bit(bit_size))?;
        }
        writeln!(w, "")?;
        Ok(())
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon-typedef>")?,
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct StructType<'input> {
    namespace: Vec<Option<&'input ffi::CStr>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
    declaration: bool,
    members: Vec<Member<'input>>,
    subprograms: Vec<Subprogram<'input>>,
}

impl<'input> StructType<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<StructType<'input>>
        where Endian: gimli::Endianity
    {
        let mut type_ = StructType::default();
        type_.namespace = unit.namespaces.clone();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        type_.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_byte_size => {
                        type_.byte_size = attr.udata_value();
                    }
                    gimli::DW_AT_declaration => {
                        if let gimli::AttributeValue::Flag(flag) = attr.value() {
                            type_.declaration = flag;
                        }
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line |
                    gimli::DW_AT_sibling => {}
                    _ => {
                        debug!("unknown struct attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        unit.namespaces.push(type_.name);
        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_subprogram => {
                    type_.subprograms.push(try!(Subprogram::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_member => {
                    type_.members.push(try!(Member::parse_dwarf(dwarf, unit, child)));
                }
                tag => {
                    debug!("unknown struct child tag: {}", tag);
                }
            }
        }
        unit.namespaces.pop();
        Ok(type_)
    }

    fn bit_size(&self, _state: &PrintState) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in self.members.iter() {
            f(member);
        }
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        self.print_name(w)?;
        writeln!(w, "")?;

        if let Some(size) = self.byte_size {
            writeln!(w, "\tsize: {}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }

        if self.declaration {
            writeln!(w, "\tdeclaration: yes")?;
        }

        if !self.members.is_empty() {
            writeln!(w, "\tmembers:")?;
            self.print_members(w, state, Some(0), 2)?;
        }

        writeln!(w, "")?;

        for subprogram in self.subprograms.iter() {
            subprogram.print(w, state)?;
        }
        Ok(())
    }

    fn print_members(
        &self,
        w: &mut Write,
        state: &PrintState,
        mut bit_offset: Option<u64>,
        indent: usize
    ) -> Result<()> {
        for member in self.members.iter() {
            member.print(w, state, &mut bit_offset, indent)?;
        }
        Ok(())
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        write!(w, "struct ")?;
        for namespace in self.namespace.iter() {
            match *namespace {
                Some(ref name) => write!(w, "{}::", name.to_string_lossy())?,
                None => write!(w, "<anon>")?,
            }
        }
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn is_anon(&self) -> bool {
        self.name.is_none()
    }
}

#[derive(Debug, Default)]
struct UnionType<'input> {
    namespace: Vec<Option<&'input ffi::CStr>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
    declaration: bool,
    members: Vec<Member<'input>>,
    subprograms: Vec<Subprogram<'input>>,
}

impl<'input> UnionType<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<UnionType<'input>>
        where Endian: gimli::Endianity
    {
        let mut type_ = UnionType::default();
        type_.namespace = unit.namespaces.clone();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        type_.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_byte_size => {
                        type_.byte_size = attr.udata_value();
                    }
                    gimli::DW_AT_declaration => {
                        if let gimli::AttributeValue::Flag(flag) = attr.value() {
                            type_.declaration = flag;
                        }
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line |
                    gimli::DW_AT_sibling => {}
                    _ => {
                        debug!("unknown union attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        unit.namespaces.push(type_.name);
        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_subprogram => {
                    type_.subprograms.push(try!(Subprogram::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_member => {
                    type_.members.push(try!(Member::parse_dwarf(dwarf, unit, child)));
                }
                tag => {
                    debug!("unknown union child tag: {}", tag);
                }
            }
        }
        unit.namespaces.pop();
        Ok(type_)
    }

    fn bit_size(&self, _state: &PrintState) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in self.members.iter() {
            f(member);
        }
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        self.print_name(w)?;
        writeln!(w, "")?;

        if let Some(size) = self.byte_size {
            writeln!(w, "\tsize: {}", size)?;
        } else if !self.declaration {
            debug!("union with no size");
        }

        if self.declaration {
            writeln!(w, "\tdeclaration: yes")?;
        }

        if !self.members.is_empty() {
            writeln!(w, "\tmembers:")?;
            self.print_members(w, state, Some(0), 2)?;
        }

        writeln!(w, "")?;

        for subprogram in self.subprograms.iter() {
            subprogram.print(w, state)?;
        }
        Ok(())
    }

    fn print_members(
        &self,
        w: &mut Write,
        state: &PrintState,
        bit_offset: Option<u64>,
        indent: usize
    ) -> Result<()> {
        for member in self.members.iter() {
            let mut bit_offset = bit_offset;
            member.print(w, state, &mut bit_offset, indent)?;
        }
        Ok(())
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        write!(w, "union ")?;
        for namespace in self.namespace.iter() {
            match *namespace {
                Some(ref name) => write!(w, "{}::", name.to_string_lossy())?,
                None => write!(w, "<anon>")?,
            }
        }
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn is_anon(&self) -> bool {
        self.name.is_none()
    }
}

#[derive(Debug, Default)]
struct Member<'input> {
    name: Option<&'input ffi::CStr>,
    type_: Option<gimli::UnitOffset>,
    // Defaults to 0, so always present.
    bit_offset: u64,
    bit_size: Option<u64>,
}

impl<'input> Member<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<Member<'input>>
        where Endian: gimli::Endianity
    {
        let mut member = Member::default();
        let mut bit_offset = None;
        let mut byte_size = None;

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        member.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            member.type_ = Some(offset);
                        }
                    }
                    gimli::DW_AT_data_member_location => {
                        match attr.value() {
                            gimli::AttributeValue::Udata(v) => member.bit_offset = v * 8,
                            gimli::AttributeValue::Exprloc(expr) => {
                                match evaluate(unit.header, expr.0) {
                                    Ok(gimli::Location::Address { address }) => {
                                        member.bit_offset = address * 8;
                                    }
                                    Ok(loc) => {
                                        debug!("unknown DW_AT_data_member_location result: {:?}",
                                               loc)
                                    }
                                    Err(e) => {
                                        debug!("DW_AT_data_member_location evaluation failed: {}",
                                               e)
                                    }
                                }
                            }
                            _ => {
                                debug!("unknown DW_AT_data_member_location: {:?}", attr.value());
                            }
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
                        member.bit_size = attr.udata_value();
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line => {}
                    _ => {
                        debug!("unknown member attribute: {} {:?}",
                               attr.name(),
                               attr.value());
                    }
                }
            }
        }

        if let (Some(bit_offset), Some(bit_size)) = (bit_offset, member.bit_size) {
            // DWARF version 2/3, but allowed in later versions for compatibility.
            // The data member is a bit field contained in an anonymous object.
            // member.bit_offset starts as the offset of the anonymous object.
            // byte_size is the size of the anonymous object.
            // bit_offset is the offset from the anonymous object MSB to the bit field MSB.
            // bit_size is the size of the bit field.
            if Endian::is_big_endian() {
                // For big endian, the MSB is the first bit, so we simply add bit_offset,
                // and byte_size is unneeded.
                member.bit_offset = member.bit_offset.wrapping_add(bit_offset);
            } else {
                // For little endian, we have to work backwards, so we need byte_size.
                if let Some(byte_size) = byte_size {
                    // First find the offset of the MSB of the anonymous object.
                    member.bit_offset = member.bit_offset.wrapping_add(byte_size * 8);
                    // Then go backwards to the LSB of the bit field.
                    member.bit_offset = member.bit_offset
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

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                tag => {
                    debug!("unknown member child tag: {}", tag);
                }
            }
        }
        Ok(member)
    }

    fn bit_size(&self, state: &PrintState) -> Option<u64> {
        if self.bit_size.is_some() {
            self.bit_size
        } else if let Some(type_) = self.type_ {
            Type::from_offset(state, type_).and_then(|v| v.bit_size(state))
        } else {
            None
        }
    }

    fn print(
        &self,
        w: &mut Write,
        state: &PrintState,
        end_bit_offset: &mut Option<u64>,
        indent: usize
    ) -> Result<()> {
        if let Some(end_bit_offset) = *end_bit_offset {
            if self.bit_offset > end_bit_offset {
                for _ in 0..indent {
                    write!(w, "\t")?;
                }
                writeln!(w,
                         "{}[{}]\t<padding>",
                         format_bit(end_bit_offset),
                         format_bit(self.bit_offset - end_bit_offset))?;
            }
        }

        for _ in 0..indent {
            write!(w, "\t")?;
        }
        write!(w, "{}", format_bit(self.bit_offset))?;
        match self.bit_size(state) {
            Some(bit_size) => {
                write!(w, "[{}]", format_bit(bit_size))?;
                *end_bit_offset = self.bit_offset.checked_add(bit_size);
            }
            None => {
                // TODO: show element size for unsized arrays.
                debug!("no size for {:?}", self);
                write!(w, "[??]")?;
                *end_bit_offset = None;
            }
        }
        match self.name {
            Some(name) => write!(w, "\t{}", name.to_string_lossy())?,
            None => write!(w, "\t<anon>")?,
        }
        if let Some(type_) = self.type_.and_then(|v| Type::from_offset(state, v)) {
            write!(w, ": ")?;
            type_.print_name(w, state)?;
            writeln!(w, "")?;
            if self.is_anon() || type_.is_anon() {
                match type_.kind {
                    TypeKind::Struct(ref t) => {
                        t.print_members(w, state, Some(self.bit_offset), indent + 1)?
                    }
                    TypeKind::Union(ref t) => {
                        t.print_members(w, state, Some(self.bit_offset), indent + 1)?
                    }
                    _ => {
                        debug!("unknown anon member: {:?}", type_);
                    }
                }
            }
        } else {
            writeln!(w, ": <invalid-type>")?;
        }
        Ok(())
    }

    fn is_anon(&self) -> bool {
        self.name.is_none()
    }
}

#[derive(Debug, Default)]
struct EnumerationType<'input> {
    namespace: Vec<Option<&'input ffi::CStr>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
    enumerators: Vec<Enumerator<'input>>,
    subprograms: Vec<Subprogram<'input>>,
}

impl<'input> EnumerationType<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<EnumerationType<'input>>
        where Endian: gimli::Endianity
    {
        let mut type_ = EnumerationType::default();
        type_.namespace = unit.namespaces.clone();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        type_.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_byte_size => {
                        type_.byte_size = attr.udata_value();
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line |
                    gimli::DW_AT_sibling => {}
                    gimli::DW_AT_type |
                    gimli::DW_AT_enum_class => {}
                    _ => {
                        debug!("unknown enumeration attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        unit.namespaces.push(type_.name);
        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_enumerator => {
                    type_.enumerators.push(try!(Enumerator::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_subprogram => {
                    type_.subprograms.push(try!(Subprogram::parse_dwarf(dwarf, unit, child)));
                }
                tag => {
                    debug!("unknown enumeration child tag: {}", tag);
                }
            }
        }
        unit.namespaces.pop();
        Ok(type_)
    }

    fn bit_size(&self, _state: &PrintState) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        self.print_name(w)?;
        writeln!(w, "")?;

        if let Some(size) = self.byte_size {
            writeln!(w, "\tsize: {}", size)?;
        }

        if !self.enumerators.is_empty() {
            writeln!(w, "\tenumerators:")?;
            for enumerator in self.enumerators.iter() {
                enumerator.print(w, state)?;
            }
        }

        writeln!(w, "")?;

        for subprogram in self.subprograms.iter() {
            subprogram.print(w, state)?;
        }
        Ok(())
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        write!(w, "enum ")?;
        for namespace in self.namespace.iter() {
            match *namespace {
                Some(ref name) => write!(w, "{}::", name.to_string_lossy())?,
                None => write!(w, "<anon>")?,
            }
        }
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Enumerator<'input> {
    name: Option<&'input ffi::CStr>,
    value: Option<i64>,
}

impl<'input> Enumerator<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        _unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<Enumerator<'input>>
        where Endian: gimli::Endianity
    {
        let mut enumerator = Enumerator::default();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(ref attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        enumerator.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_const_value => {
                        if let Some(value) = attr.sdata_value() {
                            enumerator.value = Some(value);
                        } else {
                            debug!("unknown enumerator const_value: {:?}", attr.value());
                        }
                    }
                    _ => {
                        debug!("unknown enumerator attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                tag => {
                    debug!("unknown enumerator child tag: {}", tag);
                }
            }
        }
        Ok(enumerator)
    }

    fn print(&self, w: &mut Write, _state: &PrintState) -> Result<()> {
        write!(w, "\t\t")?;
        self.print_name(w)?;
        if let Some(value) = self.value {
            write!(w, "({})", value)?;
        }
        writeln!(w, "")?;
        Ok(())
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct ArrayType<'input> {
    type_: Option<gimli::UnitOffset>,
    count: Option<u64>,
    phantom: std::marker::PhantomData<&'input [u8]>,
}

impl<'input> ArrayType<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        _dwarf: &DwarfFileState<'input, Endian>,
        _unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<ArrayType<'input>>
        where Endian: gimli::Endianity
    {
        let mut array = ArrayType::default();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            array.type_ = Some(offset);
                        }
                    }
                    gimli::DW_AT_sibling => {}
                    _ => {
                        debug!("unknown array attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_subrange_type => {
                    let mut attrs = child.entry().unwrap().attrs();
                    while let Some(attr) = try!(attrs.next()) {
                        match attr.name() {
                            gimli::DW_AT_count => {
                                array.count = attr.udata_value();
                            }
                            gimli::DW_AT_upper_bound => {
                                // TODO: use AT_lower_bound too
                                array.count = attr.udata_value();
                            }
                            gimli::DW_AT_type |
                            gimli::DW_AT_lower_bound => {}
                            _ => {
                                debug!("unknown array subrange attribute: {} {:?}",
                                       attr.name(),
                                       attr.value())
                            }
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

    fn bit_size(&self, state: &PrintState) -> Option<u64> {
        if let (Some(type_), Some(count)) = (self.type_, self.count) {
            Type::from_offset(state, type_).and_then(|t| t.bit_size(state)).map(|v| v * count)
        } else {
            None
        }
    }

    fn print_name(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        write!(w, "[")?;
        match self.type_ {
            Some(type_) => Type::print_offset_name(w, state, type_)?,
            None => write!(w, "<unknown-type>")?,
        }
        if let Some(count) = self.count {
            write!(w, "; {}", count)?;
        }
        write!(w, "]")?;
        Ok(())
    }
}

#[derive(Debug, Default)]
struct SubroutineType<'input> {
    parameters: Vec<Parameter<'input>>,
    return_type: Option<gimli::UnitOffset>,
}

impl<'input> SubroutineType<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<SubroutineType<'input>>
        where Endian: gimli::Endianity
    {
        let mut subroutine = SubroutineType::default();

        {
            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            subroutine.return_type = Some(offset);
                        }
                    }
                    gimli::DW_AT_prototyped |
                    gimli::DW_AT_sibling => {}
                    _ => {
                        debug!("unknown subroutine attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_formal_parameter => {
                    subroutine.parameters.push(try!(Parameter::parse_dwarf(dwarf, unit, child)));
                }
                tag => {
                    debug!("unknown subroutine child tag: {}", tag);
                }
            }
        }
        Ok(subroutine)
    }

    fn bit_size(&self, _state: &PrintState) -> Option<u64> {
        None
    }

    fn print_name(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        let mut first = true;
        write!(w, "(")?;
        for parameter in self.parameters.iter() {
            if first {
                first = false;
            } else {
                write!(w, ", ")?;
            }
            parameter.print(w, state)?;
        }
        write!(w, ")")?;

        if let Some(return_type) = self.return_type {
            write!(w, " -> ")?;
            Type::print_offset_name(w, state, return_type)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct Subprogram<'input> {
    offset: gimli::UnitOffset,
    namespace: Vec<Option<&'input ffi::CStr>>,
    name: Option<&'input ffi::CStr>,
    linkage_name: Option<&'input ffi::CStr>,
    low_pc: Option<u64>,
    high_pc: Option<u64>,
    size: Option<u64>,
    inline: bool,
    declaration: bool,
    parameters: Vec<Parameter<'input>>,
    return_type: Option<gimli::UnitOffset>,
    inlined_subroutines: Vec<InlinedSubroutine>,
}

impl<'input> Default for Subprogram<'input> {
    fn default() -> Self {
        Subprogram {
            offset: gimli::UnitOffset(0),
            namespace: Vec::new(),
            name: None,
            linkage_name: None,
            low_pc: None,
            high_pc: None,
            size: None,
            inline: false,
            declaration: false,
            parameters: Vec::new(),
            return_type: None,
            inlined_subroutines: Vec::new(),
        }
    }
}

impl<'input> Subprogram<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<Subprogram<'input>>
        where Endian: gimli::Endianity
    {
        let mut subprogram = Subprogram::default();
        subprogram.offset = iter.entry().unwrap().offset();
        subprogram.namespace = unit.namespaces.clone();

        {
            let entry = iter.entry().unwrap();
            let mut attrs = entry.attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        subprogram.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_linkage_name => {
                        subprogram.linkage_name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_inline => {
                        if let gimli::AttributeValue::Inline(val) = attr.value() {
                            match val {
                                gimli::DW_INL_inlined |
                                gimli::DW_INL_declared_inlined => subprogram.inline = true,
                                _ => subprogram.inline = false,
                            }
                        }
                    }
                    gimli::DW_AT_low_pc => {
                        if let gimli::AttributeValue::Addr(addr) = attr.value() {
                            subprogram.low_pc = Some(addr);
                        }
                    }
                    gimli::DW_AT_high_pc => {
                        match attr.value() {
                            gimli::AttributeValue::Addr(addr) => subprogram.high_pc = Some(addr),
                            gimli::AttributeValue::Udata(size) => subprogram.size = Some(size),
                            _ => {}
                        }
                    }
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            subprogram.return_type = Some(offset);
                        }
                    }
                    gimli::DW_AT_declaration => {
                        if let gimli::AttributeValue::Flag(flag) = attr.value() {
                            subprogram.declaration = flag;
                        }
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line |
                    gimli::DW_AT_frame_base |
                    gimli::DW_AT_external |
                    gimli::DW_AT_abstract_origin |
                    gimli::DW_AT_GNU_all_call_sites |
                    gimli::DW_AT_GNU_all_tail_call_sites |
                    gimli::DW_AT_prototyped |
                    gimli::DW_AT_sibling => {}
                    _ => {
                        debug!("unknown subprogram attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }

            if let Some(low_pc) = subprogram.low_pc {
                if let Some(high_pc) = subprogram.high_pc {
                    subprogram.size = high_pc.checked_sub(low_pc);
                } else if let Some(size) = subprogram.size {
                    subprogram.high_pc = low_pc.checked_add(size);
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_formal_parameter => {
                    subprogram.parameters.push(try!(Parameter::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_inlined_subroutine => {
                    subprogram.inlined_subroutines
                        .push(try!(InlinedSubroutine::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_lexical_block => {
                    try!(parse_dwarf_lexical_block(&mut subprogram.inlined_subroutines,
                                                   dwarf,
                                                   unit,
                                                   child));
                }
                gimli::DW_TAG_template_type_parameter |
                gimli::DW_TAG_variable |
                gimli::DW_TAG_label |
                gimli::DW_TAG_structure_type |
                gimli::DW_TAG_union_type |
                gimli::DW_TAG_GNU_call_site => {}
                tag => {
                    debug!("unknown subprogram child tag: {}", tag);
                }
            }
        }

        Ok(subprogram)
    }

    fn from_offset<'a>(
        state: &PrintState<'a, 'input>,
        offset: gimli::UnitOffset
    ) -> Option<&'a Subprogram<'input>> {
        state.subprograms.get(&offset.0).map(|v| *v)
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        write!(w, "fn ")?;
        for namespace in self.namespace.iter() {
            match *namespace {
                Some(ref name) => write!(w, "{}::", name.to_string_lossy())?,
                None => write!(w, "<anon>")?,
            }
        }
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }

        writeln!(w, "")?;

        if let Some(linkage_name) = self.linkage_name {
            writeln!(w, "\tlinkage name: {}", linkage_name.to_string_lossy())?;
        }

        if let (Some(low_pc), Some(high_pc)) = (self.low_pc, self.high_pc) {
            if high_pc > low_pc {
                writeln!(w, "\taddress: 0x{:x}-0x{:x}", low_pc, high_pc - 1)?;
            } else {
                writeln!(w, "\taddress: 0x{:x}", low_pc)?;
            }
        } else if !self.inline && !self.declaration {
            debug!("non-inline subprogram with no address");
        }

        if let Some(size) = self.size {
            writeln!(w, "\tsize: {}", size)?;
        }

        if self.inline {
            writeln!(w, "\tinline: yes")?;
        }
        if self.declaration {
            writeln!(w, "\tdeclaration: yes")?;
        }

        if let Some(return_type) = self.return_type {
            writeln!(w, "\treturn type:")?;
            write!(w, "\t\t")?;
            match Type::from_offset(state, return_type).and_then(|t| t.bit_size(state)) {
                Some(bit_size) => write!(w, "[{}]", format_bit(bit_size))?,
                None => write!(w, "[??]")?,
            }
            write!(w, "\t")?;
            Type::print_offset_name(w, state, return_type)?;
            writeln!(w, "")?;
        }

        if !self.parameters.is_empty() {
            writeln!(w, "\tparameters:")?;
            for parameter in self.parameters.iter() {
                write!(w, "\t\t")?;
                match parameter.bit_size(state) {
                    Some(bit_size) => write!(w, "[{}]", format_bit(bit_size))?,
                    None => write!(w, "[??]")?,
                }
                write!(w, "\t")?;
                parameter.print(w, state)?;
                writeln!(w, "")?;
            }
        }

        if state.flags.inline_depth > 0 && !self.inlined_subroutines.is_empty() {
            writeln!(w, "\tinlined subroutines:")?;
            for subroutine in self.inlined_subroutines.iter() {
                subroutine.print(w, state, 1)?;
            }
        }

        if let (Some(low_pc), Some(high_pc)) = (self.low_pc, self.high_pc) {
            if low_pc != 0 {
                if state.flags.calls {
                    let calls = disassemble(state.machine, &state.region, low_pc, high_pc);
                    if !calls.is_empty() {
                        writeln!(w, "\tcalls:")?;
                        for call in &calls {
                            write!(w, "\t\t0x{:x}", call)?;
                            if let Some(subprogram) = state.all_subprograms.get(call) {
                                write!(w, " ")?;
                                subprogram.print_name(w)?;
                            }
                            writeln!(w, "")?;
                        }
                    }
                }
            }
        }

        writeln!(w, "")?;
        Ok(())
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        for namespace in self.namespace.iter() {
            match *namespace {
                Some(ref name) => write!(w, "{}::", name.to_string_lossy())?,
                None => write!(w, "<anon>")?,
            }
        }
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Parameter<'input> {
    name: Option<&'input ffi::CStr>,
    type_: Option<gimli::UnitOffset>,
}

impl<'input> Parameter<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        _unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<Parameter<'input>>
        where Endian: gimli::Endianity
    {
        let mut parameter = Parameter::default();

        {
            let entry = iter.entry().unwrap();
            let mut attrs = entry.attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        parameter.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            parameter.type_ = Some(offset);
                        }
                    }
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line |
                    gimli::DW_AT_location |
                    gimli::DW_AT_abstract_origin => {}
                    _ => {
                        debug!("unknown parameter attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                tag => {
                    debug!("unknown parameter child tag: {}", tag);
                }
            }
        }
        Ok(parameter)
    }

    fn bit_size(&self, state: &PrintState) -> Option<u64> {
        self.type_
            .and_then(|t| Type::from_offset(state, t))
            .and_then(|t| t.bit_size(state))
    }

    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        if let Some(name) = self.name {
            write!(w, "{}: ", name.to_string_lossy())?;
        }
        match self.type_ {
            Some(offset) => Type::print_offset_name(w, state, offset)?,
            None => write!(w, ": <anon>")?,
        }
        Ok(())
    }
}

fn parse_dwarf_lexical_block<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    inlined_subroutines: &mut Vec<InlinedSubroutine>,
    dwarf: &DwarfFileState<'input, Endian>,
    unit: &mut DwarfUnitState<'state, 'input, Endian>,
    mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
) -> Result<()>
    where Endian: gimli::Endianity
{
    {
        let entry = iter.entry().unwrap();
        let mut attrs = entry.attrs();
        while let Some(attr) = try!(attrs.next()) {
            match attr.name() {
                gimli::DW_AT_low_pc |
                gimli::DW_AT_high_pc |
                gimli::DW_AT_ranges |
                gimli::DW_AT_sibling => {}
                _ => {
                    debug!("unknown lexical_block attribute: {} {:?}",
                           attr.name(),
                           attr.value())
                }
            }
        }
    }

    while let Some(child) = try!(iter.next()) {
        match child.entry().unwrap().tag() {
            gimli::DW_TAG_inlined_subroutine => {
                inlined_subroutines.push(try!(InlinedSubroutine::parse_dwarf(dwarf, unit, child)));
            }
            gimli::DW_TAG_lexical_block => {
                try!(parse_dwarf_lexical_block(inlined_subroutines, dwarf, unit, child));
            }
            gimli::DW_TAG_variable => {}
            tag => {
                debug!("unknown lexical_block child tag: {}", tag);
            }
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
struct InlinedSubroutine {
    abstract_origin: Option<gimli::UnitOffset>,
    size: Option<u64>,
    inlined_subroutines: Vec<InlinedSubroutine>,
}

impl InlinedSubroutine {
    fn parse_dwarf<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<InlinedSubroutine>
        where Endian: gimli::Endianity
    {
        let mut subroutine = InlinedSubroutine::default();
        let mut low_pc = None;
        let mut high_pc = None;
        let mut size = None;
        let mut ranges = None;
        {
            let entry = iter.entry().unwrap();
            let mut attrs = entry.attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_abstract_origin => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            subroutine.abstract_origin = Some(offset);
                        }
                    }
                    gimli::DW_AT_low_pc => {
                        if let gimli::AttributeValue::Addr(addr) = attr.value() {
                            low_pc = Some(addr);
                        }
                    }
                    gimli::DW_AT_high_pc => {
                        match attr.value() {
                            gimli::AttributeValue::Addr(addr) => high_pc = Some(addr),
                            gimli::AttributeValue::Udata(val) => size = Some(val),
                            _ => {}
                        }
                    }
                    gimli::DW_AT_ranges => {
                        if let gimli::AttributeValue::DebugRangesRef(val) = attr.value() {
                            ranges = Some(val);
                        }
                    }
                    gimli::DW_AT_call_file |
                    gimli::DW_AT_call_line |
                    gimli::DW_AT_sibling => {}
                    _ => {
                        debug!("unknown inlined_subroutine attribute: {} {:?}",
                               attr.name(),
                               attr.value())
                    }
                }
            }
        }

        if let Some(offset) = ranges {
            let mut size = 0;
            let low_pc = low_pc.unwrap_or(0);
            let mut ranges = try!(dwarf.debug_ranges
                .ranges(offset, unit.header.address_size(), low_pc));
            while let Some(range) = try!(ranges.next()) {
                size += range.end.wrapping_sub(range.begin);
            }
            subroutine.size = Some(size);
        } else if let Some(size) = size {
            subroutine.size = Some(size);
        } else if let (Some(low_pc), Some(high_pc)) = (low_pc, high_pc) {
            subroutine.size = Some(high_pc.wrapping_sub(low_pc));
        } else {
            debug!("unknown inlined_subroutine size");
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_inlined_subroutine => {
                    subroutine.inlined_subroutines
                        .push(try!(InlinedSubroutine::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_lexical_block => {
                    try!(parse_dwarf_lexical_block(&mut subroutine.inlined_subroutines,
                                                   dwarf,
                                                   unit,
                                                   child));
                }
                gimli::DW_TAG_formal_parameter => {}
                tag => {
                    debug!("unknown inlined_subroutine child tag: {}", tag);
                }
            }
        }
        Ok(subroutine)
    }

    fn print(&self, w: &mut Write, state: &PrintState, depth: usize) -> Result<()> {
        for _ in 0..depth + 1 {
            write!(w, "\t")?;
        }
        match self.size {
            Some(size) => write!(w, "[{}]", size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        match self.abstract_origin.and_then(|v| Subprogram::from_offset(state, v)) {
            Some(subprogram) => subprogram.print_name(w)?,
            None => write!(w, "<anon>")?,
        }
        writeln!(w, "")?;
        if state.flags.inline_depth > depth {
            for subroutine in self.inlined_subroutines.iter() {
                subroutine.print(w, state, depth + 1)?;
            }
        }
        Ok(())
    }
}

fn disassemble(
    machine: xmas_elf::header::Machine,
    region: &panopticon::Region,
    low_pc: u64,
    high_pc: u64
) -> Vec<u64> {
    match machine {
        xmas_elf::header::Machine::X86_64 => {
            disassemble_arch::<amd64::Amd64>(region, low_pc, high_pc, amd64::Mode::Long)
        }
        _ => Vec::new(),
    }
}

fn disassemble_arch<A>(
    region: &panopticon::Region,
    low_pc: u64,
    high_pc: u64,
    cfg: A::Configuration
) -> Vec<u64>
    where A: panopticon::Architecture + Debug,
          A::Configuration: Debug
{
    let mut calls = Vec::new();
    let mut mnemonics = BTreeMap::new();
    let mut jumps = vec![low_pc];
    while let Some(addr) = jumps.pop() {
        if mnemonics.contains_key(&addr) {
            continue;
        }

        let m = match A::decode(region, addr, &cfg) {
            Ok(m) => m,
            Err(e) => {
                error!("failed to disassemble: {}", e);
                return calls;
            }
        };

        for mnemonic in m.mnemonics {
            //writeln!(w, "\t{:?}", mnemonic);
            /*
            write!(w, "\t{}", mnemonic.opcode);
            let mut first = true;
            for operand in &mnemonic.operands {
                if first {
                    write!(w, "\t");
                    first = false;
                } else {
                    write!(w, ", ");
                }
                match *operand {
                    panopticon::Rvalue::Variable { ref name, .. } => write!(w, "{}", name),
                    panopticon::Rvalue::Constant { ref value, .. } => write!(w, "0x{:x}", value),
                    _ => write!(w, "?"),
                }
            }
            writeln!(w, "");
            */

            for instruction in mnemonic.instructions.iter() {
                match *instruction {
                    panopticon::Statement { op: panopticon::Operation::Call(ref call), .. } => {
                        match *call {
                            panopticon::Rvalue::Constant { ref value, .. } => {
                                calls.push(*value);
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
            // FIXME: mnemonic is large, insert boxed value
            mnemonics.insert(mnemonic.area.start, mnemonic);
        }

        for (_origin, target, _guard) in m.jumps {
            if let panopticon::Rvalue::Constant { value, size: _ } = target {
                if value > addr && value < high_pc {
                    jumps.push(value);
                }
            }
        }
    }
    calls
}

fn format_bit(val: u64) -> String {
    let byte = val / 8;
    let bit = val % 8;
    if bit == 0 {
        format!("{}", byte)
    } else {
        format!("{}.{}", byte, bit)
    }
}

#[derive(Debug)]
struct SimpleContext;

impl<'input> gimli::EvaluationContext<'input> for SimpleContext {
    type ContextError = Error;

    fn read_memory(&self, _addr: u64, _nbytes: u8, _space: Option<u64>) -> Result<u64> {
        Err("unsupported evalation read_memory callback".into())
    }
    fn read_register(&self, _regno: u64) -> Result<u64> {
        Err("unsupported evalation read_register callback".into())
    }
    fn frame_base(&self) -> Result<u64> {
        Err("unsupported evalation frame_base callback".into())
    }
    fn read_tls(&self, _slot: u64) -> Result<u64> {
        Err("unsupported evalation read_tls callback".into())
    }
    fn call_frame_cfa(&self) -> Result<u64> {
        Err("unsupported evalation call_frame_cfa callback".into())
    }
    fn get_at_location(&self, _die: gimli::DieReference) -> Result<&'input [u8]> {
        Err("unsupported evalation get_at_location callback".into())
    }
    fn evaluate_entry_value(&self, _expression: &[u8]) -> Result<u64> {
        Err("unsupported evalation evaluate_entry_value callback".into())
    }
}


fn evaluate<'input, Endian>(
    unit: &gimli::CompilationUnitHeader<Endian>,
    bytecode: &'input [u8]
) -> Result<gimli::Location<'input>>
    where Endian: gimli::Endianity
{
    let mut context = SimpleContext {};
    let mut evaluation = gimli::Evaluation::<Endian, SimpleContext>::new(bytecode,
                                                                         unit.address_size(),
                                                                         unit.format(),
                                                                         &mut context);
    evaluation.set_initial_value(0);
    let pieces = try!(evaluation.evaluate());
    if pieces.len() != 1 {
        return Err(format!("unsupported number of evaluation pieces: {}", pieces.len()).into());
    }
    Ok(pieces[0].location)
}
