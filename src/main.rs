extern crate env_logger;
extern crate gimli;
#[macro_use]
extern crate log;
extern crate memmap;
extern crate xmas_elf;
extern crate panopticon;

use std::borrow::Borrow;
use std::borrow::Cow;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::cmp::Ordering;
use std::env;
use std::fmt;
use std::fmt::Debug;
use std::fs;
use std::ffi;
use std::error;
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

impl From<gimli::Error> for Error {
    fn from(e: gimli::Error) -> Error {
        Error(Cow::Owned(format!("DWARF error: {}", e)))
    }
}

pub type Result<T> = result::Result<T, Error>;

fn main() {
    env_logger::init().ok();

    for path in env::args_os().skip(1) {
        if let Err(e) = parse_file(&path) {
            error!("{}: {}", path.to_string_lossy(), e);
        }
    }
}

struct File {
    // TODO: use format independent machine type
    machine: xmas_elf::header::Machine,
    region: panopticon::Region,
}

fn parse_file(path: &ffi::OsStr) -> Result<()> {
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

    let file = File {
        machine: machine,
        region: region,
    };

    for unit in units {
        unit.print(&file);
    }
    Ok(())
}

struct DwarfFileState<'input, Endian>
    where Endian: gimli::Endianity
{
    debug_abbrev: gimli::DebugAbbrev<'input, Endian>,
    debug_info: gimli::DebugInfo<'input, Endian>,
    debug_str: gimli::DebugStr<'input, Endian>,
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

    let dwarf = DwarfFileState {
        debug_abbrev: debug_abbrev,
        debug_info: debug_info,
        debug_str: debug_str,
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
    abbrev: &'state gimli::Abbreviations,
    type_names: HashMap<usize, &'input ffi::CStr>,
    line: Option<gimli::DebugLineOffset>,
    ranges: Option<gimli::DebugRangesOffset>,
    namespaces: Vec<Option<&'input ffi::CStr>>,
}

#[derive(Debug, Default)]
struct Unit<'input> {
    dir: Option<&'input ffi::CStr>,
    name: Option<&'input ffi::CStr>,
    language: Option<gimli::DwLang>,
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
            abbrev: abbrev,
            type_names: HashMap::new(),
            line: None,
            ranges: None,
            namespaces: Vec::new(),
        };

        let mut tree = try!(unit_header.entries_tree(abbrev, None));
        let iter = tree.iter();

        let mut unit = Unit::default();
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
                gimli::DW_TAG_pointer_type |
                gimli::DW_TAG_array_type |
                gimli::DW_TAG_subroutine_type |
                gimli::DW_TAG_typedef |
                gimli::DW_TAG_const_type |
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

    fn print(&self, file: &File) {
        for type_ in self.types.iter() {
            type_.print(file);
        }
        for subprogram in self.subprograms.iter() {
            subprogram.print(file);
        }
    }
}

#[derive(Debug)]
struct Type<'input> {
    namespace: Vec<Option<&'input ffi::CStr>>,
    name: Option<&'input ffi::CStr>,
    tag: gimli::DwTag,
    parameters: Vec<Parameter<'input>>,
    return_type: Option<&'input ffi::CStr>,
    subprograms: Vec<Subprogram<'input>>,
}

impl<'input> Default for Type<'input> {
    fn default() -> Self {
        Type {
            namespace: Vec::new(),
            name: None,
            tag: gimli::DwTag(0),
            parameters: Vec::new(),
            return_type: None,
            subprograms: Vec::new(),
        }
    }
}

impl<'input> Type<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        mut iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
    ) -> Result<Type<'input>>
        where Endian: gimli::Endianity
    {
        let mut type_ = Type::default();
        type_.namespace = unit.namespaces.clone();

        {
            type_.tag = iter.entry().unwrap().tag();

            let mut attrs = iter.entry().unwrap().attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        type_.name = attr.string_value(&dwarf.debug_str);
                    }
                    gimli::DW_AT_type => {
                        if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                            if let Some(name) = try!(type_name(dwarf, unit, offset)) {
                                type_.return_type = Some(name);
                            } else {
                                debug!("invalid DW_AT_type offset {}", offset.0);
                            }
                        }
                    }
                    gimli::DW_AT_byte_size |
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line |
                    gimli::DW_AT_sibling |
                    gimli::DW_AT_declaration |
                    gimli::DW_AT_enum_class |
                    gimli::DW_AT_encoding |
                    gimli::DW_AT_prototyped => {}
                    _ => debug!("unknown type attribute: {} {:?}", attr.name(), attr.value()),
                }
            }
        }

        if let Some(name) = type_.name {
            unit.type_names.insert(iter.entry().unwrap().offset().0, name);
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_formal_parameter => {
                    type_.parameters.push(try!(Parameter::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_subprogram => {
                    type_.subprograms.push(try!(Subprogram::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_member |
                gimli::DW_TAG_enumerator |
                gimli::DW_TAG_subrange_type => {}
                tag => {
                    debug!("unknown type child tag: {}", tag);
                }
            }
        }
        Ok(type_)
    }

    fn print(&self, file: &File) {
        print!("{}: ", self.tag);
        for namespace in self.namespace.iter() {
            match *namespace {
                Some(ref name) => print!("{}::", name.to_string_lossy()),
                None => print!("<anon>"),
            }
        }
        match self.name {
            Some(name) => print!("{}", name.to_string_lossy()),
            None => print!("<anon>"),
        }
        if let Some(return_type) = self.return_type {
            print!(" -> {}", return_type.to_string_lossy());
        }
        println!("");

        for parameter in self.parameters.iter() {
            print!("\t");
            parameter.print();
            println!("");
        }

        for subprogram in self.subprograms.iter() {
            subprogram.print(file);
        }
    }
}

#[derive(Debug)]
struct Subprogram<'input> {
    namespace: Vec<Option<&'input ffi::CStr>>,
    name: Option<&'input ffi::CStr>,
    low_pc: Option<u64>,
    high_pc: Option<u64>,
    size: Option<u64>,
    inline: bool,
    parameters: Vec<Parameter<'input>>,
    return_type: Option<&'input ffi::CStr>,
}

impl<'input> Default for Subprogram<'input> {
    fn default() -> Self {
        Subprogram {
            namespace: Vec::new(),
            name: None,
            low_pc: None,
            high_pc: None,
            size: None,
            inline: false,
            parameters: Vec::new(),
            return_type: None,
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
        subprogram.namespace = unit.namespaces.clone();

        {
            let entry = iter.entry().unwrap();
            let mut attrs = entry.attrs();
            while let Some(attr) = try!(attrs.next()) {
                match attr.name() {
                    gimli::DW_AT_name => {
                        subprogram.name = attr.string_value(&dwarf.debug_str);
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
                            if let Some(name) = try!(type_name(dwarf, unit, offset)) {
                                subprogram.return_type = Some(name);
                            } else {
                                debug!("invalid DW_AT_type offset {}", offset.0);
                            }
                        }
                    }
                    gimli::DW_AT_linkage_name |
                    gimli::DW_AT_decl_file |
                    gimli::DW_AT_decl_line |
                    gimli::DW_AT_frame_base |
                    gimli::DW_AT_external |
                    gimli::DW_AT_abstract_origin |
                    gimli::DW_AT_GNU_all_call_sites |
                    gimli::DW_AT_GNU_all_tail_call_sites |
                    gimli::DW_AT_prototyped |
                    gimli::DW_AT_declaration |
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
                    subprogram.size = Some(high_pc - low_pc);
                } else if let Some(size) = subprogram.size {
                    subprogram.high_pc = Some(low_pc + size);
                }
            }
        }

        while let Some(child) = try!(iter.next()) {
            match child.entry().unwrap().tag() {
                gimli::DW_TAG_formal_parameter => {
                    subprogram.parameters.push(try!(Parameter::parse_dwarf(dwarf, unit, child)));
                }
                gimli::DW_TAG_template_type_parameter |
                gimli::DW_TAG_lexical_block |
                gimli::DW_TAG_inlined_subroutine |
                gimli::DW_TAG_variable |
                gimli::DW_TAG_label |
                gimli::DW_TAG_union_type |
                gimli::DW_TAG_GNU_call_site => {}
                tag => {
                    debug!("unknown subprogram child tag: {}", tag);
                }
            }
        }

        Ok(subprogram)
    }

    fn print(&self, file: &File) {
        print!("fn ");
        for namespace in self.namespace.iter() {
            match *namespace {
                Some(ref name) => print!("{}::", name.to_string_lossy()),
                None => print!("<anon>"),
            }
        }
        match self.name {
            Some(name) => print!("{}", name.to_string_lossy()),
            None => print!("<anon>"),
        }

        let mut first = true;
        print!("(");
        for parameter in self.parameters.iter() {
            if first {
                first = false;
            } else {
                print!(", ");
            }
            parameter.print();
        }
        print!(")");

        if let Some(return_type) = self.return_type {
            print!(" -> {}", return_type.to_string_lossy());
        }

        println!("");

        if let Some(size) = self.size {
            println!("\tsize: {}", size);
        }

        if self.inline {
            println!("\tinline: yes");
        } else {
            println!("\tinline: no");
        }

        if let (Some(low_pc), Some(high_pc)) = (self.low_pc, self.high_pc) {
            if low_pc != 0 {
                // TODO: is high_pc inclusive?
                println!("\taddress: 0x{:x}-0x{:x}", low_pc, high_pc - 1);
                disassemble(file.machine, &file.region, low_pc, high_pc);
            }
        }
    }
}

#[derive(Debug, Default)]
struct Parameter<'input> {
    name: Option<&'input ffi::CStr>,
    type_: Option<&'input ffi::CStr>,
}

impl<'input> Parameter<'input> {
    fn parse_dwarf<'state, 'abbrev, 'unit, 'tree, Endian>(
        dwarf: &DwarfFileState<'input, Endian>,
        unit: &mut DwarfUnitState<'state, 'input, Endian>,
        iter: gimli::EntriesTreeIter<'input, 'abbrev, 'unit, 'tree, Endian>
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
                            if let Some(name) = try!(type_name(dwarf, unit, offset)) {
                                parameter.type_ = Some(name);
                            } else {
                                debug!("invalid DW_AT_type offset {}", offset.0);
                            }
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
        Ok(parameter)
    }

    fn print(&self) {
        match self.name {
            Some(name) => print!("{}", name.to_string_lossy()),
            None => print!("<anon>"),
        }
        match self.type_ {
            Some(name) => print!(": {}", name.to_string_lossy()),
            None => print!(": <anon>"),
        }
    }
}

fn type_name<'state, 'input, 'abbrev, 'unit, 'tree, Endian>(
    dwarf: &DwarfFileState<'input, Endian>,
    unit: &mut DwarfUnitState<'state, 'input, Endian>,
    offset: gimli::UnitOffset
) -> Result<Option<&'input ffi::CStr>>
    where Endian: gimli::Endianity
{
    if let Some(name) = unit.type_names.get(&offset.0) {
        return Ok(Some(name));
    }

    let mut tree = try!(unit.header.entries_tree(unit.abbrev, Some(offset)));
    let iter = tree.iter();
    let mut attrs = iter.entry().unwrap().attrs();
    while let Some(attr) = try!(attrs.next()) {
        match attr.name() {
            gimli::DW_AT_name => {
                match attr.string_value(&dwarf.debug_str) {
                    Some(name) => {
                        unit.type_names.insert(offset.0, name);
                        return Ok(Some(name));
                    }
                    None => return Ok(None),
                }
            }
            _ => {}
        }
    }
    Ok(None)
}

fn disassemble(
    machine: xmas_elf::header::Machine,
    region: &panopticon::Region,
    low_pc: u64,
    high_pc: u64
) {
    match machine {
        xmas_elf::header::Machine::X86_64 => {
            disassemble_arch::<amd64::Amd64>(region, low_pc, high_pc, amd64::Mode::Long);
        }
        _ => {}
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Jump(u64);

impl Ord for Jump {
    fn cmp(&self, other: &Jump) -> Ordering {
        other.0.cmp(&self.0)
    }
}

impl PartialOrd for Jump {
    fn partial_cmp(&self, other: &Jump) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn disassemble_arch<A>(
    region: &panopticon::Region,
    low_pc: u64,
    high_pc: u64,
    cfg: A::Configuration
)
    where A: panopticon::Architecture + Debug,
          A::Configuration: Debug
{
    let mut calls = Vec::new();
    // FIXME: stop using BinaryHeap; we need to be able to go backwards sometimes
    let mut jumps = BinaryHeap::new();
    let mut addr = low_pc;
    loop {
        let m = match A::decode(region, addr, &cfg) {
            Ok(m) => m,
            Err(e) => {
                error!("failed to disassemble: {}", e);
                return;
            }
        };

        for mnemonic in m.mnemonics {
            //println!("\t{:?}", mnemonic);
            /*
            print!("\t{}", mnemonic.opcode);
            let mut first = true;
            for operand in &mnemonic.operands {
                if first {
                    print!("\t");
                    first = false;
                } else {
                    print!(", ");
                }
                match *operand {
                    panopticon::Rvalue::Variable { ref name, .. } => print!("{}", name),
                    panopticon::Rvalue::Constant { ref value, .. } => print!("0x{:x}", value),
                    _ => print!("?"),
                }
            }
            println!("");
            */

            for instruction in mnemonic.instructions {
                match instruction {
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
        }

        for (_origin, target, _guard) in m.jumps {
            if let panopticon::Rvalue::Constant { value, size: _ } = target {
                jumps.push(Jump(value));
                // if value < low_pc || value >= high_pc {
                // calls.push(value);
                // }
                // if value > addr && value < next_addr {
                // next_addr = value;
                // }
                //
            }
        }

        while let Some(&Jump(jump)) = jumps.peek() {
            if jump > addr && jump <= high_pc {
                break;
            }
            jumps.pop();
        }
        addr = match jumps.pop() {
            Some(Jump(addr)) => addr,
            None => break,
        }
    }

    if !calls.is_empty() {
        print!("\tcalls: 0x{:x}", calls[0]);
        for call in &calls[1..] {
            print!(", 0x{:x}", call);
        }
        println!("");
    }
}
