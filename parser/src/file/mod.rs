use std::borrow::Cow;
use std::default::Default;
use std::fs;
use std::mem;
use std::ops::Deref;
use std::sync::Mutex;

mod dwarf;

use fnv::FnvHashMap as HashMap;
use gimli;
use memmap;
use object::{self, Object, ObjectSection, ObjectSegment, ObjectSymbol, ObjectSymbolTable};

use crate::cfi::Cfi;
use crate::function::{Function, FunctionDetails, FunctionOffset};
use crate::location::Register;
use crate::range::{Range, RangeList};
use crate::types::{Enumerator, Type, TypeOffset};
use crate::unit::Unit;
use crate::variable::Variable;
use crate::{Address, Result, Size};

pub(crate) enum DebugInfo<'input, Endian>
where
    Endian: gimli::Endianity + 'input,
{
    Dwarf(dwarf::DwarfDebugInfo<'input, Endian>),
}

impl<'input, Endian> DebugInfo<'input, Endian>
where
    Endian: gimli::Endianity + 'input,
{
    fn get_type(&self, offset: TypeOffset) -> Option<Type<'input>> {
        match self {
            DebugInfo::Dwarf(dwarf) => dwarf.get_type(offset),
        }
    }

    fn get_enumerators(&self, offset: TypeOffset) -> Vec<Enumerator<'input>> {
        match self {
            DebugInfo::Dwarf(dwarf) => dwarf.get_enumerators(offset),
        }
    }

    fn get_function_details(
        &self,
        offset: FunctionOffset,
        hash: &FileHash<'input>,
    ) -> Option<FunctionDetails<'input>> {
        match self {
            DebugInfo::Dwarf(dwarf) => dwarf.get_function_details(offset, hash),
        }
    }

    fn get_cfi(&self, address: Address, size: Size) -> Vec<Cfi> {
        match self {
            DebugInfo::Dwarf(dwarf) => dwarf.get_cfi(address, size),
        }
    }

    fn get_register_name(&self, machine: Architecture, register: Register) -> Option<&'static str> {
        match self {
            DebugInfo::Dwarf(dwarf) => dwarf.get_register_name(machine, register),
        }
    }
}

pub(crate) struct Arena {
    // TODO: can these be a single `Vec<Box<dyn ??>>`?
    buffers: Mutex<Vec<Vec<u8>>>,
    strings: Mutex<Vec<String>>,
    relocations: Mutex<Vec<Box<dwarf::RelocationMap>>>,
}

impl Arena {
    fn new() -> Self {
        Arena {
            buffers: Mutex::new(Vec::new()),
            strings: Mutex::new(Vec::new()),
            relocations: Mutex::new(Vec::new()),
        }
    }

    fn add_buffer<'input>(&'input self, bytes: Vec<u8>) -> &'input [u8] {
        let mut buffers = self.buffers.lock().unwrap();
        let i = buffers.len();
        buffers.push(bytes);
        let b = &buffers[i];
        unsafe { mem::transmute::<&[u8], &'input [u8]>(b) }
    }

    fn add_string<'input>(&'input self, bytes: &'input [u8]) -> &'input str {
        // FIXME: this is effectively leaking strings that require lossy conversion,
        // fix by avoiding duplicates
        match String::from_utf8_lossy(bytes) {
            Cow::Borrowed(s) => s,
            Cow::Owned(s) => {
                let mut strings = self.strings.lock().unwrap();
                let i = strings.len();
                strings.push(s);
                let s = &strings[i];
                unsafe { mem::transmute::<&str, &'input str>(s) }
            }
        }
    }

    fn add_relocations<'input>(
        &'input self,
        entry: Box<dwarf::RelocationMap>,
    ) -> &'input dwarf::RelocationMap {
        let mut relocations = self.relocations.lock().unwrap();
        let i = relocations.len();
        relocations.push(entry);
        let entry = &relocations[i];
        unsafe { mem::transmute::<&dwarf::RelocationMap, &'input dwarf::RelocationMap>(entry) }
    }
}

pub use object::Architecture;

/// The context needed for a parsed file.
///
/// The parsed file references the context, so it is included here as well.
pub struct FileContext {
    // Self-referential, not actually `static.
    file: File<'static>,
    _map: memmap::Mmap,
    _arena: Box<Arena>,
}

impl FileContext {
    fn new<F>(map: memmap::Mmap, f: F) -> Result<FileContext>
    where
        F: for<'a> FnOnce(&'a [u8], &'a Arena) -> Result<File<'a>>,
    {
        let arena = Box::new(Arena::new());
        let file = f(&map, &arena)?;
        Ok(FileContext {
            // `file` only borrows from `map` and `arena`, which we are preserving
            // without moving.
            file: unsafe { mem::transmute::<File<'_>, File<'static>>(file) },
            _map: map,
            _arena: arena,
        })
    }

    /// Return the parsed debuginfo for the file.
    pub fn file<'a>(&'a self) -> &'a File<'a> {
        unsafe { mem::transmute::<&'a File<'static>, &'a File<'a>>(&self.file) }
    }
}

/// The parsed debuginfo for a single file.
pub struct File<'input> {
    pub(crate) path: String,
    pub(crate) machine: Architecture,
    pub(crate) segments: Vec<Segment<'input>>,
    pub(crate) sections: Vec<Section<'input>>,
    pub(crate) symbols: Vec<Symbol<'input>>,
    pub(crate) relocations: Vec<Relocation<'input>>,
    pub(crate) units: Vec<Unit<'input>>,
    debug_info: DebugInfo<'input, gimli::RunTimeEndian>,
}

impl<'input> File<'input> {
    pub(crate) fn get_type(&self, offset: TypeOffset) -> Option<Type<'input>> {
        self.debug_info.get_type(offset)
    }

    pub(crate) fn get_enumerators(&self, offset: TypeOffset) -> Vec<Enumerator<'input>> {
        self.debug_info.get_enumerators(offset)
    }

    pub(crate) fn get_function_details(
        &self,
        offset: FunctionOffset,
        hash: &FileHash<'input>,
    ) -> FunctionDetails<'input> {
        self.debug_info
            .get_function_details(offset, hash)
            .unwrap_or_default()
    }

    pub(crate) fn get_cfi(&self, address: Address, size: Size) -> Vec<Cfi> {
        self.debug_info.get_cfi(address, size)
    }

    pub(crate) fn get_register_name(&self, register: Register) -> Option<&'static str> {
        self.debug_info.get_register_name(self.machine, register)
    }

    /// Parse the file with the given path.
    pub fn parse(path: String) -> Result<FileContext> {
        let handle = match fs::File::open(&path) {
            Ok(handle) => handle,
            Err(e) => {
                return Err(format!("open failed: {}", e).into());
            }
        };

        let map = match unsafe { memmap::Mmap::map(&handle) } {
            Ok(map) => map,
            Err(e) => {
                return Err(format!("memmap failed: {}", e).into());
            }
        };

        // TODO: split DWARF
        // TODO: PDB
        FileContext::new(map, |data, strings| {
            let object = object::File::parse(data)?;
            File::parse_object(&object, &object, path, strings)
        })
    }

    fn parse_object(
        object: &object::File<'input>,
        debug_object: &object::File<'input>,
        path: String,
        arena: &'input Arena,
    ) -> Result<File<'input>> {
        let machine = object.architecture();
        let mut segments = Vec::new();
        for segment in object.segments() {
            if let Ok(bytes) = segment.data() {
                segments.push(Segment {
                    address: segment.address(),
                    bytes,
                });
            }
        }

        let mut sections = Vec::new();
        for section in object.sections() {
            let name = Some(section.name()?).map(|x| Cow::Owned(x.to_string()));
            let segment = section.segment_name()?.map(|x| Cow::Owned(x.to_string()));
            let address = if section.address() != 0 {
                Some(section.address())
            } else {
                None
            };
            let size = section.size();
            if size != 0 {
                sections.push(Section {
                    name,
                    segment,
                    address,
                    size,
                });
            }
        }

        // TODO: symbols from debug_object too?
        let mut symbols = Vec::new();
        for symbol in object.symbols() {
            // TODO: handle relocatable objects
            let address = symbol.address();
            if address == 0 {
                continue;
            }

            let size = symbol.size();
            if size == 0 {
                continue;
            }

            // TODO: handle SymbolKind::File
            let kind = match symbol.kind() {
                object::SymbolKind::Text => SymbolKind::Function,
                object::SymbolKind::Data | object::SymbolKind::Unknown => SymbolKind::Variable,
                _ => continue,
            };

            let name = Some(symbol.name()?);

            symbols.push(Symbol {
                name,
                kind,
                address,
                size,
            });
        }

        let mut relocations = Vec::new();
        if let (Some(dynamic_symbols), Some(dynamic_relocations)) =
            (object.dynamic_symbol_table(), object.dynamic_relocations())
        {
            for (address, relocation) in dynamic_relocations {
                let size = relocation.size();
                match relocation.target() {
                    object::RelocationTarget::Symbol(index) => {
                        if let Ok(symbol) = dynamic_symbols.symbol_by_index(index) {
                            relocations.push(Relocation {
                                address,
                                size,
                                symbol: symbol.name()?,
                            });
                        }
                    }
                    _ => {}
                }
            }
        }

        let endian = if debug_object.is_little_endian() {
            gimli::RunTimeEndian::Little
        } else {
            gimli::RunTimeEndian::Big
        };

        let (units, debug_info) = dwarf::parse(endian, debug_object, arena)?;
        let mut file = File {
            path,
            machine,
            segments,
            sections,
            symbols,
            relocations,
            units,
            debug_info,
        };
        file.normalize();
        Ok(file)
    }

    fn normalize(&mut self) {
        self.symbols.sort_by(|a, b| a.address.cmp(&b.address));
        let mut used_symbols = vec![false; self.symbols.len()];

        // Set symbol names on functions/variables.
        for unit in &mut self.units {
            for function in &mut unit.functions {
                if let Some(address) = function.address() {
                    if let Some(symbol) = Self::get_symbol(
                        &*self.symbols,
                        &mut used_symbols,
                        address,
                        function.linkage_name().or_else(|| function.name()),
                    ) {
                        function.symbol_name = symbol.name;
                    }
                }
            }

            for variable in &mut unit.variables {
                if let Some(address) = variable.address() {
                    if let Some(symbol) = Self::get_symbol(
                        &*self.symbols,
                        &mut used_symbols,
                        address,
                        variable.linkage_name().or_else(|| variable.name()),
                    ) {
                        variable.symbol_name = symbol.name;
                    }
                }
            }
        }

        // Create a unit for symbols that don't have debuginfo.
        let mut unit = Unit::default();
        unit.name = Some(Cow::Borrowed("<symtab>"));
        for (symbol, used) in self.symbols.iter().zip(used_symbols.iter()) {
            if *used {
                continue;
            }
            unit.ranges.push(Range {
                begin: symbol.address,
                end: symbol.address + symbol.size,
            });
            match symbol.kind() {
                SymbolKind::Variable => {
                    unit.variables.push(Variable {
                        name: symbol.name,
                        linkage_name: symbol.name,
                        address: Address::new(symbol.address),
                        size: Size::new(symbol.size),
                        ..Default::default()
                    });
                }
                SymbolKind::Function => {
                    unit.functions.push(Function {
                        name: symbol.name,
                        linkage_name: symbol.name,
                        address: Address::new(symbol.address),
                        size: Size::new(symbol.size),
                        ..Default::default()
                    });
                }
            }
        }
        unit.ranges.sort();
        self.units.push(unit);

        // Create a unit for all remaining address ranges.
        let mut unit = Unit::default();
        unit.name = Some(Cow::Borrowed("<unknown>"));
        unit.ranges = self.unknown_ranges();
        self.units.push(unit);
    }

    // Determine if the symbol at the given address has the given name.
    // There may be multiple symbols for the same address.
    // If none match the given name, then return the first one.
    fn get_symbol<'sym>(
        symbols: &'sym [Symbol<'input>],
        used_symbols: &mut [bool],
        address: u64,
        name: Option<&str>,
    ) -> Option<&'sym Symbol<'input>> {
        if let Ok(mut index) = symbols.binary_search_by(|x| x.address.cmp(&address)) {
            while index > 0 && symbols[index - 1].address == address {
                index -= 1;
            }
            let mut found = false;
            for (symbol, used_symbol) in (&symbols[index..])
                .iter()
                .zip((&mut used_symbols[index..]).iter_mut())
            {
                if symbol.address != address {
                    break;
                }
                *used_symbol = true;
                if symbol.name() == name {
                    found = true;
                }
            }
            if found {
                None
            } else {
                Some(&symbols[index])
            }
        } else {
            None
        }
    }

    /// The file path.
    #[inline]
    pub fn path(&self) -> &str {
        &self.path
    }

    /// The machine type that the file contains debuginfo for.
    #[inline]
    pub fn machine(&self) -> Architecture {
        self.machine
    }

    /// Find the segment data for the given address range.
    pub fn segment_bytes(&self, range: Range) -> Option<&'input [u8]> {
        for segment in &self.segments {
            if range.begin >= segment.address
                && range.end <= segment.address + segment.bytes.len() as u64
            {
                let begin = (range.begin - segment.address) as usize;
                let len = (range.end - range.begin) as usize;
                return Some(&segment.bytes[begin..][..len]);
            }
        }
        None
    }

    /// A list of segments in the file.
    #[inline]
    pub fn segments(&self) -> &[Segment<'input>] {
        &self.segments
    }

    /// A list of sections in the file.
    #[inline]
    pub fn sections(&self) -> &[Section<'input>] {
        &self.sections
    }

    /// A list of symbols in the file.
    #[inline]
    pub fn symbols(&self) -> &[Symbol<'input>] {
        &self.symbols
    }

    /// A list of relocations in the file.
    #[inline]
    pub fn relocations(&self) -> &[Relocation<'input>] {
        &self.relocations
    }

    /// A list of compilation units in the file.
    #[inline]
    pub fn units(&self) -> &[Unit<'input>] {
        &self.units
    }

    /// A list of address ranges covered by the compilation units.
    ///
    /// This includes both `Unit::ranges` and `Unit::unknown_ranges`.
    pub fn ranges(&self, hash: &FileHash) -> RangeList {
        let mut ranges = RangeList::default();
        for unit in &self.units {
            for range in unit.ranges(hash).list() {
                ranges.push(*range);
            }
            for range in unit.unknown_ranges(hash).list() {
                ranges.push(*range);
            }
        }
        ranges.sort();
        ranges
    }

    // Used to create <unknown> unit. After creation of that unit
    // this will return an empty range list.
    fn unknown_ranges(&self) -> RangeList {
        // FIXME: don't create this hash twice
        let hash = FileHash::new(self);
        let unit_ranges = self.ranges(&hash);

        let mut ranges = RangeList::default();
        for section in &self.sections {
            if let Some(range) = section.address() {
                ranges.push(range);
            }
        }
        ranges.sort();
        ranges.subtract(&unit_ranges)
    }

    /// The total size of functions in all compilation units.
    pub fn function_size(&self) -> u64 {
        let mut size = 0;
        for unit in &self.units {
            size += unit.function_size();
        }
        size
    }

    /// The total size of variables in all compilation units.
    pub fn variable_size(&self, hash: &FileHash) -> u64 {
        let mut size = 0;
        for unit in &self.units {
            size += unit.variable_size(hash);
        }
        size
    }
}

/// An index of functions and types within a file.
pub struct FileHash<'input> {
    /// The file being indexed.
    pub file: &'input File<'input>,
    /// All functions by address.
    pub functions_by_address: HashMap<u64, &'input Function<'input>>,
    /// All functions by offset.
    pub functions_by_offset: HashMap<FunctionOffset, &'input Function<'input>>,
    /// All types by offset.
    pub types: HashMap<TypeOffset, &'input Type<'input>>,
    // The type corresponding to `TypeOffset::none()`.
    pub(crate) void: Type<'input>,
}

impl<'input> FileHash<'input> {
    /// Create a new `FileHash` for the given `File`.
    pub fn new(file: &'input File<'input>) -> Self {
        FileHash {
            file,
            functions_by_address: FileHash::functions_by_address(file),
            functions_by_offset: FileHash::functions_by_offset(file),
            types: FileHash::types(file),
            void: Type::void(),
        }
    }

    /// Returns a map from address to function for all functions in the file.
    fn functions_by_address<'a>(file: &'a File<'input>) -> HashMap<u64, &'a Function<'input>> {
        let mut functions = HashMap::default();
        for unit in &file.units {
            for function in &unit.functions {
                if let Some(address) = function.address() {
                    // TODO: handle duplicate addresses
                    functions.insert(address, function);
                }
            }
        }
        functions
    }

    /// Returns a map from offset to function for all functions in the file.
    fn functions_by_offset<'a>(
        file: &'a File<'input>,
    ) -> HashMap<FunctionOffset, &'a Function<'input>> {
        let mut functions = HashMap::default();
        for unit in &file.units {
            for function in &unit.functions {
                functions.insert(function.offset, function);
            }
        }
        functions
    }

    /// Returns a map from offset to type for all types in the file.
    fn types<'a>(file: &'a File<'input>) -> HashMap<TypeOffset, &'a Type<'input>> {
        let mut types = HashMap::default();
        for unit in &file.units {
            for ty in &unit.types {
                types.insert(ty.offset, ty);
            }
        }
        types
    }
}

/// A loadable range of bytes.
#[derive(Debug)]
pub struct Segment<'input> {
    /// The address that the bytes should be loaded at.
    pub address: u64,
    /// The bytes, which may be code or data.
    pub bytes: &'input [u8],
}

/// A named section.
#[derive(Debug)]
pub struct Section<'input> {
    pub(crate) name: Option<Cow<'input, str>>,
    pub(crate) segment: Option<Cow<'input, str>>,
    pub(crate) address: Option<u64>,
    pub(crate) size: u64,
}

impl<'input> Section<'input> {
    /// The name of this section.
    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(Cow::deref)
    }

    /// The name of the segment containing this section, if applicable.
    pub fn segment(&self) -> Option<&str> {
        self.segment.as_ref().map(Cow::deref)
    }

    /// The address range covered by this section if it is loadable.
    pub fn address(&self) -> Option<Range> {
        self.address.map(|address| Range {
            begin: address,
            end: address + self.size,
        })
    }

    /// The size of the section.
    #[inline]
    pub fn size(&self) -> u64 {
        self.size
    }
}

/// A symbol kind.
#[derive(Debug, Clone, Copy)]
pub enum SymbolKind {
    /// The symbol is a variable.
    Variable,
    /// The symbol is a function.
    Function,
}

/// A symbol.
#[derive(Debug, Clone)]
pub struct Symbol<'input> {
    pub(crate) name: Option<&'input str>,
    pub(crate) kind: SymbolKind,
    pub(crate) address: u64,
    pub(crate) size: u64,
}

impl<'input> Symbol<'input> {
    /// The symbol name.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The symbol kind.
    #[inline]
    pub fn kind(&self) -> SymbolKind {
        self.kind
    }

    /// The symbol address range.
    #[inline]
    pub fn address(&self) -> Range {
        Range {
            begin: self.address,
            end: self.address + self.size,
        }
    }

    /// The symbol size range.
    #[inline]
    pub fn size(&self) -> u64 {
        self.size
    }
}

/// A relocation.
#[derive(Debug, Clone)]
pub struct Relocation<'input> {
    pub(crate) address: u64,
    pub(crate) size: u8,
    pub(crate) symbol: &'input str,
}

impl<'input> Relocation<'input> {
    /// The relocation address.
    #[inline]
    pub fn address(&self) -> u64 {
        self.address
    }

    /// The relocation size.
    #[inline]
    pub fn size(&self) -> u8 {
        self.size
    }

    /// The name of the symbol referenced by the relocation.
    #[inline]
    pub fn symbol(&self) -> &'input str {
        self.symbol
    }
}
