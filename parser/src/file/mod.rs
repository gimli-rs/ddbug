use std::borrow::Cow;
use std::default::Default;
use std::fs;
use std::ops::Deref;

mod dwarf;

use fnv::FnvHashMap as HashMap;
use gimli;
use memmap;
use moria;
use object::{self, Object, ObjectSection, ObjectSegment};
use typed_arena::Arena;

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
    Dwarf(&'input dwarf::DwarfDebugInfo<'input, Endian>),
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

pub(crate) struct StringCache {
    strings: Arena<String>,
}

impl StringCache {
    fn new() -> Self {
        StringCache {
            strings: Arena::new(),
        }
    }

    fn get<'input>(&'input self, bytes: &'input [u8]) -> &'input str {
        // FIXME: this is effectively leaking strings that require lossy conversion,
        // fix by avoiding duplicates
        match String::from_utf8_lossy(bytes) {
            Cow::Borrowed(s) => s,
            Cow::Owned(s) => &*self.strings.alloc(s),
        }
    }
}

pub use object::target_lexicon::Architecture;

/// The parsed debuginfo for a single file.
pub struct File<'input> {
    pub(crate) path: &'input str,
    pub(crate) machine: Architecture,
    pub(crate) segments: Vec<Segment<'input>>,
    pub(crate) sections: Vec<Section<'input>>,
    pub(crate) symbols: Vec<Symbol<'input>>,
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
    ///
    /// `cb` is a callback function that is called with the parsed File.
    /// It requires a callback so that memory management is simplified.
    pub fn parse<Cb>(path: &str, cb: Cb) -> Result<()>
    where
        Cb: FnOnce(&File) -> Result<()>,
    {
        let handle = match fs::File::open(path) {
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

        let object = object::File::parse(&*map)?;

        if object.has_debug_symbols() {
            File::parse_object(&object, &object, path, cb)
        } else {
            let debug_path = match moria::locate_debug_symbols(&object, path) {
                Ok(debug_path) => debug_path,
                Err(e) => {
                    return Err(format!("unable to locate debug file: {}", e).into());
                }
            };

            let handle = match fs::File::open(debug_path) {
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

            let debug_object = object::File::parse(&*map)?;
            File::parse_object(&object, &debug_object, path, cb)
        }
        /*
        let input = &*map;
        if input.starts_with(b"Microsoft C/C++ MSF 7.00\r\n\x1a\x44\x53\x00") {
            pdb::parse(input, path, cb)
        } else {
            File::parse_object(input, path, cb)
        }
        */
    }

    fn parse_object<Cb>(
        object: &object::File,
        debug_object: &object::File,
        path: &str,
        cb: Cb,
    ) -> Result<()>
    where
        Cb: FnOnce(&File) -> Result<()>,
    {
        let machine = object.architecture();
        let mut segments = Vec::new();
        for segment in object.segments() {
            segments.push(Segment {
                address: segment.address(),
                bytes: segment.data(),
            });
        }

        let mut sections = Vec::new();
        for section in object.sections() {
            let name = section.name().map(|x| Cow::Owned(x.to_string()));
            let segment = section.segment_name().map(|x| Cow::Owned(x.to_string()));
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
        for (_, symbol) in object.symbols() {
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

            let name = symbol.name();

            symbols.push(Symbol {
                name,
                kind,
                address,
                size,
            });
        }

        let endian = if debug_object.is_little_endian() {
            gimli::RunTimeEndian::Little
        } else {
            gimli::RunTimeEndian::Big
        };

        let strings = &StringCache::new();
        dwarf::parse(endian, debug_object, strings, |units, debug_info| {
            let mut file = File {
                path,
                machine,
                segments,
                sections,
                symbols,
                units,
                debug_info,
            };
            file.normalize();
            cb(&file)
        })
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
    pub fn path(&self) -> &'input str {
        self.path
    }

    /// The machine type that the file contains debuginfo for.
    #[inline]
    pub fn machine(&self) -> Architecture {
        self.machine
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
