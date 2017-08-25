extern crate gimli;
#[macro_use]
extern crate log;
extern crate memmap;
extern crate goblin;
extern crate panopticon_core as panopticon;
extern crate panopticon_amd64 as amd64;
extern crate pdb as crate_pdb;

mod diff;
mod diffstate;
mod dwarf;
mod elf;
mod mach;
mod pdb;
mod range;
mod types;

use std::borrow::Borrow;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp;
use std::error;
use std::fmt::{self, Debug};
use std::fs;
use std::io;
use std::io::Write;
use std::result;
use std::rc::Rc;

use diffstate::{DiffList, DiffState, PrintList, PrintState};
use range::RangeList;
use types::{Type, TypeKind, TypeOffset};

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

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error(Cow::Owned(format!("IO error: {}", e)))
    }
}

impl From<gimli::Error> for Error {
    fn from(e: gimli::Error) -> Error {
        Error(Cow::Owned(format!("DWARF error: {}", e)))
    }
}

impl From<crate_pdb::Error> for Error {
    fn from(e: crate_pdb::Error) -> Error {
        Error(Cow::Owned(format!("PDB error: {}", e)))
    }
}

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort {
    None,
    Name,
    Size,
}

impl Sort {
    fn with_diff(self, diff: bool) -> Self {
        if diff {
            Sort::Name
        } else {
            self
        }
    }
}

impl Default for Sort {
    fn default() -> Self {
        Sort::None
    }
}

#[derive(Debug, Default, Clone)]
pub struct Options<'a> {
    pub calls: bool,
    pub inline_depth: usize,

    pub category_file: bool,
    pub category_unit: bool,
    pub category_type: bool,
    pub category_function: bool,
    pub category_variable: bool,

    pub filter_function_inline: Option<bool>,
    pub filter_name: Option<&'a str>,
    pub filter_namespace: Vec<&'a str>,
    pub filter_unit: Option<&'a str>,

    pub sort: Sort,

    pub ignore_added: bool,
    pub ignore_deleted: bool,
    pub ignore_function_address: bool,
    pub ignore_function_size: bool,
    pub ignore_function_inline: bool,
    pub ignore_variable_address: bool,
    pub prefix_map: Vec<(&'a str, &'a str)>,
}

impl<'a> Options<'a> {
    pub fn unit(&mut self, unit: &'a str) -> &mut Self {
        self.filter_unit = Some(unit);
        self
    }

    pub fn name(&mut self, name: &'a str) -> &mut Self {
        self.filter_name = Some(name);
        self
    }

    fn filter_function_inline(&self, inline: bool) -> bool {
        self.filter_function_inline.is_none() || self.filter_function_inline == Some(inline)
    }

    fn filter_name(&self, name: Option<&[u8]>) -> bool {
        if let Some(filter) = self.filter_name {
            filter_name(name, filter)
        } else {
            true
        }
    }

    fn filter_namespace(&self, namespace: &Option<Rc<Namespace>>) -> bool {
        if !self.filter_namespace.is_empty() {
            match *namespace {
                Some(ref namespace) => namespace.filter(&self.filter_namespace),
                None => false,
            }
        } else {
            true
        }
    }
}

fn filter_name(name: Option<&[u8]>, filter: &str) -> bool {
    match name {
        Some(name) => name == filter.as_bytes(),
        None => false,
    }
}

fn filter_option<T, F>(o: Option<T>, f: F) -> Option<T>
where
    T: Copy,
    F: FnOnce(T) -> bool,
{
    o.and_then(|v| if f(v) { Some(v) } else { None })
}

#[derive(Debug)]
pub struct CodeRegion {
    // TODO: use format independent machine type
    machine: u16,
    region: panopticon::Region,
}

#[derive(Debug)]
pub struct File<'a, 'input> {
    path: &'a str,
    code: Option<CodeRegion>,
    units: Vec<Unit<'input>>,
}

impl<'a, 'input> File<'a, 'input> {
    pub fn parse(path: &'a str, cb: &mut FnMut(&mut File) -> Result<()>) -> Result<()> {
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
        if input.starts_with(b"Microsoft C/C++ MSF 7.00\r\n\x1a\x44\x53\x00") {
            pdb::parse(input, path, cb)
        } else {
            let mut cursor = io::Cursor::new(input);
            match goblin::peek(&mut cursor) {
                Ok(goblin::Hint::Elf(_)) => elf::parse(input, path, cb),
                Ok(goblin::Hint::Mach(_)) => mach::parse(input, path, cb),
                Ok(_) => Err("unrecognized file format".into()),
                Err(e) => Err(format!("file identification failed: {}", e).into()),
            }
        }
    }

    pub fn print(&self, w: &mut Write, options: &Options) -> Result<()> {
        let hash = FileHash::new(self);
        let mut state = PrintState::new(self, &hash, options);

        if options.category_file {
            state.line(w, |w, _state| {
                write!(w, "file {}", self.path)?;
                Ok(())
            })?;

            // TODO: display ranges/size that aren't covered by debuginfo.
            let ranges = self.ranges();
            state.list("addresses", w, &(), ranges.list())?;
            state.line_option_u64(w, "size", ranges.size())?;
            writeln!(w, "")?;
        }

        for unit in self.filter_units(options, false) {
            unit.print(w, &mut state, options)?;
        }
        Ok(())
    }

    pub fn diff(w: &mut Write, file_a: &File, file_b: &File, options: &Options) -> Result<()> {
        let hash_a = FileHash::new(file_a);
        let hash_b = FileHash::new(file_b);
        let mut state = DiffState::new(file_a, &hash_a, file_b, &hash_b, options);

        if options.category_file {
            state.line(w, file_a, file_b, |w, _state, x| {
                write!(w, "file {}", x.path)?;
                Ok(())
            })?;
            let ranges_a = file_a.ranges();
            let ranges_b = file_b.ranges();
            state.list("addresses", w, &(), ranges_a.list(), &(), ranges_b.list())?;
            state.line_option_u64(w, "size", ranges_a.size(), ranges_b.size())?;
            writeln!(w, "")?;
        }

        state
            .merge(
                w,
                |_state| file_a.filter_units(options, true),
                |_state| file_b.filter_units(options, true),
                |_hash_a, a, _hash_b, b| Unit::cmp_id(a, b, options),
                |w, state, a, b| {
                    Unit::diff(a, b, w, state, options)
                },
                |w, state, a| {
                    if !options.ignore_deleted {
                        a.print(w, state, options)?;
                    }
                    Ok(())
                },
                |w, state, b| {
                    if !options.ignore_added {
                        b.print(w, state, options)?;
                    }
                    Ok(())
                },
            )?;
        Ok(())
    }

    fn filter_units(&self, options: &Options, diff: bool) -> Vec<&Unit> {
        let mut units: Vec<_> = self.units.iter().filter(|a| a.filter(options)).collect();
        match options.sort.with_diff(diff) {
            Sort::None => {}
            Sort::Name => units.sort_by(|a, b| Unit::cmp_id(a, b, options)),
            Sort::Size => units.sort_by(|a, b| Unit::cmp_size(a, b)),
        }
        units
    }

    fn ranges(&self) -> RangeList {
        let mut ranges = RangeList::default();
        for unit in &self.units {
            for range in unit.ranges.list() {
                ranges.push(*range);
            }
        }
        ranges.sort();
        ranges
    }
}

#[derive(Debug)]
struct FileHash<'a, 'input>
where
    'input: 'a,
{
    // All functions by address.
    functions: HashMap<u64, &'a Function<'input>>,
    // All types by offset.
    types: HashMap<TypeOffset, &'a Type<'input>>,
}

impl<'a, 'input> FileHash<'a, 'input> {
    fn new(file: &'a File<'a, 'input>) -> Self {
        FileHash {
            functions: Self::functions(file),
            types: Self::types(file),
        }
    }

    /// Returns a map from address to function for all functions in the file.
    fn functions(file: &'a File<'a, 'input>) -> HashMap<u64, &'a Function<'input>> {
        let mut functions = HashMap::new();
        // TODO: insert symbol table names too
        for unit in &file.units {
            for function in unit.functions.values() {
                if let Some(low_pc) = function.low_pc {
                    // TODO: handle duplicate addresses
                    functions.insert(low_pc, function);
                }
            }
        }
        functions
    }

    /// Returns a map from offset to type for all types in the file.
    fn types(file: &'a File<'a, 'input>) -> HashMap<TypeOffset, &'a Type<'input>> {
        let mut types = HashMap::new();
        for unit in &file.units {
            for (offset, ty) in unit.types.iter() {
                types.insert(*offset, ty);
            }
        }
        types
    }
}

#[derive(Debug, PartialEq, Eq)]
enum NamespaceKind {
    Namespace,
    Function,
    Type,
}

#[derive(Debug)]
struct Namespace<'input> {
    parent: Option<Rc<Namespace<'input>>>,
    name: Option<&'input [u8]>,
    kind: NamespaceKind,
}

impl<'input> Namespace<'input> {
    fn new(
        parent: &Option<Rc<Namespace<'input>>>,
        name: Option<&'input [u8]>,
        kind: NamespaceKind,
    ) -> Rc<Namespace<'input>> {
        Rc::new(Namespace {
            parent: parent.clone(),
            name: name,
            kind: kind,
        })
    }

    fn len(&self) -> usize {
        match self.parent {
            Some(ref parent) => parent.len() + 1,
            None => 1,
        }
    }

    fn up(&self, len: usize) -> &Namespace {
        if len == 0 {
            self
        } else {
            match self.parent {
                Some(ref parent) => parent.up(len - 1),
                None => self,
            }
        }
    }

    fn print(&self, w: &mut Write) -> Result<()> {
        if let Some(ref parent) = self.parent {
            parent.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        write!(w, "::")?;
        Ok(())
    }

    fn _filter(&self, namespace: &[&str]) -> (bool, usize) {
        let (ret, offset) = match self.parent {
            Some(ref parent) => parent._filter(namespace),
            None => (true, 0),
        };

        if ret {
            if offset < namespace.len() {
                (filter_name(self.name, namespace[offset]), offset + 1)
            } else {
                (true, offset)
            }
        } else {
            (false, 0)
        }
    }

    fn filter(&self, namespace: &[&str]) -> bool {
        self._filter(namespace) == (true, namespace.len())
    }

    fn _cmp(a: &Namespace, b: &Namespace) -> cmp::Ordering {
        debug_assert_eq!(a.len(), b.len());
        match (a.parent.as_ref(), b.parent.as_ref()) {
            (Some(p1), Some(p2)) => match Self::_cmp(p1, p2) {
                cmp::Ordering::Equal => a.name.cmp(&b.name),
                o => o,
            },
            _ => cmp::Ordering::Equal,
        }
    }

    fn cmp(a: &Namespace, b: &Namespace) -> cmp::Ordering {
        let len_a = a.len();
        let len_b = b.len();
        match len_a.cmp(&len_b) {
            cmp::Ordering::Equal => Self::_cmp(a, b),
            cmp::Ordering::Less => {
                let b = b.up(len_b - len_a);
                match Self::_cmp(a, b) {
                    cmp::Ordering::Equal => cmp::Ordering::Less,
                    other => other,
                }
            }
            cmp::Ordering::Greater => {
                let a = a.up(len_a - len_b);
                match Self::_cmp(a, b) {
                    cmp::Ordering::Equal => cmp::Ordering::Greater,
                    other => other,
                }
            }
        }
    }

    fn is_anon_type(namespace: &Option<Rc<Namespace>>) -> bool {
        match *namespace {
            Some(ref namespace) => {
                namespace.kind == NamespaceKind::Type &&
                    (namespace.name.is_none() || Namespace::is_anon_type(&namespace.parent))
            }
            None => false,
        }
    }
}

fn cmp_ns_and_name(
    ns1: &Option<Rc<Namespace>>,
    name1: Option<&[u8]>,
    ns2: &Option<Rc<Namespace>>,
    name2: Option<&[u8]>,
) -> cmp::Ordering {
    match (ns1, ns2) {
        (&Some(ref ns1), &Some(ref ns2)) => match Namespace::cmp(ns1, ns2) {
            cmp::Ordering::Equal => name1.cmp(&name2),
            o => o,
        },
        (&Some(_), &None) => cmp::Ordering::Greater,
        (&None, &Some(_)) => cmp::Ordering::Less,
        (&None, &None) => name1.cmp(&name2),
    }
}

#[derive(Debug, Default)]
pub struct Unit<'input> {
    dir: Option<&'input [u8]>,
    name: Option<&'input [u8]>,
    language: Option<gimli::DwLang>,
    address_size: Option<u64>,
    low_pc: Option<u64>,
    ranges: RangeList,
    types: BTreeMap<TypeOffset, Type<'input>>,
    functions: BTreeMap<FunctionOffset, Function<'input>>,
    variables: BTreeMap<VariableOffset, Variable<'input>>,
}

impl<'input> Unit<'input> {
    fn prefix_map(&self, options: &Options<'input>) -> (&'input [u8], &'input [u8]) {
        let name = self.name.unwrap_or(&[]);
        for &(old, new) in &options.prefix_map {
            if name.starts_with(old.as_bytes()) {
                return (new.as_bytes(), &name[old.len()..]);
            }
        }
        (&[], name)
    }

    /// Return true if this unit matches the filter options.
    fn filter(&self, options: &Options) -> bool {
        if let Some(filter) = options.filter_unit {
            let (prefix, suffix) = self.prefix_map(options);
            let iter = prefix.iter().chain(suffix);
            iter.cmp(filter.as_bytes()) == cmp::Ordering::Equal
        } else {
            true
        }
    }

    /// The offsets of types that should be printed inline.
    fn inline_types(&self, state: &PrintState) -> HashSet<usize> {
        let mut inline_types = HashSet::new();
        for ty in self.types.values() {
            // Assume all anonymous types are inline. We don't actually check
            // that they will be inline, but in future we could (eg for TypeDefs).
            // TODO: is this a valid assumption?
            if ty.is_anon() {
                inline_types.insert(ty.offset.0);
            }

            // Find all inline members.
            ty.visit_members(&mut |t| if t.is_inline(state.hash) {
                if let Some(offset) = t.ty {
                    inline_types.insert(offset.0);
                }
            });
        }
        inline_types
    }

    /// Filter and sort the list of types using the options.
    /// Perform additional filtering and always sort when diffing.
    fn filter_types(&self, state: &PrintState, options: &Options, diff: bool) -> Vec<&Type> {
        let inline_types = self.inline_types(state);
        let filter_type = |t: &Type| {
            // Filter by user options.
            if !t.filter(options) {
                return false;
            }
            match t.kind {
                TypeKind::Struct(ref t) => {
                    // Hack for rust closures
                    // TODO: is there better way of identifying these, or a
                    // a way to match pairs for diffing?
                    if diff && filter_name(t.name, "closure") {
                        return false;
                    }
                }
                TypeKind::Def(..) | TypeKind::Union(..) | TypeKind::Enumeration(..) => {}
                TypeKind::Base(..) |
                TypeKind::Array(..) |
                TypeKind::Function(..) |
                TypeKind::Unspecified(..) |
                TypeKind::PointerToMember(..) |
                TypeKind::Modifier(..) => return false,
            }
            // Filter out inline types.
            !inline_types.contains(&t.offset.0)
        };
        let mut types: Vec<_> = self.types.values().filter(|a| filter_type(a)).collect();
        match options.sort.with_diff(diff) {
            Sort::None => {}
            Sort::Name => types.sort_by(|a, b| Type::cmp_id(state.hash, a, state.hash, b)),
            Sort::Size => types.sort_by(|a, b| Type::cmp_size(state.hash, a, state.hash, b)),
        }
        types
    }

    /// Filter and sort the list of functions using the options.
    /// Always sort when diffing.
    fn filter_functions(
        &self,
        state: &PrintState,
        options: &Options,
        diff: bool,
    ) -> Vec<&Function> {
        let mut functions: Vec<_> = self.functions.values().filter(|a| a.filter(options)).collect();
        match options.sort.with_diff(diff) {
            Sort::None => {}
            Sort::Name => {
                functions.sort_by(|a, b| Function::cmp_id_and_param(state.hash, a, state.hash, b))
            }
            Sort::Size => functions.sort_by(|a, b| Function::cmp_size(a, b)),
        }
        functions
    }

    /// Filter and sort the list of variables using the options.
    /// Always sort when diffing.
    fn filter_variables(
        &self,
        state: &PrintState,
        options: &Options,
        diff: bool,
    ) -> Vec<&Variable> {
        let mut variables: Vec<_> = self.variables.values().filter(|a| a.filter(options)).collect();
        match options.sort.with_diff(diff) {
            Sort::None => {}
            Sort::Name => variables.sort_by(|a, b| Variable::cmp_id(a, b)),
            Sort::Size => {
                variables.sort_by(|a, b| Variable::cmp_size(state.hash, a, state.hash, b))
            }
        }
        variables
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_address(&self, w: &mut Write) -> Result<()> {
        if self.ranges.list().is_empty() {
            if let Some(low_pc) = self.low_pc {
                write!(w, "address: 0x{:x}", low_pc)?;
            }
        } else if self.ranges.list().len() == 1 {
            write!(w, "address: ")?;
            self.ranges.list()[0].print(w)?;
        }
        Ok(())
    }

    fn size(&self) -> Option<u64> {
        self.ranges.size()
    }

    fn print_size(&self, w: &mut Write) -> Result<()> {
        if let Some(size) = self.size() {
            write!(w, "size: {}", size)?;
        }
        Ok(())
    }

    fn function_size(&self) -> Option<u64> {
        let mut size = 0;
        for function in self.functions.values() {
            if function.low_pc.is_some() {
                size += function.size.unwrap_or(0);
            }
        }
        if size != 0 {
            Some(size)
        } else {
            None
        }
    }

    fn print_function_size(&self, w: &mut Write) -> Result<()> {
        if let Some(size) = self.function_size() {
            write!(w, "fn size: {}", size)?;
        }
        Ok(())
    }

    fn variable_size(&self, hash: &FileHash) -> Option<u64> {
        let mut size = 0;
        for variable in self.variables.values() {
            if variable.address.is_some() {
                size += variable.byte_size(hash).unwrap_or(0);
            }
        }
        if size != 0 {
            Some(size)
        } else {
            None
        }
    }

    fn print_variable_size(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        if let Some(size) = self.variable_size(hash) {
            write!(w, "var size: {}", size)?;
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, options: &Options) -> Result<()> {
        if options.category_unit {
            state.line(w, |w, _state| {
                write!(w, "unit ")?;
                self.print_ref(w)
            })?;
            state.indent(|state| {
                if self.ranges.list().len() > 1 {
                    state.list("addresses", w, &(), self.ranges.list())?;
                } else {
                    state.line_option(w, |w, _state| self.print_address(w))?;
                }
                state.line_option(w, |w, _state| self.print_size(w))?;
                state.line_option(w, |w, _state| self.print_function_size(w))?;
                state.line_option(w, |w, state| self.print_variable_size(w, state.hash))
            })?;
            writeln!(w, "")?;
        }

        if options.category_type {
            for ty in &self.filter_types(state, options, false) {
                ty.print(w, state, self)?;
                writeln!(w, "")?;
            }
        }
        if options.category_function {
            for function in &self.filter_functions(state, options, false) {
                function.print(w, state, self)?;
                writeln!(w, "")?;
            }
        }
        if options.category_variable {
            for variable in &self.filter_variables(state, options, false) {
                variable.print(w, state)?;
                writeln!(w, "")?;
            }
        }
        Ok(())
    }

    /// Compare the identifying information of two units.
    /// This can be used to sort, and to determine if two units refer to the same source.
    fn cmp_id(a: &Unit, b: &Unit, options: &Options) -> cmp::Ordering {
        let (prefix_a, suffix_a) = a.prefix_map(options);
        let (prefix_b, suffix_b) = b.prefix_map(options);
        let iter_a = prefix_a.iter().chain(suffix_a);
        let iter_b = prefix_b.iter().chain(suffix_b);
        iter_a.cmp(iter_b)
    }

    /// Compare the size of two units.
    fn cmp_size(a: &Unit, b: &Unit) -> cmp::Ordering {
        a.size().cmp(&b.size())
    }

    fn diff(
        unit_a: &Unit,
        unit_b: &Unit,
        w: &mut Write,
        state: &mut DiffState,
        options: &Options,
    ) -> Result<()> {
        if options.category_unit {
            state.line(w, unit_a, unit_b, |w, _state, unit| {
                write!(w, "unit ")?;
                unit.print_ref(w)
            })?;
            state.indent(|state| {
                if unit_a.ranges.list().len() > 1 || unit_b.ranges.list().len() > 1 {
                    state.list(
                        "addresses",
                        w,
                        &(),
                        unit_a.ranges.list(),
                        &(),
                        unit_b.ranges.list(),
                    )?;
                } else {
                    state.line_option(w, unit_a, unit_b, |w, _state, x| x.print_address(w))?;
                }
                state.line_option_u64(w, "size", unit_a.size(), unit_b.size())?;
                state
                    .line_option_u64(w, "fn size", unit_a.function_size(), unit_b.function_size())?;
                state.line_option_u64(
                    w,
                    "var size",
                    unit_a.variable_size(state.a.hash),
                    unit_b.variable_size(state.b.hash),
                )
            })?;
            writeln!(w, "")?;
        }

        if options.category_type {
            state
            .merge(
                w,
                |state| unit_a.filter_types(state, options, true),
                |state| unit_b.filter_types(state, options, true),
                |hash_a, a, hash_b, b| Type::cmp_id(hash_a, a, hash_b, b),
                |w, state, a, b| {
                    state.diff(
                        w, |w, state| {
                            Type::diff(w, state, unit_a, a, unit_b, b)?;
                            writeln!(w, "")?;
                            Ok(())
                        }
                    )
                },
                |w, state, a| {
                    if !options.ignore_deleted {
                        a.print(w, state, unit_a)?;
                        writeln!(w, "")?;
                    }
                    Ok(())
                },
                |w, state, b| {
                    if !options.ignore_added {
                        b.print(w, state, unit_b)?;
                        writeln!(w, "")?;
                    }
                    Ok(())
                },
            )?;
        }
        if options.category_function {
            state
            .merge(
                w,
                |state| unit_a.filter_functions(state, options, true),
                |state| unit_b.filter_functions(state, options, true),
                |hash_a, a, hash_b, b| Function::cmp_id(hash_a, a, hash_b, b),
                |w, state, a, b| {
                    state.diff(
                        w, |w, state| {
                            Function::diff(w, state, unit_a, a, unit_b, b)?;
                            writeln!(w, "")?;
                            Ok(())
                        }
                    )
                },
                |w, state, a| {
                    if !options.ignore_deleted {
                        a.print(w, state, unit_a)?;
                        writeln!(w, "")?;
                    }
                    Ok(())
                },
                |w, state, b| {
                    if !options.ignore_added {
                        b.print(w, state, unit_b)?;
                        writeln!(w, "")?;
                    }
                    Ok(())
                },
            )?;
        }
        if options.category_variable {
            state
            .merge(
                w,
                |state| unit_a.filter_variables(state, options, true),
                |state| unit_b.filter_variables(state, options, true),
                |_hash_a, a, _hash_b, b| Variable::cmp_id(a, b),
                |w, state, a, b| {
                    state.diff(
                        w, |w, state| {
                            Variable::diff(w, state, a, b)?;
                            writeln!(w, "")?;
                            Ok(())
                        }
                    )
                },
                |w, state, a| {
                    if !options.ignore_deleted {
                        a.print(w, state)?;
                        writeln!(w, "")?;
                    }
                    Ok(())
                },
                |w, state, b| {
                    if !options.ignore_added {
                        b.print(w, state)?;
                        writeln!(w, "")?;
                    }
                    Ok(())
                },
            )?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct FunctionOffset(usize);

impl From<gimli::DebugInfoOffset> for FunctionOffset {
    fn from(o: gimli::DebugInfoOffset) -> FunctionOffset {
        FunctionOffset(o.0)
    }
}

#[derive(Debug)]
struct Function<'input> {
    namespace: Option<Rc<Namespace<'input>>>,
    name: Option<&'input [u8]>,
    linkage_name: Option<&'input [u8]>,
    low_pc: Option<u64>,
    high_pc: Option<u64>,
    size: Option<u64>,
    inline: bool,
    declaration: bool,
    parameters: Vec<Parameter<'input>>,
    return_type: Option<TypeOffset>,
    inlined_functions: Vec<InlinedFunction<'input>>,
    variables: Vec<Variable<'input>>,
}

impl<'input> Function<'input> {
    fn from_offset<'a>(
        unit: &'a Unit<'input>,
        offset: FunctionOffset,
    ) -> Option<&'a Function<'input>> {
        unit.functions.get(&offset)
    }

    fn return_type<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.return_type.and_then(|v| Type::from_offset(hash, v))
    }

    fn filter(&self, options: &Options) -> bool {
        if !self.inline && self.low_pc.is_none() {
            // TODO: make this configurable?
            return false;
        }
        options.filter_name(self.name) && options.filter_namespace(&self.namespace) &&
            options.filter_function_inline(self.inline)
    }

    fn calls(&self, file: &File) -> Vec<u64> {
        if let (Some(low_pc), Some(high_pc)) = (self.low_pc, self.high_pc) {
            if low_pc != 0 {
                if let Some(ref code) = file.code {
                    return disassemble(code, low_pc, high_pc);
                }
            }
        }
        Vec::new()
    }

    /// Compare the identifying information of two functions.
    /// This can be used to sort, and to determine if two functions refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(_hash_a: &FileHash, a: &Function, _hash_b: &FileHash, b: &Function) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    // This function is a bit of a hack. We use it for sorting, but not for
    // equality, in the hopes that we'll get better results in the presence
    // of overloading, while still coping with changed function signatures.
    // TODO: do something smarter
    fn cmp_id_and_param(
        hash_a: &FileHash,
        a: &Function,
        hash_b: &FileHash,
        b: &Function,
    ) -> cmp::Ordering {
        let ord = Self::cmp_id(hash_a, a, hash_b, b);
        if ord != cmp::Ordering::Equal {
            return ord;
        }

        for (parameter_a, parameter_b) in a.parameters.iter().zip(b.parameters.iter()) {
            let ord = Parameter::cmp_type(hash_a, parameter_a, hash_b, parameter_b);
            if ord != cmp::Ordering::Equal {
                return ord;
            }
        }

        a.parameters.len().cmp(&b.parameters.len())
    }

    /// Compare the size of two functions.
    fn cmp_size(a: &Function, b: &Function) -> cmp::Ordering {
        a.size.cmp(&b.size)
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line(w, |w, _state| self.print_name(w))?;
        state.indent(|state| {
            state.line_option(w, |w, _state| self.print_linkage_name(w))?;
            state.line_option(w, |w, _state| self.print_address(w))?;
            state.line_option(w, |w, _state| self.print_size(w))?;
            state.line_option(w, |w, _state| self.print_inline(w))?;
            state.line_option(w, |w, _state| self.print_declaration(w))?;
            state.line_option(w, |w, _state| self.print_return_type_label(w))?;
            state
                .indent(|state| state.line_option(w, |w, state| self.print_return_type(w, state)))?;
            state.list("parameters", w, unit, &self.parameters)?;
            state.list("variables", w, unit, &self.variables)?;
            state
                .inline(|state| state.list("inlined functions", w, unit, &self.inlined_functions))?;
            if state.options.calls {
                let calls = self.calls(state.file);
                if !calls.is_empty() {
                    state.line(w, |w, _state| self.print_calls_label(w))?;
                    state.indent(|state| self.print_calls(w, state, &calls))?;
                }
            }
            Ok(())
        })
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Function,
        unit_b: &Unit,
        b: &Function,
    ) -> Result<()> {
        state.line(w, a, b, |w, _state, x| x.print_name(w))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, _state, x| x.print_linkage_name(w))?;
            let flag = state.options.ignore_function_address;
            state.ignore_diff(
                flag,
                |state| state.line_option(w, a, b, |w, _state, x| x.print_address(w)),
            )?;
            let flag = state.options.ignore_function_size;
            state.ignore_diff(
                flag,
                |state| state.line_option(w, a, b, |w, _state, x| x.print_size(w)),
            )?;
            let flag = state.options.ignore_function_inline;
            state.ignore_diff(
                flag,
                |state| state.line_option(w, a, b, |w, _state, x| x.print_inline(w)),
            )?;
            state.line_option(w, a, b, |w, _state, x| x.print_declaration(w))?;
            state.line_option(w, a, b, |w, _state, x| x.print_return_type_label(w))?;
            state
                .indent(
                    |state| state.line_option(w, a, b, |w, state, x| x.print_return_type(w, state)),
                )?;
            state.list("parameters", w, unit_a, &a.parameters, unit_b, &b.parameters)?;
            {
                let mut variables_a: Vec<_> = a.variables.iter().collect();
                variables_a.sort_by(|x, y| Variable::cmp_id(x, y));
                let mut variables_b: Vec<_> = b.variables.iter().collect();
                variables_b.sort_by(|x, y| Variable::cmp_id(x, y));
                state.list("variables", w, unit_a, &variables_a, unit_b, &variables_b)?;
            }
            state.inline(|state| {
                state.list(
                    "inlined functions",
                    w,
                    unit_a,
                    &a.inlined_functions,
                    unit_b,
                    &b.inlined_functions,
                )
            })?;
            // TODO
            if false && state.options.calls {
                let calls_a = a.calls(state.a.file);
                let calls_b = b.calls(state.b.file);
                state.line_option(w, (a, &calls_a), (b, &calls_b), |w, _state, (x, calls)| {
                    if !calls.is_empty() {
                        x.print_calls_label(w)?;
                    }
                    Ok(())
                })?;
                state.indent(|state| Function::diff_calls(w, state, &calls_a, &calls_b))?;
            }
            Ok(())
        })
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        write!(w, "fn ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_linkage_name(&self, w: &mut Write) -> Result<()> {
        if let Some(linkage_name) = self.linkage_name {
            write!(w, "linkage name: {}", String::from_utf8_lossy(linkage_name))?;
        }
        Ok(())
    }

    fn print_address(&self, w: &mut Write) -> Result<()> {
        if let (Some(low_pc), Some(high_pc)) = (self.low_pc, self.high_pc) {
            if high_pc > low_pc {
                write!(w, "address: 0x{:x}-0x{:x}", low_pc, high_pc - 1)?;
            } else {
                write!(w, "address: 0x{:x}", low_pc)?;
            }
        } else if let Some(low_pc) = self.low_pc {
            write!(w, "address: 0x{:x}", low_pc)?;
        } else if !self.inline && !self.declaration {
            debug!("non-inline function with no address");
        }
        Ok(())
    }

    fn print_size(&self, w: &mut Write) -> Result<()> {
        if let Some(size) = self.size {
            write!(w, "size: {}", size)?;
        }
        Ok(())
    }

    fn print_inline(&self, w: &mut Write) -> Result<()> {
        if self.inline {
            write!(w, "inline: yes")?;
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_return_type_label(&self, w: &mut Write) -> Result<()> {
        if self.return_type.is_some() {
            write!(w, "return type:")?;
        }
        Ok(())
    }

    fn print_return_type(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        if self.return_type.is_some() {
            match self.return_type(state.hash).and_then(|t| t.byte_size(state.hash)) {
                Some(byte_size) => write!(w, "[{}]", byte_size)?,
                None => write!(w, "[??]")?,
            }
            write!(w, "\t")?;
            Type::print_ref_from_offset(w, state, self.return_type)?;
        }
        Ok(())
    }

    fn print_calls_label(&self, w: &mut Write) -> Result<()> {
        write!(w, "calls:")?;
        Ok(())
    }

    fn print_calls(&self, w: &mut Write, state: &mut PrintState, calls: &[u64]) -> Result<()> {
        for call in calls {
            state.line(w, |w, state| {
                write!(w, "0x{:x}", call)?;
                if let Some(function) = state.hash.functions.get(call) {
                    write!(w, " ")?;
                    function.print_ref(w)?;
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    fn diff_calls(
        _w: &mut Write,
        _state: &mut DiffState,
        _calls_a: &[u64],
        _calls_b: &[u64],
    ) -> Result<()> {
        // TODO
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Parameter<'input> {
    name: Option<&'input [u8]>,
    ty: Option<TypeOffset>,
}

impl<'input> Parameter<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash))
    }

    fn print_decl(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        if let Some(name) = self.name {
            write!(w, "{}: ", String::from_utf8_lossy(name))?;
        }
        match self.ty(state.hash) {
            Some(ty) => ty.print_ref(w, state)?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_size_and_decl(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        match self.byte_size(state.hash) {
            Some(byte_size) => write!(w, "[{}]", byte_size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        self.print_decl(w, state)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    #[allow(dead_code)]
    fn cmp_id(hash_a: &FileHash, a: &Parameter, hash_b: &FileHash, b: &Parameter) -> cmp::Ordering {
        let ord = Self::cmp_type(hash_a, a, hash_b, b);
        if ord != cmp::Ordering::Equal {
            return ord;
        }
        a.name.cmp(&b.name)
    }

    fn cmp_type(
        hash_a: &FileHash,
        a: &Parameter,
        hash_b: &FileHash,
        b: &Parameter,
    ) -> cmp::Ordering {
        match (a.ty(hash_a), b.ty(hash_b)) {
            (Some(ty_a), Some(ty_b)) => Type::cmp_id(hash_a, ty_a, hash_b, ty_b),
            (Some(_), None) => cmp::Ordering::Less,
            (None, Some(_)) => cmp::Ordering::Greater,
            (None, None) => cmp::Ordering::Equal,
        }
    }
}

impl<'input> PrintList for Parameter<'input> {
    type Arg = Unit<'input>;

    fn print_list(&self, w: &mut Write, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(w, |w, state| self.print_size_and_decl(w, state))
    }
}

impl<'input> DiffList for Parameter<'input> {
    fn step_cost() -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 1;
        }
        match (a.ty(state.a.hash), b.ty(state.b.hash)) {
            (Some(ty_a), Some(ty_b)) => {
                if Type::cmp_id(state.a.hash, ty_a, state.b.hash, ty_b) != cmp::Ordering::Equal {
                    cost += 1;
                }
            }
            (None, None) => {}
            _ => {
                cost += 1;
            }
        }
        cost
    }

    fn diff_list(
        w: &mut Write,
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(w, a, b, |w, state, x| x.print_size_and_decl(w, state))
    }
}

#[derive(Debug, Default)]
struct InlinedFunction<'input> {
    abstract_origin: Option<FunctionOffset>,
    size: Option<u64>,
    inlined_functions: Vec<InlinedFunction<'input>>,
    variables: Vec<Variable<'input>>,
}

impl<'input> InlinedFunction<'input> {
    fn print_size_and_decl(&self, w: &mut Write, _state: &PrintState, unit: &Unit) -> Result<()> {
        match self.size {
            Some(size) => write!(w, "[{}]", size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        match self.abstract_origin.and_then(|v| Function::from_offset(unit, v)) {
            Some(function) => function.print_ref(w)?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }
}

impl<'input> PrintList for InlinedFunction<'input> {
    type Arg = Unit<'input>;

    fn print_list(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line(w, |w, state| self.print_size_and_decl(w, state, unit))?;
        state.inline(|state| state.list("", w, unit, &self.inlined_functions))?;
        Ok(())
    }
}

impl<'input> DiffList for InlinedFunction<'input> {
    fn step_cost() -> usize {
        1
    }

    fn diff_cost(state: &DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        let function_a = a.abstract_origin.and_then(|v| Function::from_offset(unit_a, v)).unwrap();
        let function_b = b.abstract_origin.and_then(|v| Function::from_offset(unit_b, v)).unwrap();
        if Function::cmp_id(state.a.hash, function_a, state.b.hash, function_b) !=
            cmp::Ordering::Equal
        {
            cost += 1;
        }
        if a.size != b.size {
            cost += 1;
        }
        cost
    }

    fn diff_list(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Self,
        unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(
            w,
            (unit_a, a),
            (unit_b, b),
            |w, state, (unit, x)| x.print_size_and_decl(w, state, unit),
        )?;

        state
            .inline(|state| {
                state.list("", w, unit_a, &a.inlined_functions, unit_b, &b.inlined_functions)
            })?;

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct VariableOffset(usize);

impl From<gimli::DebugInfoOffset> for VariableOffset {
    fn from(o: gimli::DebugInfoOffset) -> VariableOffset {
        VariableOffset(o.0)
    }
}

#[derive(Debug, Default)]
struct Variable<'input> {
    namespace: Option<Rc<Namespace<'input>>>,
    name: Option<&'input [u8]>,
    linkage_name: Option<&'input [u8]>,
    ty: Option<TypeOffset>,
    declaration: bool,
    address: Option<u64>,
}

impl<'input> Variable<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|t| t.byte_size(hash))
    }

    fn filter(&self, options: &Options) -> bool {
        if !self.declaration && self.address.is_none() {
            // TODO: make this configurable?
            return false;
        }
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two variables.
    /// This can be used to sort, and to determine if two variables refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &Variable, b: &Variable) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    /// Compare the size of two variables.
    fn cmp_size(hash_a: &FileHash, a: &Variable, hash_b: &FileHash, b: &Variable) -> cmp::Ordering {
        a.byte_size(hash_a).cmp(&b.byte_size(hash_b))
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_decl(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        self.print_ref(w)?;
        write!(w, ": ")?;
        Type::print_ref_from_offset(w, state, self.ty)?;
        Ok(())
    }

    fn print_size_and_decl(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        match self.byte_size(state.hash) {
            Some(byte_size) => write!(w, "[{}]", byte_size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        self.print_decl(w, state)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line(w, |w, state| self.print_name(w, state))?;
        state.indent(|state| {
            state.line_option(w, |w, _state| self.print_linkage_name(w))?;
            state.line_option(w, |w, _state| self.print_address(w))?;
            state.line_option(w, |w, state| self.print_size(w, state))?;
            state.line_option(w, |w, _state| self.print_declaration(w))
            // TODO: print anon type inline
        })
    }

    fn diff(w: &mut Write, state: &mut DiffState, a: &Variable, b: &Variable) -> Result<()> {
        state.line(w, a, b, |w, state, x| x.print_name(w, state))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, _state, x| x.print_linkage_name(w))?;
            let flag = state.options.ignore_variable_address;
            state.ignore_diff(
                flag,
                |state| state.line_option(w, a, b, |w, _state, x| x.print_address(w)),
            )?;
            state.line_option(w, a, b, |w, state, x| x.print_size(w, state))?;
            state.line_option(w, a, b, |w, _state, x| x.print_declaration(w))
        })
    }

    fn print_name(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        write!(w, "var ")?;
        self.print_ref(w)?;
        write!(w, ": ")?;
        Type::print_ref_from_offset(w, state, self.ty)?;
        Ok(())
    }

    fn print_linkage_name(&self, w: &mut Write) -> Result<()> {
        if let Some(linkage_name) = self.linkage_name {
            write!(w, "linkage name: {}", String::from_utf8_lossy(linkage_name))?;
        }
        Ok(())
    }

    fn print_address(&self, w: &mut Write) -> Result<()> {
        if let Some(address) = self.address {
            write!(w, "address: 0x{:x}", address)?;
        }
        Ok(())
    }

    fn print_size(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        if let Some(byte_size) = self.byte_size(state.hash) {
            write!(w, "size: {}", byte_size)?;
        } else if !self.declaration {
            debug!("variable with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }
}

impl<'input> PrintList for Variable<'input> {
    type Arg = Unit<'input>;

    fn print_list(&self, w: &mut Write, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(w, |w, state| self.print_size_and_decl(w, state))
    }
}

impl<'a, 'input> DiffList for &'a Variable<'input> {
    fn step_cost() -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 1;
        }
        match (a.ty(state.a.hash), b.ty(state.b.hash)) {
            (Some(ty_a), Some(ty_b)) => {
                if Type::cmp_id(state.a.hash, ty_a, state.b.hash, ty_b) != cmp::Ordering::Equal {
                    cost += 1;
                }
            }
            (None, None) => {}
            _ => {
                cost += 1;
            }
        }
        cost
    }

    fn diff_list(
        w: &mut Write,
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(w, a, b, |w, state, x| x.print_size_and_decl(w, state))
    }
}

fn disassemble(code: &CodeRegion, low_pc: u64, high_pc: u64) -> Vec<u64> {
    match code.machine {
        goblin::elf::header::EM_X86_64 => {
            disassemble_arch::<amd64::Amd64>(&code.region, low_pc, high_pc, amd64::Mode::Long)
        }
        _ => Vec::new(),
    }
}

fn disassemble_arch<A>(
    region: &panopticon::Region,
    low_pc: u64,
    high_pc: u64,
    cfg: A::Configuration,
) -> Vec<u64>
where
    A: panopticon::Architecture + Debug,
    A::Configuration: Debug,
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
            /*
            //writeln!(w, "\t{:?}", mnemonic);
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

            for instruction in &mnemonic.instructions {
                match *instruction {
                    panopticon::Statement {
                        op: panopticon::Operation::Call(ref call),
                        ..
                    } => match *call {
                        panopticon::Rvalue::Constant { ref value, .. } => {
                            calls.push(*value);
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
            // FIXME: mnemonic is large, insert boxed value
            mnemonics.insert(mnemonic.area.start, mnemonic);
        }

        for (_origin, target, _guard) in m.jumps {
            if let panopticon::Rvalue::Constant { value, .. } = target {
                if value > addr && value < high_pc {
                    jumps.push(value);
                }
            }
        }
    }
    calls
}
