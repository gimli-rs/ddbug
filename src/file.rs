use std::cmp;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::rc::Rc;

use elf;
use gimli;
use goblin;
use mach;
use memmap;
use pdb;
use panopticon;

use {filter_name, Options, Result, Sort};
use diffstate::{DiffState, PrintState};
use function::{Function, FunctionOffset};
use range::RangeList;
use types::{Type, TypeKind, TypeOffset};
use variable::{Variable, VariableOffset};

#[derive(Debug)]
pub(crate) struct CodeRegion {
    // TODO: use format independent machine type
    pub machine: u16,
    pub region: panopticon::Region,
}

#[derive(Debug)]
pub struct File<'a, 'input> {
    pub(crate) path: &'a str,
    pub(crate) code: Option<CodeRegion>,
    pub(crate) units: Vec<Unit<'input>>,
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
pub(crate) struct FileHash<'a, 'input>
where
    'input: 'a,
{
    // All functions by address.
    pub functions: HashMap<u64, &'a Function<'input>>,
    // All types by offset.
    pub types: HashMap<TypeOffset, &'a Type<'input>>,
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
pub(crate) enum NamespaceKind {
    Namespace,
    Function,
    Type,
}

#[derive(Debug)]
pub(crate) struct Namespace<'input> {
    pub parent: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub kind: NamespaceKind,
}

impl<'input> Namespace<'input> {
    pub fn new(
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

    pub fn print(&self, w: &mut Write) -> Result<()> {
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

    pub fn filter(&self, namespace: &[&str]) -> bool {
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

    pub fn is_anon_type(namespace: &Option<Rc<Namespace>>) -> bool {
        match *namespace {
            Some(ref namespace) => {
                namespace.kind == NamespaceKind::Type &&
                    (namespace.name.is_none() || Namespace::is_anon_type(&namespace.parent))
            }
            None => false,
        }
    }
}

pub(crate) fn cmp_ns_and_name(
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
pub(crate) struct Unit<'input> {
    pub dir: Option<&'input [u8]>,
    pub name: Option<&'input [u8]>,
    pub language: Option<gimli::DwLang>,
    pub address_size: Option<u64>,
    pub low_pc: Option<u64>,
    pub ranges: RangeList,
    pub types: BTreeMap<TypeOffset, Type<'input>>,
    pub functions: BTreeMap<FunctionOffset, Function<'input>>,
    pub variables: BTreeMap<VariableOffset, Variable<'input>>,
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
