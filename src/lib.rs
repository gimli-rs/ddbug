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
use std::cmp;
use std::error;
use std::fmt::{self, Debug};
use std::fs;
use std::ffi;
use std::io::Write;
use std::result;
use std::rc::Rc;

use panopticon::amd64;

mod dwarf;

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

#[derive(Debug, Clone)]
pub struct Flags<'a> {
    pub calls: bool,
    pub sort: bool,
    pub inline_depth: usize,
    pub unit: Option<&'a str>,
    pub name: Option<&'a str>,
    pub namespace: Vec<&'a str>,
}

impl<'a> Flags<'a> {
    pub fn unit(&mut self, unit: &'a str) -> &mut Self {
        self.unit = Some(unit);
        self
    }

    pub fn name(&mut self, name: &'a str) -> &mut Self {
        self.name = Some(name);
        self
    }

    fn filter_unit(&self, unit: Option<&ffi::CStr>) -> bool {
        if let Some(filter) = self.unit {
            filter_name(unit, filter)
        } else {
            true
        }
    }

    fn filter_name(&self, name: Option<&ffi::CStr>) -> bool {
        if let Some(filter) = self.name {
            filter_name(name, filter)
        } else {
            true
        }
    }

    fn filter_namespace(&self, namespace: &Namespace) -> bool {
        namespace.filter(&self.namespace)
    }
}

fn filter_name(name: Option<&ffi::CStr>, filter: &str) -> bool {
    match name {
        Some(name) => name.to_bytes() == filter.as_bytes(),
        None => false,
    }
}


#[derive(Debug)]
pub struct File<'input> {
    // TODO: use format independent machine type
    machine: xmas_elf::header::Machine,
    region: panopticon::Region,
    units: Vec<Unit<'input>>,
}

impl<'input> File<'input> {
    /// Returns a map from address to subprogram for all subprograms in the file.
    fn subprograms(&self) -> HashMap<u64, &Subprogram<'input>> {
        let mut all_subprograms = HashMap::new();
        // TODO: insert symbol table names too
        for unit in &self.units {
            for subprogram in unit.subprograms.values() {
                if let Some(low_pc) = subprogram.low_pc {
                    all_subprograms.insert(low_pc, subprogram);
                }
            }
        }
        all_subprograms
    }

    fn filter_units(&self, flags: &Flags, diff: bool) -> Vec<&Unit> {
        let mut units: Vec<_> = self.units.iter().filter(|a| a.filter(flags)).collect();
        if diff || flags.sort {
            units.sort_by(|a, b| Unit::cmp_id(a, b));
        }
        units
    }
}

pub fn parse_file(path: &str, cb: &mut FnMut(&mut File) -> Result<()>) -> Result<()> {
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
    let machine = elf.header.pt2?.machine();
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
        xmas_elf::header::Data::LittleEndian => dwarf::parse::<gimli::LittleEndian>(&elf)?,
        xmas_elf::header::Data::BigEndian => dwarf::parse::<gimli::BigEndian>(&elf)?,
        _ => {
            return Err("Unknown endianity".into());
        }
    };

    let mut file = File {
        machine: machine,
        region: region,
        units: units,
    };

    cb(&mut file)
}

struct PrintState<'a, 'input>
    where 'input: 'a
{
    indent: usize,
    prefix: &'static str,

    // The remaining fields contain information that is commonly needed in print methods.
    file: &'a File<'input>,
    // All subprograms by address.
    all_subprograms: &'a HashMap<u64, &'a Subprogram<'input>>,
    flags: &'a Flags<'a>,
}

impl<'a, 'input> PrintState<'a, 'input>
    where 'input: 'a
{
    fn new(
        file: &'a File<'input>,
        subprograms: &'a HashMap<u64, &'a Subprogram<'input>>,
        flags: &'a Flags<'a>
    ) -> Self {
        PrintState {
            indent: 0,
            prefix: "",
            file: file,
            all_subprograms: subprograms,
            flags: flags,
        }
    }

    fn indent<F>(&mut self, mut f: F) -> Result<()>
        where F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>
    {
        self.indent += 1;
        let ret = f(self);
        self.indent -= 1;
        ret
    }

    fn prefix<F>(&mut self, prefix: &'static str, mut f: F) -> Result<()>
        where F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>
    {
        let prev = self.prefix;
        self.prefix = prefix;
        let ret = f(self);
        self.prefix = prev;
        ret
    }

    fn line_start(&self, w: &mut Write) -> Result<()> {
        write!(w, "{}", self.prefix)?;
        for _ in 0..self.indent {
            write!(w, "\t")?;
        }
        Ok(())
    }
}

pub fn print_file(w: &mut Write, file: &mut File, flags: &Flags) -> Result<()> {
    let subprograms = file.subprograms();
    for unit in file.filter_units(flags, false).iter() {
        let mut state = PrintState::new(file, &subprograms, flags);
        if flags.unit.is_none() {
            state.line_start(w)?;
            write!(w, "Unit: ")?;
            unit.print_ref(w)?;
            writeln!(w, "")?;
        }
        unit.print(w, &mut state, flags)?;
    }
    Ok(())
}

enum MergeResult<T> {
    Left(T),
    Right(T),
    Both(T, T),
}

struct MergeIterator<T, I, C>
    where T: Copy,
          I: Iterator<Item = T>,
          C: Fn(T, T) -> cmp::Ordering
{
    iter_left: I,
    iter_right: I,
    item_left: Option<T>,
    item_right: Option<T>,
    item_cmp: C,
}

impl<T, I, C> MergeIterator<T, I, C>
    where T: Copy,
          I: Iterator<Item = T>,
          C: Fn(T, T) -> cmp::Ordering
{
    fn new(mut left: I, mut right: I, cmp: C) -> Self {
        let item_left = left.next();
        let item_right = right.next();
        MergeIterator {
            iter_left: left,
            iter_right: right,
            item_left: item_left,
            item_right: item_right,
            item_cmp: cmp,
        }
    }
}

impl<T, I, C> Iterator for MergeIterator<T, I, C>
    where T: Copy,
          I: Iterator<Item = T>,
          C: Fn(T, T) -> cmp::Ordering
{
    type Item = MergeResult<T>;

    fn next(&mut self) -> Option<MergeResult<T>> {
        match (self.item_left, self.item_right) {
            (Some(left), Some(right)) => {
                match (self.item_cmp)(left, right) {
                    cmp::Ordering::Equal => {
                        self.item_left = self.iter_left.next();
                        self.item_right = self.iter_right.next();
                        Some(MergeResult::Both(left, right))
                    }
                    cmp::Ordering::Less => {
                        self.item_left = self.iter_left.next();
                        Some(MergeResult::Left(left))
                    }
                    cmp::Ordering::Greater => {
                        self.item_right = self.iter_right.next();
                        Some(MergeResult::Right(right))
                    }
                }
            }
            (Some(left), None) => {
                self.item_left = self.iter_left.next();
                Some(MergeResult::Left(left))
            }
            (None, Some(right)) => {
                self.item_right = self.iter_right.next();
                Some(MergeResult::Right(right))
            }
            (None, None) => None,
        }
    }
}

struct DiffState<'a, 'input>
    where 'input: 'a
{
    a: PrintState<'a, 'input>,
    b: PrintState<'a, 'input>,
}

impl<'a, 'input> DiffState<'a, 'input>
    where 'input: 'a
{
    fn new(
        file_a: &'a File<'input>,
        subprograms_a: &'a HashMap<u64, &'a Subprogram<'input>>,
        file_b: &'a File<'input>,
        subprograms_b: &'a HashMap<u64, &'a Subprogram<'input>>,
        flags: &'a Flags<'a>
    ) -> Self {
        DiffState {
            a: PrintState::new(file_a, subprograms_a, flags),
            b: PrintState::new(file_b, subprograms_b, flags),
        }
    }

    fn merge<T, I, FCmp, FEqual, FLess, FGreater>(
        &mut self,
        w: &mut Write,
        iter_a: I,
        iter_b: I,
        cmp: FCmp,
        mut equal: FEqual,
        less: FLess,
        greater: FGreater
    ) -> Result<()>
        where T: Copy,
              I: Iterator<Item = T>,
              FCmp: Fn(T, T) -> cmp::Ordering,
              FEqual: FnMut(&mut Write, &mut DiffState<'a, 'input>, T, T) -> Result<()>,
              FLess: Fn(&mut Write, &mut PrintState<'a, 'input>, T) -> Result<()>,
              FGreater: Fn(&mut Write, &mut PrintState<'a, 'input>, T) -> Result<()>
    {
        for m in MergeIterator::new(iter_a, iter_b, cmp) {
            match m {
                MergeResult::Both(l, r) => self.prefix_equal(|state| equal(w, state, l, r))?,
                MergeResult::Left(l) => self.prefix_less(|state| less(w, state, l))?,
                MergeResult::Right(r) => self.prefix_greater(|state| greater(w, state, r))?,
            }
        }
        Ok(())
    }

    fn indent<F>(&mut self, mut f: F) -> Result<()>
        where F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>
    {
        self.a.indent += 1;
        self.b.indent += 1;
        let ret = f(self);
        self.a.indent -= 1;
        self.b.indent -= 1;
        ret
    }

    fn prefix_equal<F>(&mut self, mut f: F) -> Result<()>
        where F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>
    {
        let prev_a = self.a.prefix;
        let prev_b = self.b.prefix;
        self.a.prefix = "  ";
        self.b.prefix = "  ";
        let ret = f(self);
        self.a.prefix = prev_a;
        self.b.prefix = prev_b;
        ret
    }

    fn prefix_less<F>(&mut self, f: F) -> Result<()>
        where F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>
    {
        self.a.prefix("- ", f)
    }

    fn prefix_greater<F>(&mut self, f: F) -> Result<()>
        where F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>
    {
        self.b.prefix("+ ", f)
    }

    fn prefix_diff<F>(&mut self, mut f: F) -> Result<()>
        where F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>
    {
        let prev_a = self.a.prefix;
        let prev_b = self.b.prefix;
        self.a.prefix = "- ";
        self.b.prefix = "+ ";
        let ret = f(self);
        self.a.prefix = prev_a;
        self.b.prefix = prev_b;
        ret
    }

    fn diff<A, B>(&mut self, w: &mut Write, mut f_a: A, mut f_b: B) -> Result<()>
        where A: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>,
              B: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>
    {
        let mut a = Vec::new();
        let mut state = PrintState::new(self.a.file, self.a.all_subprograms, self.a.flags);
        f_a(&mut a, &mut state)?;

        let mut b = Vec::new();
        let mut state = PrintState::new(self.b.file, self.b.all_subprograms, self.b.flags);
        f_b(&mut b, &mut state)?;

        if a == b {
            self.prefix_equal(|state| {
                state.a.line_start(w)?;
                w.write_all(&*a)?;
                Ok(())
            })
        } else {
            self.prefix_diff(|state| {
                state.a.line_start(w)?;
                w.write_all(&*a)?;
                state.b.line_start(w)?;
                w.write_all(&*b)?;
                Ok(())
            })
        }
    }
}

pub fn diff_file(w: &mut Write, file_a: &mut File, file_b: &mut File, flags: &Flags) -> Result<()> {
    let subprograms_a = file_a.subprograms();
    let subprograms_b = file_b.subprograms();
    let mut state = DiffState::new(file_a, &subprograms_a, file_b, &subprograms_b, flags);
    state.merge(w,
               &mut file_a.filter_units(flags, true).iter(),
               &mut file_b.filter_units(flags, true).iter(),
               |a, b| Unit::cmp_id(a, b),
               |w, state, a, b| {
            if flags.unit.is_none() {
                state.a.line_start(w)?;
                write!(w, "Unit: ")?;
                a.print_ref(w)?;
                writeln!(w, "")?;
            }
            Unit::diff(a, b, w, state, flags)
        },
               |w, state, a| {
            state.line_start(w)?;
            write!(w, "Unit: ")?;
            a.print_ref(w)?;
            writeln!(w, "")?;
            Ok(())
        },
               |w, state, b| {
            state.line_start(w)?;
            write!(w, "Unit: ")?;
            b.print_ref(w)?;
            writeln!(w, "")?;
            Ok(())
        })?;
    Ok(())
}

#[derive(Debug, Default)]
struct Namespace<'input> {
    parent: Option<Rc<Namespace<'input>>>,
    name: Option<&'input ffi::CStr>,
}

impl Namespace<'static> {
    fn root() -> Rc<Namespace<'static>> {
        Rc::new(Namespace {
            parent: None,
            name: None,
        })
    }
}

impl<'input> Namespace<'input> {
    fn new(
        parent: &Rc<Namespace<'input>>,
        name: Option<&'input ffi::CStr>
    ) -> Rc<Namespace<'input>> {
        Rc::new(Namespace {
            parent: Some(parent.clone()),
            name: name,
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
            match self.name {
                Some(name) => write!(w, "{}", name.to_string_lossy())?,
                None => write!(w, "<anon>")?,
            }
            write!(w, "::")?;
        }
        Ok(())
    }

    fn _filter(&self, namespace: &[&str]) -> (bool, usize) {
        match self.parent {
            Some(ref parent) => {
                let (ret, offset) = parent._filter(namespace);
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
            None => (true, 0),
        }
    }

    fn filter(&self, namespace: &[&str]) -> bool {
        self._filter(namespace) == (true, namespace.len())
    }

    fn _cmp(a: &Namespace, b: &Namespace) -> cmp::Ordering {
        debug_assert!(a.len() == b.len());
        match (a.parent.as_ref(), b.parent.as_ref()) {
            (Some(p1), Some(p2)) => {
                match Self::_cmp(p1, p2) {
                    cmp::Ordering::Equal => a.name.cmp(&b.name),
                    o => o,
                }
            }
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
}

fn cmp_ns_and_name(
    ns1: &Namespace,
    name1: Option<&ffi::CStr>,
    ns2: &Namespace,
    name2: Option<&ffi::CStr>
) -> cmp::Ordering {
    match Namespace::cmp(ns1, ns2) {
        cmp::Ordering::Equal => name1.cmp(&name2),
        o => o,
    }
}

#[derive(Debug, Default)]
pub struct Unit<'input> {
    dir: Option<&'input ffi::CStr>,
    name: Option<&'input ffi::CStr>,
    language: Option<gimli::DwLang>,
    address_size: Option<u64>,
    low_pc: Option<u64>,
    high_pc: Option<u64>,
    size: Option<u64>,
    types: BTreeMap<usize, Type<'input>>,
    subprograms: BTreeMap<usize, Subprogram<'input>>,
    variables: Vec<Variable<'input>>,
}

impl<'input> Unit<'input> {
    /// Return true if this unit matches the filter options in the flags.
    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_unit(self.name)
    }

    /// The offsets of types that should be printed inline.
    fn inline_types(&self) -> HashSet<usize> {
        let mut inline_types = HashSet::new();
        for ty in self.types.values() {
            // Assume all anonymous types are inline. We don't actually check
            // that they will be inline, but in future we could (eg for TypeDefs).
            // TODO: is this a valid assumption?
            if ty.is_anon() {
                inline_types.insert(ty.offset.0);
            }

            // Find all inline members.
            ty.visit_members(&mut |t| {
                if t.is_inline(self) {
                    if let Some(offset) = t.ty {
                        inline_types.insert(offset.0);
                    }
                }
            });
        }
        inline_types
    }

    /// Filter and sort the list of types using the options in the flags.
    /// Perform additional filtering and always sort when diffing.
    fn filter_types(&self, flags: &Flags, diff: bool) -> Vec<&Type> {
        let inline_types = self.inline_types();
        let filter_type = |t: &Type| {
            // Filter by user options.
            if !t.filter(flags) {
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
                TypeKind::Def(..) |
                TypeKind::Union(..) |
                TypeKind::Enumeration(..) => {}
                TypeKind::Base(..) |
                TypeKind::Array(..) |
                TypeKind::Subroutine(..) |
                TypeKind::Modifier(..) |
                TypeKind::Unimplemented(..) => return false,
            }
            // Filter out inline types.
            !inline_types.contains(&t.offset.0)
        };
        let mut types: Vec<_> = self.types.values().filter(|a| filter_type(a)).collect();
        if diff || flags.sort {
            types.sort_by(|a, b| Type::cmp_id(a, b));
        }
        types
    }

    /// Filter and sort the list of subprograms using the options in the flags.
    /// Always sort when diffing.
    fn filter_subprograms(&self, flags: &Flags, diff: bool) -> Vec<&Subprogram> {
        let mut subprograms: Vec<_> =
            self.subprograms.values().filter(|a| a.filter(flags)).collect();
        if diff || flags.sort {
            subprograms.sort_by(|a, b| Subprogram::cmp_id(a, b));
        }
        subprograms
    }

    /// Filter and sort the list of variables using the options in the flags.
    /// Always sort when diffing.
    fn filter_variables(&self, flags: &Flags, diff: bool) -> Vec<&Variable> {
        let mut variables: Vec<_> = self.variables.iter().filter(|a| a.filter(flags)).collect();
        if diff || flags.sort {
            variables.sort_by(|a, b| Variable::cmp_id(a, b));
        }
        variables
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, flags: &Flags) -> Result<()> {
        for ty in &self.filter_types(flags, false) {
            ty.print(w, state, self)?;
        }
        for subprogram in &self.filter_subprograms(flags, false) {
            subprogram.print(w, state, self)?;
        }
        for variable in &self.filter_variables(flags, false) {
            variable.print(w, state, self)?;
        }
        Ok(())
    }

    /// Compare the identifying information of two units.
    /// This can be used to sort, and to determine if two units refer to the same source.
    fn cmp_id(a: &Unit, b: &Unit) -> cmp::Ordering {
        // TODO: ignore base paths
        a.name.cmp(&b.name)
    }

    fn diff(
        unit_a: &Unit,
        unit_b: &Unit,
        w: &mut Write,
        state: &mut DiffState,
        flags: &Flags
    ) -> Result<()> {
        state.merge(w,
                   &mut unit_a.filter_types(flags, true).iter(),
                   &mut unit_b.filter_types(flags, true).iter(),
                   |a, b| Type::cmp_id(a, b),
                   |w, state, a, b| Type::diff(w, state, unit_a, a, unit_b, b),
                   |w, state, a| a.print(w, state, unit_a),
                   |w, state, b| b.print(w, state, unit_b))?;
        state.merge(w,
                   &mut unit_a.filter_subprograms(flags, true).iter(),
                   &mut unit_b.filter_subprograms(flags, true).iter(),
                   |a, b| Subprogram::cmp_id(a, b),
                   |w, state, a, b| Subprogram::diff(w, state, unit_a, a, unit_b, b),
                   |w, state, a| a.print(w, state, unit_a),
                   |w, state, b| b.print(w, state, unit_b))?;
        state.merge(w,
                   &mut unit_a.filter_variables(flags, true).iter(),
                   &mut unit_b.filter_variables(flags, true).iter(),
                   |a, b| Variable::cmp_id(a, b),
                   |w, state, a, b| Variable::diff(w, state, unit_a, a, unit_b, b),
                   |w, state, a| a.print(w, state, unit_a),
                   |w, state, b| b.print(w, state, unit_b))?;
        Ok(())
    }
}

#[derive(Debug)]
enum TypeKind<'input> {
    Base(BaseType<'input>),
    Def(TypeDef<'input>),
    Struct(StructType<'input>),
    Union(UnionType<'input>),
    Enumeration(EnumerationType<'input>),
    Array(ArrayType<'input>),
    Subroutine(SubroutineType<'input>),
    Modifier(TypeModifier<'input>),
    Unimplemented(gimli::DwTag),
}

impl<'input> TypeKind<'input> {
    fn discriminant_value(&self) -> u8 {
        match *self {
            TypeKind::Base(..) => 0,
            TypeKind::Def(..) => 1,
            TypeKind::Struct(..) => 2,
            TypeKind::Union(..) => 3,
            TypeKind::Enumeration(..) => 4,
            TypeKind::Array(..) => 5,
            TypeKind::Subroutine(..) => 6,
            TypeKind::Modifier(..) => 7,
            TypeKind::Unimplemented(..) => 8,
        }
    }
}

#[derive(Debug)]
struct Type<'input> {
    offset: gimli::UnitOffset,
    kind: TypeKind<'input>,
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
    fn from_offset<'a>(
        unit: &'a Unit<'input>,
        offset: gimli::UnitOffset
    ) -> Option<&'a Type<'input>> {
        unit.types.get(&offset.0)
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        match self.kind {
            TypeKind::Base(ref val) => val.bit_size(unit),
            TypeKind::Def(ref val) => val.bit_size(unit),
            TypeKind::Struct(ref val) => val.bit_size(unit),
            TypeKind::Union(ref val) => val.bit_size(unit),
            TypeKind::Enumeration(ref val) => val.bit_size(unit),
            TypeKind::Array(ref val) => val.bit_size(unit),
            TypeKind::Subroutine(ref val) => val.bit_size(unit),
            TypeKind::Modifier(ref val) => val.bit_size(unit),
            TypeKind::Unimplemented(_) => None,
        }
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        match self.kind {
            TypeKind::Struct(ref val) => val.visit_members(f),
            TypeKind::Union(ref val) => val.visit_members(f),
            TypeKind::Enumeration(..) |
            TypeKind::Def(..) |
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Subroutine(..) |
            TypeKind::Modifier(..) |
            TypeKind::Unimplemented(_) => {}
        }
    }

    fn filter(&self, flags: &Flags) -> bool {
        match self.kind {
            TypeKind::Def(ref val) => val.filter(flags),
            TypeKind::Struct(ref val) => val.filter(flags),
            TypeKind::Union(ref val) => val.filter(flags),
            TypeKind::Enumeration(ref val) => val.filter(flags),
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Subroutine(..) |
            TypeKind::Modifier(..) |
            TypeKind::Unimplemented(_) => flags.name.is_none(),
        }
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        match self.kind {
            TypeKind::Def(ref val) => val.print(w, state, unit),
            TypeKind::Struct(ref val) => val.print(w, state, unit),
            TypeKind::Union(ref val) => val.print(w, state, unit),
            TypeKind::Enumeration(ref val) => val.print(w, state),
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Subroutine(..) |
            TypeKind::Modifier(..) |
            TypeKind::Unimplemented(..) => Err(format!("can't print {:?}", self).into()),
        }
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState, unit: &Unit) -> Result<()> {
        match self.kind {
            TypeKind::Base(ref val) => val.print_ref(w),
            TypeKind::Def(ref val) => val.print_ref(w),
            TypeKind::Struct(ref val) => val.print_ref(w),
            TypeKind::Union(ref val) => val.print_ref(w),
            TypeKind::Enumeration(ref val) => val.print_ref(w),
            TypeKind::Array(ref val) => val.print_ref(w, state, unit),
            TypeKind::Subroutine(ref val) => val.print_ref(w, state, unit),
            TypeKind::Modifier(ref val) => val.print_ref(w, state, unit),
            TypeKind::Unimplemented(..) => Err(format!("can't print_ref {:?}", self).into()),
        }
    }

    fn print_ref_from_offset(
        w: &mut Write,
        state: &PrintState,
        unit: &Unit,
        offset: gimli::UnitOffset
    ) -> Result<()> {
        match Type::from_offset(unit, offset) {
            Some(ty) => ty.print_ref(w, state, unit)?,
            None => write!(w, "<invalid-type>")?,
        }
        Ok(())
    }

    fn is_anon(&self) -> bool {
        match self.kind {
            TypeKind::Struct(ref val) => val.is_anon(),
            TypeKind::Union(ref val) => val.is_anon(),
            TypeKind::Base(..) |
            TypeKind::Def(..) |
            TypeKind::Enumeration(..) |
            TypeKind::Array(..) |
            TypeKind::Subroutine(..) |
            TypeKind::Modifier(..) |
            TypeKind::Unimplemented(..) => false,
        }
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    /// This must only be called for types that have identifiers.
    fn cmp_id(type_a: &Type, type_b: &Type) -> cmp::Ordering {
        use TypeKind::*;
        match (&type_a.kind, &type_b.kind) {
            (&Def(ref a), &Def(ref b)) => TypeDef::cmp_id(a, b),
            (&Struct(ref a), &Struct(ref b)) => StructType::cmp_id(a, b),
            (&Union(ref a), &Union(ref b)) => UnionType::cmp_id(a, b),
            (&Enumeration(ref a), &Enumeration(ref b)) => EnumerationType::cmp_id(a, b),
            _ => {
                let discr_a = type_a.kind.discriminant_value();
                let discr_b = type_b.kind.discriminant_value();
                debug_assert!(discr_a != discr_b);
                discr_a.cmp(&discr_b)
            }
        }
    }

    fn equal_ref(unit_a: &Unit, type_a: &Type, unit_b: &Unit, type_b: &Type) -> bool {
        use TypeKind::*;
        match (&type_a.kind, &type_b.kind) {
            (&Base(ref a), &Base(ref b)) => BaseType::equal_ref(a, b),
            (&Def(ref a), &Def(ref b)) => TypeDef::equal_ref(a, b),
            (&Struct(ref a), &Struct(ref b)) => StructType::equal_ref(a, b),
            (&Union(ref a), &Union(ref b)) => UnionType::equal_ref(a, b),
            (&Enumeration(ref a), &Enumeration(ref b)) => EnumerationType::equal_ref(a, b),
            (&Array(ref a), &Array(ref b)) => ArrayType::equal_ref(unit_a, a, unit_b, b),
            (&Subroutine(ref a), &Subroutine(ref b)) => {
                SubroutineType::equal_ref(unit_a, a, unit_b, b)
            }
            (&Modifier(ref a), &Modifier(ref b)) => TypeModifier::equal_ref(unit_a, a, unit_b, b),
            _ => false,
        }
    }

    fn equal_ref_option(
        unit_a: &Unit,
        type_a: Option<&Type>,
        unit_b: &Unit,
        type_b: Option<&Type>
    ) -> bool {
        match (type_a, type_b) {
            (Some(a), Some(b)) => Type::equal_ref(unit_a, a, unit_b, b),
            (None, None) => true,
            _ => false,
        }
    }

    fn equal(unit_a: &Unit, type_a: &Type, unit_b: &Unit, type_b: &Type) -> bool {
        use TypeKind::*;
        match (&type_a.kind, &type_b.kind) {
            (&Base(ref a), &Base(ref b)) => BaseType::equal_ref(a, b),
            (&Def(ref a), &Def(ref b)) => TypeDef::equal(unit_a, a, unit_b, b),
            (&Struct(ref a), &Struct(ref b)) => StructType::equal(unit_a, a, unit_b, b),
            (&Union(ref a), &Union(ref b)) => UnionType::equal(unit_a, a, unit_b, b),
            (&Enumeration(ref a), &Enumeration(ref b)) => {
                EnumerationType::equal(unit_a, a, unit_b, b)
            }
            (&Array(ref a), &Array(ref b)) => ArrayType::equal_ref(unit_a, a, unit_b, b),
            (&Subroutine(ref a), &Subroutine(ref b)) => {
                SubroutineType::equal_ref(unit_a, a, unit_b, b)
            }
            (&Modifier(ref a), &Modifier(ref b)) => TypeModifier::equal_ref(unit_a, a, unit_b, b),
            _ => false,
        }
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        type_a: &Type,
        unit_b: &Unit,
        type_b: &Type
    ) -> Result<()> {
        use TypeKind::*;
        match (&type_a.kind, &type_b.kind) {
            (&Def(ref a), &Def(ref b)) => TypeDef::diff(w, state, unit_a, a, unit_b, b),
            (&Struct(ref a), &Struct(ref b)) => StructType::diff(w, state, unit_a, a, unit_b, b),
            (&Union(ref a), &Union(ref b)) => UnionType::diff(w, state, unit_a, a, unit_b, b),
            (&Enumeration(ref a), &Enumeration(ref b)) => {
                EnumerationType::diff(w, state, unit_a, a, unit_b, b)
            }
            _ => Err(format!("can't diff {:?}, {:?}", type_a, type_b).into()),
        }
    }
}

#[derive(Debug)]
struct TypeModifier<'input> {
    kind: TypeModifierKind,
    ty: Option<gimli::UnitOffset>,
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TypeModifierKind {
    Const,
    Pointer,
    Restrict,
}

impl<'input> TypeModifier<'input> {
    fn ty<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| Type::from_offset(unit, v))
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        if let Some(byte_size) = self.byte_size {
            return Some(byte_size * 8);
        }
        match self.kind {
            TypeModifierKind::Const |
            TypeModifierKind::Restrict => self.ty(unit).and_then(|v| v.bit_size(unit)),
            TypeModifierKind::Pointer => unit.address_size.map(|v| v * 8),
        }
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState, unit: &Unit) -> Result<()> {
        if let Some(name) = self.name {
            // Not sure namespace is required here.
            self.namespace.print(w)?;
            write!(w, "{}", name.to_string_lossy())?;
        } else {
            match self.kind {
                TypeModifierKind::Const => write!(w, "const ")?,
                TypeModifierKind::Pointer => write!(w, "* ")?,
                TypeModifierKind::Restrict => write!(w, "restrict ")?,
            }
            match self.ty {
                Some(ty) => Type::print_ref_from_offset(w, state, unit, ty)?,
                None => write!(w, "<unknown-type>")?,
            }
        }
        Ok(())
    }

    fn equal_ref(unit_a: &Unit, a: &TypeModifier, unit_b: &Unit, b: &TypeModifier) -> bool {
        if cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name) != cmp::Ordering::Equal {
            return false;
        }
        if a.kind != b.kind {
            return false;
        }
        Type::equal_ref_option(unit_a, a.ty(unit_a), unit_b, b.ty(unit_b))
    }
}

#[derive(Debug, Default)]
struct BaseType<'input> {
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
}

impl<'input> BaseType<'input> {
    fn bit_size(&self, _unit: &Unit) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon-base-type>")?,
        }
        Ok(())
    }

    fn equal_ref(a: &BaseType, b: &BaseType) -> bool {
        a.name.cmp(&b.name) == cmp::Ordering::Equal
    }
}

#[derive(Debug, Default)]
struct TypeDef<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input ffi::CStr>,
    ty: Option<gimli::UnitOffset>,
}

impl<'input> TypeDef<'input> {
    fn ty<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|t| Type::from_offset(unit, t))
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        self.ty(unit).and_then(|v| v.bit_size(unit))
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon-typedef>")?,
        }
        Ok(())
    }

    fn print_ty_anon(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line_start(w)?;
        write!(w, "type ")?;
        self.print_ref(w)?;
        write!(w, " = ")?;
        writeln!(w, "")?;
        Ok(())
    }

    fn print_ty_unknown(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line_start(w)?;
        write!(w, "type ")?;
        self.print_ref(w)?;
        write!(w, " = ")?;
        writeln!(w, "<unknown-type>")?;
        Ok(())
    }

    fn print_ty_name(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        ty: &Type
    ) -> Result<()> {
        state.line_start(w)?;
        write!(w, "type ")?;
        self.print_ref(w)?;
        write!(w, " = ")?;
        ty.print_ref(w, state, unit)?;
        writeln!(w, "")?;
        Ok(())
    }

    fn print_bit_size(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        if let Some(bit_size) = self.bit_size(unit) {
            state.line_start(w)?;
            writeln!(w, "size: {}", format_bit(bit_size))?;
        }
        Ok(())
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        if let Some(ty) = self.ty(unit) {
            if ty.is_anon() {
                self.print_ty_anon(w, state)?;
                state.indent(|state| ty.print(w, state, unit))?;
            } else {
                self.print_ty_name(w, state, unit, ty)?;
                state.indent(|state| self.print_bit_size(w, state, unit))?;
                writeln!(w, "")?;
            }
        } else {
            self.print_ty_unknown(w, state)?;
            writeln!(w, "")?;
        }
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &TypeDef, b: &TypeDef) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn equal_ref(a: &TypeDef, b: &TypeDef) -> bool {
        Self::cmp_id(a, b) == cmp::Ordering::Equal
    }

    fn equal(unit_a: &Unit, a: &TypeDef, unit_b: &Unit, b: &TypeDef) -> bool {
        // TODO: this may compare more than we print
        if Self::cmp_id(a, b) != cmp::Ordering::Equal {
            return false;
        }
        match (a.ty(unit_a), b.ty(unit_b)) {
            (Some(ty_a), Some(ty_b)) => Type::equal(unit_a, ty_a, unit_b, ty_b),
            (None, None) => true,
            _ => false,
        }
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &TypeDef,
        unit_b: &Unit,
        b: &TypeDef
    ) -> Result<()> {
        if Self::equal(unit_a, a, unit_b, b) {
            return Ok(());
        }

        match (a.ty(unit_a), b.ty(unit_b)) {
            (Some(ty_a), Some(ty_b)) => {
                match (ty_a.is_anon(), ty_b.is_anon()) {
                    (true, true) => {
                        state.prefix_equal(|state| a.print_ty_anon(w, &mut state.a))?;
                        state.indent(|state| Type::diff(w, state, unit_a, ty_a, unit_b, ty_b))?;
                    }
                    (true, false) | (false, true) => {
                        state.prefix_diff(|state| {
                                a.print(w, &mut state.a, unit_a)?;
                                b.print(w, &mut state.b, unit_b)
                            })?;
                    }
                    (false, false) => {
                        state.diff(w,
                                  |w, state| a.print_ty_name(w, state, unit_a, ty_a),
                                  |w, state| b.print_ty_name(w, state, unit_b, ty_b))?;
                        state.indent(|state| {
                                if a.bit_size(unit_a) == b.bit_size(unit_b) {
                                    state.prefix_equal(|state| {
                                        a.print_bit_size(w, &mut state.a, unit_a)
                                    })
                                } else {
                                    state.prefix_diff(|state| {
                                        a.print_bit_size(w, &mut state.a, unit_a)?;
                                        b.print_bit_size(w, &mut state.b, unit_b)
                                    })
                                }
                            })?;
                        writeln!(w, "")?;
                    }
                }
            }
            (Some(_), None) | (None, Some(_)) => {
                state.prefix_diff(|state| {
                        a.print(w, &mut state.a, unit_a)?;
                        b.print(w, &mut state.b, unit_b)
                    })?;
            }
            (None, None) => {
                state.prefix_equal(|state| a.print_ty_unknown(w, &mut state.a))?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct StructType<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
    declaration: bool,
    members: Vec<Member<'input>>,
}

impl<'input> StructType<'input> {
    fn bit_size(&self, _unit: &Unit) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        self.print_name(w, state)?;
        state.indent(|state| {
            self.print_byte_size(w, state)?;
            self.print_declaration(w, state)?;
            self.print_members_label(w, state)?;
            state.indent(|state| self.print_members(w, state, unit, Some(0)))?;
            writeln!(w, "")?;
            Ok(())
        })
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &StructType,
        unit_b: &Unit,
        b: &StructType
    ) -> Result<()> {
        if Self::equal(unit_a, a, unit_b, b) {
            return Ok(());
        }

        // The names should be the same, but we can't be sure.
        state.diff(w,
                  |w, state| a.print_name(w, state),
                  |w, state| b.print_name(w, state))?;

        state.indent(|state| {
                if a.byte_size == b.byte_size {
                    state.prefix_equal(|state| a.print_byte_size(w, &mut state.a))?;
                } else {
                    state.prefix_diff(|state| {
                            a.print_byte_size(w, &mut state.a)?;
                            b.print_byte_size(w, &mut state.b)
                        })?;
                }

                if a.declaration == b.declaration {
                    state.prefix_equal(|state| a.print_declaration(w, &mut state.a))?;
                } else {
                    state.prefix_diff(|state| {
                            a.print_declaration(w, &mut state.a)?;
                            b.print_declaration(w, &mut state.b)
                        })?;
                }

                if a.members.is_empty() == b.members.is_empty() {
                    state.prefix_equal(|state| a.print_members_label(w, &mut state.a))?;
                } else {
                    state.prefix_diff(|state| {
                            a.print_members_label(w, &mut state.a)?;
                            b.print_members_label(w, &mut state.b)
                        })?;
                }

                state.indent(|state| {
                        Self::diff_members(w, state, unit_a, a, Some(0), unit_b, b, Some(0))
                    })?;

                writeln!(w, "")?;
                Ok(())
            })?;

        Ok(())
    }

    fn print_name(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line_start(w)?;
        self.print_ref(w)?;
        writeln!(w, "")?;
        Ok(())
    }

    fn print_byte_size(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size {
            state.line_start(w)?;
            writeln!(w, "size: {}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if self.declaration {
            state.line_start(w)?;
            writeln!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_members_label(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if !self.members.is_empty() {
            state.line_start(w)?;
            writeln!(w, "members:")?;
        }
        Ok(())
    }

    fn print_members(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        mut bit_offset: Option<u64>
    ) -> Result<()> {
        for member in &self.members {
            member.print(w, state, unit, &mut bit_offset)?;
        }
        Member::print_padding(w, state, self.padding(bit_offset))?;
        Ok(())
    }

    fn diff_members(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &StructType,
        mut bit_offset_a: Option<u64>,
        unit_b: &Unit,
        b: &StructType,
        mut bit_offset_b: Option<u64>
    ) -> Result<()> {
        // Enumerate members and sort by name. Exclude anonymous members.
        let mut members_a =
            a.members.iter().enumerate().filter(|a| a.1.name.is_some()).collect::<Vec<_>>();
        members_a.sort_by(|x, y| Member::cmp_id(x.1, y.1));
        let mut members_b =
            b.members.iter().enumerate().filter(|b| b.1.name.is_some()).collect::<Vec<_>>();
        members_b.sort_by(|x, y| Member::cmp_id(x.1, y.1));

        // Find pairs of members with the same name.
        let mut pairs = Vec::new();
        for m in MergeIterator::new(members_a.iter(),
                                    members_b.iter(),
                                    |a, b| Member::cmp_id(a.1, b.1)) {
            if let MergeResult::Both(a, b) = m {
                pairs.push((a, b));
            }
        }
        // TODO: For remaining members, find pairs of members with the same type.
        // This should also handle matching up anonymous members.

        // Sort pairs by the indices and equality.
        pairs.sort_by(|&(xa, xb), &(ya, yb)| {
            match (xa.0.cmp(&ya.0), xb.0.cmp(&yb.0)) {
                (cmp::Ordering::Less, cmp::Ordering::Less) => cmp::Ordering::Less,
                (cmp::Ordering::Greater, cmp::Ordering::Greater) => cmp::Ordering::Greater,
                (cmp_a, _cmp_b) => {
                    match (Member::equal(unit_a, xa.1, unit_b, xb.1),
                           Member::equal(unit_a, ya.1, unit_b, yb.1)) {
                        (true, false) => cmp::Ordering::Less,
                        (false, true) => cmp::Ordering::Greater,
                        _ => cmp_a,
                    }
                }
            }
        });

        // Loop through the pairs.
        let mut index_a = 0;
        let mut index_b = 0;
        let mut iter_a = a.members.iter();
        let mut iter_b = b.members.iter();
        for &(a, b) in &pairs {
            // Skip pairs that are already partially printed.
            if a.0 < index_a || b.0 < index_b {
                continue;
            }

            // Print members leading up to the pair.
            while index_a < a.0 {
                if let Some(a) = iter_a.next() {
                    state.prefix_less(|state| a.print(w, state, unit_a, &mut bit_offset_a))?;
                }
                index_a = index_a + 1;
            }
            while index_b < b.0 {
                if let Some(b) = iter_b.next() {
                    state.prefix_greater(|state| b.print(w, state, unit_b, &mut bit_offset_b))?;
                }
                index_b = index_b + 1;
            }

            // Diff the pair.
            if let (Some(a), Some(b)) = (iter_a.next(), iter_b.next()) {
                state.prefix_diff(|state| {
                        Member::diff(w,
                                     state,
                                     unit_a,
                                     a,
                                     &mut bit_offset_a,
                                     unit_b,
                                     b,
                                     &mut bit_offset_b)
                    })?;
            }
            index_a = index_a + 1;
            index_b = index_b + 1;
        }

        // Print trailing members.
        for a in iter_a {
            state.prefix_less(|state| a.print(w, state, unit_a, &mut bit_offset_a))?;
        }
        for b in iter_b {
            state.prefix_greater(|state| b.print(w, state, unit_b, &mut bit_offset_b))?;
        }

        let padding_a = a.padding(bit_offset_a);
        let padding_b = b.padding(bit_offset_b);
        if padding_a == padding_b {
            state.prefix_equal(|state| Member::print_padding(w, &mut state.a, padding_a))?;
        } else {
            state.prefix_diff(|state| {
                    Member::print_padding(w, &mut state.a, padding_a)?;
                    Member::print_padding(w, &mut state.b, padding_b)
                })?;
        }

        Ok(())
    }

    // Returns (offset, size) of padding.
    fn padding(&self, bit_offset: Option<u64>) -> Option<(u64, u64)> {
        if let (Some(bit_offset), Some(size)) = (bit_offset, self.byte_size) {
            if bit_offset < size * 8 {
                return Some((bit_offset, size * 8 - bit_offset));
            }
        }
        None
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        write!(w, "struct ")?;
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn equal_ref(a: &StructType, b: &StructType) -> bool {
        Self::cmp_id(a, b) == cmp::Ordering::Equal
    }

    fn is_anon(&self) -> bool {
        self.name.is_none()
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &StructType, b: &StructType) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn equal(unit_a: &Unit, a: &StructType, unit_b: &Unit, b: &StructType) -> bool {
        Self::cmp_id(a, b) == cmp::Ordering::Equal && a.byte_size == b.byte_size &&
        a.declaration == b.declaration && Self::equal_members(unit_a, a, unit_b, b)
    }

    fn equal_members(
        unit_a: &Unit,
        struct_a: &StructType,
        unit_b: &Unit,
        struct_b: &StructType
    ) -> bool {
        if struct_a.members.len() != struct_b.members.len() {
            return false;
        }
        for (a, b) in struct_a.members.iter().zip(struct_b.members.iter()) {
            if !Member::equal(unit_a, a, unit_b, b) {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, Default)]
struct UnionType<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
    declaration: bool,
    members: Vec<Member<'input>>,
}

impl<'input> UnionType<'input> {
    fn bit_size(&self, _unit: &Unit) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        self.print_name(w, state)?;
        state.indent(|state| {
            self.print_byte_size(w, state)?;
            self.print_declaration(w, state)?;
            self.print_members_label(w, state)?;
            state.indent(|state| self.print_members(w, state, unit, Some(0)))?;
            writeln!(w, "")?;
            Ok(())
        })
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &UnionType,
        unit_b: &Unit,
        b: &UnionType
    ) -> Result<()> {
        if Self::equal(unit_a, a, unit_b, b) {
            return Ok(());
        }

        // The names should be the same, but we can't be sure.
        state.diff(w,
                  |w, state| a.print_name(w, state),
                  |w, state| b.print_name(w, state))?;

        state.indent(|state| {
                if a.byte_size == b.byte_size {
                    state.prefix_equal(|state| a.print_byte_size(w, &mut state.a))?;
                } else {
                    state.prefix_diff(|state| {
                            a.print_byte_size(w, &mut state.a)?;
                            b.print_byte_size(w, &mut state.b)
                        })?;
                }

                if a.declaration == b.declaration {
                    state.prefix_equal(|state| a.print_declaration(w, &mut state.a))?;
                } else {
                    state.prefix_diff(|state| {
                            a.print_declaration(w, &mut state.a)?;
                            b.print_declaration(w, &mut state.b)
                        })?;
                }

                if a.members.is_empty() == b.members.is_empty() {
                    state.prefix_equal(|state| a.print_members_label(w, &mut state.a))?;
                } else {
                    state.prefix_diff(|state| {
                            a.print_members_label(w, &mut state.a)?;
                            b.print_members_label(w, &mut state.b)
                        })?;
                }

                state.indent(|state| {
                        Self::diff_members(w, state, unit_a, a, Some(0), unit_b, b, Some(0))
                    })?;

                writeln!(w, "")?;
                Ok(())
            })?;

        Ok(())
    }

    fn print_name(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line_start(w)?;
        self.print_ref(w)?;
        writeln!(w, "")?;
        Ok(())
    }

    fn print_byte_size(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size {
            state.line_start(w)?;
            writeln!(w, "size: {}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if self.declaration {
            state.line_start(w)?;
            writeln!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_members_label(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if !self.members.is_empty() {
            state.line_start(w)?;
            writeln!(w, "members:")?;
        }
        Ok(())
    }

    fn print_members(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        bit_offset: Option<u64>
    ) -> Result<()> {
        for member in &self.members {
            let mut bit_offset = bit_offset;
            member.print(w, state, unit, &mut bit_offset)?;
        }
        // TODO: trailing padding?
        Ok(())
    }

    fn diff_members(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &UnionType,
        bit_offset_a: Option<u64>,
        unit_b: &Unit,
        b: &UnionType,
        bit_offset_b: Option<u64>
    ) -> Result<()> {
        // Sort by name so that merging will compare members with the same name
        // even if they were reordered.
        // TODO: is this smart enough? maybe take type into account too.
        let mut members_a = a.members.iter().collect::<Vec<_>>();
        members_a.sort_by(|x, y| Member::cmp_id(x, y));
        let mut members_b = b.members.iter().collect::<Vec<_>>();
        members_b.sort_by(|x, y| Member::cmp_id(x, y));

        state.merge(w,
                   &mut members_a.iter(),
                   &mut members_b.iter(),
                   |a, b| Member::cmp_id(a, b),
                   |w, state, a, b| {
                Member::diff(w,
                             state,
                             unit_a,
                             a,
                             &mut bit_offset_a.clone(),
                             unit_b,
                             b,
                             &mut bit_offset_b.clone())
            },
                   |w, state, a| a.print(w, state, unit_a, &mut bit_offset_a.clone()),
                   |w, state, b| b.print(w, state, unit_b, &mut bit_offset_b.clone()))?;
        // TODO: trailing padding?
        Ok(())
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        write!(w, "union ")?;
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn equal_ref(a: &UnionType, b: &UnionType) -> bool {
        Self::cmp_id(a, b) == cmp::Ordering::Equal
    }

    fn is_anon(&self) -> bool {
        self.name.is_none()
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &UnionType, b: &UnionType) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn equal(unit_a: &Unit, a: &UnionType, unit_b: &Unit, b: &UnionType) -> bool {
        Self::cmp_id(a, b) == cmp::Ordering::Equal && a.byte_size == b.byte_size &&
        a.declaration == b.declaration && Self::equal_members(unit_a, a, unit_b, b)
    }

    fn equal_members(
        unit_a: &Unit,
        union_a: &UnionType,
        unit_b: &Unit,
        union_b: &UnionType
    ) -> bool {
        if union_a.members.len() != union_b.members.len() {
            return false;
        }
        for (a, b) in union_a.members.iter().zip(union_b.members.iter()) {
            if !Member::equal(unit_a, a, unit_b, b) {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, Default)]
struct Member<'input> {
    name: Option<&'input ffi::CStr>,
    // TODO: treat padding as typeless member?
    ty: Option<gimli::UnitOffset>,
    // Defaults to 0, so always present.
    bit_offset: u64,
    bit_size: Option<u64>,
}

impl<'input> Member<'input> {
    fn ty<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|t| Type::from_offset(unit, t))
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        if self.bit_size.is_some() {
            self.bit_size
        } else {
            self.ty(unit).and_then(|v| v.bit_size(unit))
        }
    }

    fn print(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        end_bit_offset: &mut Option<u64>
    ) -> Result<()> {
        Self::print_padding(w, state, self.padding(*end_bit_offset))?;
        self.print_name(w, state, unit, end_bit_offset)?;
        if self.is_inline(unit) {
            self.print_inline(w, state, unit)?;
        }
        Ok(())
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Member,
        end_bit_offset_a: &mut Option<u64>,
        unit_b: &Unit,
        b: &Member,
        end_bit_offset_b: &mut Option<u64>
    ) -> Result<()> {
        let padding_a = a.padding(*end_bit_offset_a);
        let padding_b = b.padding(*end_bit_offset_b);
        if padding_a == padding_b {
            state.prefix_equal(|state| Self::print_padding(w, &mut state.a, padding_a))?;
        } else {
            state.prefix_diff(|state| {
                    Self::print_padding(w, &mut state.a, padding_a)?;
                    Self::print_padding(w, &mut state.b, padding_b)
                })?;
        }

        state.diff(w,
                  |w, state| a.print_name(w, state, unit_a, end_bit_offset_a),
                  |w, state| b.print_name(w, state, unit_b, end_bit_offset_b))?;

        match (a.is_inline(unit_a), b.is_inline(unit_b)) {
            (true, true) => {
                Self::diff_inline(w, state, unit_a, a, unit_b, b)?;
            }
            (true, false) => {
                state.prefix_less(|state| a.print_inline(w, state, unit_a))?;
            }
            (false, true) => {
                state.prefix_greater(|state| b.print_inline(w, state, unit_b))?;
            }
            (false, false) => {}
        }

        Ok(())
    }

    // Returns (offset, size) of padding.
    fn padding(&self, end_bit_offset: Option<u64>) -> Option<(u64, u64)> {
        if let Some(end_bit_offset) = end_bit_offset {
            if self.bit_offset > end_bit_offset {
                return Some((end_bit_offset, self.bit_offset - end_bit_offset));
            }
        }
        None
    }

    fn print_padding(
        w: &mut Write,
        state: &mut PrintState,
        padding: Option<(u64, u64)>
    ) -> Result<()> {
        if let Some((padding_bit_offset, padding_bit_size)) = padding {
            state.line_start(w)?;
            writeln!(w,
                     "{}[{}]\t<padding>",
                     format_bit(padding_bit_offset),
                     format_bit(padding_bit_size))?;
        }
        Ok(())
    }

    fn print_name(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        end_bit_offset: &mut Option<u64>
    ) -> Result<()> {
        state.line_start(w)?;
        write!(w, "{}", format_bit(self.bit_offset))?;
        match self.bit_size(unit) {
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
        if let Some(ty) = self.ty(unit) {
            write!(w, ": ")?;
            ty.print_ref(w, state, unit)?;
            writeln!(w, "")?;
        } else {
            writeln!(w, ": <invalid-type>")?;
        }
        Ok(())
    }

    fn is_inline(&self, unit: &Unit) -> bool {
        match self.name {
            Some(s) => {
                if s.to_bytes().starts_with(b"RUST$ENCODED$ENUM$") {
                    return true;
                }
            }
            None => return true,
        };
        if let Some(ty) = self.ty(unit) {
            ty.is_anon()
        } else {
            false
        }
    }

    fn print_inline(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        if let Some(ty) = self.ty(unit) {
            match ty.kind {
                TypeKind::Struct(ref t) => {
                    return state.indent(|state| {
                        t.print_members(w, state, unit, Some(self.bit_offset))
                    });
                }
                TypeKind::Union(ref t) => {
                    return state.indent(|state| {
                        t.print_members(w, state, unit, Some(self.bit_offset))
                    });
                }
                _ => {
                    debug!("unknown anon member: {:?}", ty);
                }
            }
        }
        Ok(())
    }

    fn diff_inline(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Member,
        unit_b: &Unit,
        b: &Member
    ) -> Result<()> {
        if let (Some(ty_a), Some(ty_b)) = (a.ty(unit_a), b.ty(unit_b)) {
            match (&ty_a.kind, &ty_b.kind) {
                (&TypeKind::Struct(ref t_a), &TypeKind::Struct(ref t_b)) => {
                    return state.indent(|state| {
                        StructType::diff_members(w,
                                                 state,
                                                 unit_a,
                                                 t_a,
                                                 Some(a.bit_offset),
                                                 unit_b,
                                                 t_b,
                                                 Some(b.bit_offset))
                    });
                }
                (&TypeKind::Union(ref t_a), &TypeKind::Union(ref t_b)) => {
                    return state.indent(|state| {
                        UnionType::diff_members(w,
                                                state,
                                                unit_a,
                                                t_a,
                                                Some(a.bit_offset),
                                                unit_b,
                                                t_b,
                                                Some(b.bit_offset))
                    });
                }
                _ => {}
            }
        }
        state.prefix_diff(|state| {
            a.print_inline(w, &mut state.a, unit_a)?;
            b.print_inline(w, &mut state.b, unit_b)?;
            Ok(())
        })
    }

    fn cmp_id(a: &Member, b: &Member) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }

    fn equal(unit_a: &Unit, a: &Member, unit_b: &Unit, b: &Member) -> bool {
        // FIXME: lots wrong here
        if Self::cmp_id(a, b) != cmp::Ordering::Equal {
            return false;
        }
        if a.bit_offset != b.bit_offset {
            return false;
        }
        if a.bit_size != b.bit_size {
            return false;
        }
        // FIXME: should use equal_ref for non-inline members
        match (a.ty(unit_a), b.ty(unit_b)) {
            (Some(ty_a), Some(ty_b)) => Type::equal(unit_a, ty_a, unit_b, ty_b),
            (None, None) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Default)]
struct EnumerationType<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input ffi::CStr>,
    byte_size: Option<u64>,
    enumerators: Vec<Enumerator<'input>>,
}

impl<'input> EnumerationType<'input> {
    fn bit_size(&self, _unit: &Unit) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line_start(w)?;
        self.print_ref(w)?;
        writeln!(w, "")?;

        state.indent(|state| {
            if let Some(size) = self.byte_size {
                state.line_start(w)?;
                writeln!(w, "size: {}", size)?;
            }

            if !self.enumerators.is_empty() {
                state.line_start(w)?;
                writeln!(w, "enumerators:")?;
                state.indent(|state| {
                        for enumerator in &self.enumerators {
                            enumerator.print(w, state)?;
                        }
                        Ok(())
                    })?;
            }

            writeln!(w, "")?;
            Ok(())
        })
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        write!(w, "enum ")?;
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &EnumerationType, b: &EnumerationType) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn equal_ref(a: &EnumerationType, b: &EnumerationType) -> bool {
        Self::cmp_id(a, b) == cmp::Ordering::Equal
    }

    fn equal(unit_a: &Unit, a: &EnumerationType, unit_b: &Unit, b: &EnumerationType) -> bool {
        Self::cmp_id(a, b) == cmp::Ordering::Equal && a.byte_size == b.byte_size &&
        Self::equal_enumerators(unit_a, a, unit_b, b)
    }

    fn equal_enumerators(
        unit_a: &Unit,
        enum_a: &EnumerationType,
        unit_b: &Unit,
        enum_b: &EnumerationType
    ) -> bool {
        if enum_a.enumerators.len() != enum_b.enumerators.len() {
            return false;
        }
        for (a, b) in enum_a.enumerators.iter().zip(enum_b.enumerators.iter()) {
            if !Enumerator::equal(unit_a, a, unit_b, b) {
                return false;
            }
        }
        true
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &EnumerationType,
        unit_b: &Unit,
        b: &EnumerationType
    ) -> Result<()> {
        if Self::equal(unit_a, a, unit_b, b) {
            return Ok(());
        }
        // TODO
        state.prefix_diff(|state| {
                a.print(w, &mut state.a)?;
                b.print(w, &mut state.b)
            })?;
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Enumerator<'input> {
    name: Option<&'input ffi::CStr>,
    value: Option<i64>,
}

impl<'input> Enumerator<'input> {
    fn print(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        state.line_start(w)?;
        self.print_ref(w)?;
        if let Some(value) = self.value {
            write!(w, "({})", value)?;
        }
        writeln!(w, "")?;
        Ok(())
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn equal(_unit_a: &Unit, _a: &Enumerator, _unit_b: &Unit, _b: &Enumerator) -> bool {
        // TODO
        true
    }
}

#[derive(Debug, Default)]
struct ArrayType<'input> {
    ty: Option<gimli::UnitOffset>,
    count: Option<u64>,
    phantom: std::marker::PhantomData<&'input [u8]>,
}

impl<'input> ArrayType<'input> {
    fn ty<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| unit.types.get(&v.0))
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        if let (Some(ty), Some(count)) = (self.ty(unit), self.count) {
            ty.bit_size(unit).map(|v| v * count)
        } else {
            None
        }
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState, unit: &Unit) -> Result<()> {
        write!(w, "[")?;
        match self.ty {
            Some(ty) => Type::print_ref_from_offset(w, state, unit, ty)?,
            None => write!(w, "<unknown-type>")?,
        }
        if let Some(count) = self.count {
            write!(w, "; {}", count)?;
        }
        write!(w, "]")?;
        Ok(())
    }

    fn equal_ref(unit_a: &Unit, a: &ArrayType, unit_b: &Unit, b: &ArrayType) -> bool {
        if a.count != b.count {
            return false;
        }
        Type::equal_ref_option(unit_a, a.ty(unit_a), unit_b, b.ty(unit_b))
    }
}

#[derive(Debug, Default)]
struct SubroutineType<'input> {
    parameters: Vec<Parameter<'input>>,
    return_type: Option<gimli::UnitOffset>,
}

impl<'input> SubroutineType<'input> {
    fn bit_size(&self, _unit: &Unit) -> Option<u64> {
        None
    }

    fn return_type<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.return_type.and_then(|v| unit.types.get(&v.0))
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState, unit: &Unit) -> Result<()> {
        let mut first = true;
        write!(w, "(")?;
        for parameter in &self.parameters {
            if first {
                first = false;
            } else {
                write!(w, ", ")?;
            }
            parameter.print(w, state, unit)?;
        }
        write!(w, ")")?;

        if let Some(return_type) = self.return_type(unit) {
            write!(w, " -> ")?;
            return_type.print_ref(w, state, unit)?;
        }
        Ok(())
    }

    fn equal_ref(
        unit_a: &Unit,
        sub_a: &SubroutineType,
        unit_b: &Unit,
        sub_b: &SubroutineType
    ) -> bool {
        if sub_a.parameters.len().cmp(&sub_b.parameters.len()) != cmp::Ordering::Equal {
            return false;
        }
        for (a, b) in sub_a.parameters.iter().zip(sub_b.parameters.iter()) {
            if !Parameter::equal(unit_a, a, unit_b, b) {
                return false;
            }
        }
        Type::equal_ref_option(unit_a,
                               sub_a.return_type(unit_a),
                               unit_b,
                               sub_b.return_type(unit_b))
    }
}

#[derive(Debug)]
struct Subprogram<'input> {
    offset: gimli::UnitOffset,
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input ffi::CStr>,
    linkage_name: Option<&'input ffi::CStr>,
    low_pc: Option<u64>,
    high_pc: Option<u64>,
    size: Option<u64>,
    inline: bool,
    declaration: bool,
    parameters: Vec<Parameter<'input>>,
    return_type: Option<gimli::UnitOffset>,
    inlined_subroutines: Vec<InlinedSubroutine<'input>>,
    variables: Vec<Variable<'input>>,
}

impl<'input> Subprogram<'input> {
    fn from_offset<'a>(
        unit: &'a Unit<'input>,
        offset: gimli::UnitOffset
    ) -> Option<&'a Subprogram<'input>> {
        unit.subprograms.get(&offset.0)
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line_start(w)?;
        write!(w, "fn ")?;
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        writeln!(w, "")?;

        state.indent(|state| {
            if let Some(linkage_name) = self.linkage_name {
                state.line_start(w)?;
                writeln!(w, "linkage name: {}", linkage_name.to_string_lossy())?;
            }

            if let (Some(low_pc), Some(high_pc)) = (self.low_pc, self.high_pc) {
                if high_pc > low_pc {
                    state.line_start(w)?;
                    writeln!(w, "address: 0x{:x}-0x{:x}", low_pc, high_pc - 1)?;
                } else {
                    state.line_start(w)?;
                    writeln!(w, "address: 0x{:x}", low_pc)?;
                }
            } else if !self.inline && !self.declaration {
                debug!("non-inline subprogram with no address");
            }

            if let Some(size) = self.size {
                state.line_start(w)?;
                writeln!(w, "size: {}", size)?;
            }

            if self.inline {
                state.line_start(w)?;
                writeln!(w, "inline: yes")?;
            }
            if self.declaration {
                state.line_start(w)?;
                writeln!(w, "declaration: yes")?;
            }

            if let Some(return_type) = self.return_type {
                state.line_start(w)?;
                writeln!(w, "return type:")?;
                state.indent(|state| {
                        state.line_start(w)?;
                        match Type::from_offset(unit, return_type).and_then(|t| t.bit_size(unit)) {
                            Some(bit_size) => write!(w, "[{}]", format_bit(bit_size))?,
                            None => write!(w, "[??]")?,
                        }
                        write!(w, "\t")?;
                        Type::print_ref_from_offset(w, state, unit, return_type)?;
                        writeln!(w, "")?;
                        Ok(())
                    })?;
            }

            if !self.parameters.is_empty() {
                state.line_start(w)?;
                writeln!(w, "parameters:")?;
                state.indent(|state| {
                        for parameter in &self.parameters {
                            state.line_start(w)?;
                            match parameter.bit_size(unit) {
                                Some(bit_size) => write!(w, "[{}]", format_bit(bit_size))?,
                                None => write!(w, "[??]")?,
                            }
                            write!(w, "\t")?;
                            parameter.print(w, state, unit)?;
                            writeln!(w, "")?;
                        }
                        Ok(())
                    })?;
            }

            if state.flags.inline_depth > 0 && !self.inlined_subroutines.is_empty() {
                state.line_start(w)?;
                writeln!(w, "inlined subroutines:")?;
                state.indent(|state| {
                        for subroutine in &self.inlined_subroutines {
                            subroutine.print(w, state, unit, 1)?;
                        }
                        Ok(())
                    })?;
            }

            if let (Some(low_pc), Some(high_pc)) = (self.low_pc, self.high_pc) {
                if low_pc != 0 && state.flags.calls {
                    let calls =
                        disassemble(state.file.machine, &state.file.region, low_pc, high_pc);
                    if !calls.is_empty() {
                        state.line_start(w)?;
                        writeln!(w, "calls:")?;
                        state.indent(|state| {
                                for call in &calls {
                                    state.line_start(w)?;
                                    write!(w, "0x{:x}", call)?;
                                    if let Some(subprogram) = state.all_subprograms.get(call) {
                                        write!(w, " ")?;
                                        subprogram.print_ref(w)?;
                                    }
                                    writeln!(w, "")?;
                                }
                                Ok(())
                            })?;
                    }
                }
            }

            writeln!(w, "")?;
            Ok(())
        })
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    /// Compare the identifying information of two subprograms.
    /// This can be used to sort, and to determine if two subprograms refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &Subprogram, b: &Subprogram) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn equal(a: &Subprogram, b: &Subprogram, _state: &DiffState) -> bool {
        if Self::cmp_id(a, b) != cmp::Ordering::Equal {
            return false;
        }
        // TODO
        true
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Subprogram,
        unit_b: &Unit,
        b: &Subprogram
    ) -> Result<()> {
        if Self::equal(a, b, state) {
            return Ok(());
        }
        // TODO
        state.prefix_diff(|state| {
                a.print(w, &mut state.a, unit_a)?;
                b.print(w, &mut state.b, unit_b)
            })?;
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Parameter<'input> {
    name: Option<&'input ffi::CStr>,
    ty: Option<gimli::UnitOffset>,
}

impl<'input> Parameter<'input> {
    fn ty<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| Type::from_offset(unit, v))
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        self.ty(unit).and_then(|t| t.bit_size(unit))
    }

    fn print(&self, w: &mut Write, state: &PrintState, unit: &Unit) -> Result<()> {
        if let Some(name) = self.name {
            write!(w, "{}: ", name.to_string_lossy())?;
        }
        match self.ty(unit) {
            Some(ty) => ty.print_ref(w, state, unit)?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn equal(unit_a: &Unit, a: &Parameter, unit_b: &Unit, b: &Parameter) -> bool {
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            return false;
        }
        Type::equal_ref_option(unit_a, a.ty(unit_a), unit_b, b.ty(unit_b))
    }
}

#[derive(Debug, Default)]
struct InlinedSubroutine<'input> {
    abstract_origin: Option<gimli::UnitOffset>,
    size: Option<u64>,
    inlined_subroutines: Vec<InlinedSubroutine<'input>>,
    variables: Vec<Variable<'input>>,
}

impl<'input> InlinedSubroutine<'input> {
    fn print(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        depth: usize
    ) -> Result<()> {
        state.line_start(w)?;
        match self.size {
            Some(size) => write!(w, "[{}]", size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        match self.abstract_origin.and_then(|v| Subprogram::from_offset(unit, v)) {
            Some(subprogram) => subprogram.print_ref(w)?,
            None => write!(w, "<anon>")?,
        }
        writeln!(w, "")?;

        if state.flags.inline_depth > depth {
            state.indent(|state| {
                    for subroutine in &self.inlined_subroutines {
                        subroutine.print(w, state, unit, depth + 1)?;
                    }
                    Ok(())
                })?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Variable<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input ffi::CStr>,
    linkage_name: Option<&'input ffi::CStr>,
    ty: Option<gimli::UnitOffset>,
    declaration: bool,
}

impl<'input> Variable<'input> {
    fn ty<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| Type::from_offset(unit, v))
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        self.ty(unit).and_then(|t| t.bit_size(unit))
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line_start(w)?;
        write!(w, "var ")?;
        self.print_ref(w)?;
        write!(w, ": ")?;
        match self.ty {
            Some(offset) => Type::print_ref_from_offset(w, state, unit, offset)?,
            None => write!(w, "<anon>")?,
        }
        writeln!(w, "")?;

        state.indent(|state| {
            if let Some(linkage_name) = self.linkage_name {
                state.line_start(w)?;
                writeln!(w, "linkage name: {}", linkage_name.to_string_lossy())?;
            }

            if let Some(bit_size) = self.bit_size(unit) {
                state.line_start(w)?;
                writeln!(w, "size: {}", format_bit(bit_size))?;
            } else if !self.declaration {
                debug!("variable with no size");
            }

            if self.declaration {
                state.line_start(w)?;
                writeln!(w, "declaration: yes")?;
            }

            writeln!(w, "")?;
            Ok(())
        })
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", name.to_string_lossy())?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    /// Compare the identifying information of two variables.
    /// This can be used to sort, and to determine if two variables refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &Variable, b: &Variable) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn equal(a: &Variable, b: &Variable, _state: &DiffState) -> bool {
        if Self::cmp_id(a, b) != cmp::Ordering::Equal {
            return false;
        }
        // TODO
        true
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Variable,
        unit_b: &Unit,
        b: &Variable
    ) -> Result<()> {
        if Self::equal(a, b, state) {
            return Ok(());
        }
        // TODO
        state.prefix_diff(|state| {
                a.print(w, &mut state.a, unit_a)?;
                b.print(w, &mut state.b, unit_b)
            })?;
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

            for instruction in &mnemonic.instructions {
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
            if let panopticon::Rvalue::Constant { value, .. } = target {
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
