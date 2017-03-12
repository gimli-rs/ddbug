extern crate gimli;
#[macro_use]
extern crate log;
extern crate memmap;
extern crate xmas_elf;
extern crate panopticon;
extern crate pdb as crate_pdb;

use std::borrow::Borrow;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp;
use std::error;
use std::fmt::{self, Debug};
use std::fs;
use std::io::Write;
use std::result;
use std::rc::Rc;

use panopticon::amd64;

mod dwarf;
mod pdb;

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

impl From<crate_pdb::Error> for Error {
    fn from(e: crate_pdb::Error) -> Error {
        Error(Cow::Owned(format!("PDB error: {}", e)))
    }
}

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, Default, Clone)]
pub struct Flags<'a> {
    pub calls: bool,
    pub sort: bool,
    pub ignore_added: bool,
    pub ignore_deleted: bool,
    pub ignore_function_address: bool,
    pub ignore_function_size: bool,
    pub ignore_function_inline: bool,
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

    fn filter_unit(&self, unit: Option<&[u8]>) -> bool {
        if let Some(filter) = self.unit {
            filter_name(unit, filter)
        } else {
            true
        }
    }

    fn filter_name(&self, name: Option<&[u8]>) -> bool {
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

fn filter_name(name: Option<&[u8]>, filter: &str) -> bool {
    match name {
        Some(name) => name == filter.as_bytes(),
        None => false,
    }
}

fn filter_option<T, F>(o: Option<T>, f: F) -> Option<T>
    where T: Copy,
          F: FnOnce(T) -> bool
{
    o.and_then(|v| if f(v) { Some(v) } else { None })
}

#[derive(Debug)]
pub struct CodeRegion {
    // TODO: use format independent machine type
    machine: xmas_elf::header::Machine,
    region: panopticon::Region,
}

#[derive(Debug)]
pub struct File<'input> {
    code: Option<CodeRegion>,
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
                    // TODO: handle duplicate addresses
                    all_subprograms.insert(low_pc, subprogram);
                }
            }
        }
        all_subprograms
    }

    fn filter_units(&self, flags: &Flags, diff: bool) -> Vec<&Unit> {
        let mut units: Vec<_> = self.units
            .iter()
            .filter(|a| a.filter(flags))
            .collect();
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
    if input.starts_with(&xmas_elf::header::MAGIC) {
        parse_elf(input, cb)
    } else if input.starts_with(b"Microsoft C/C++ MSF 7.00\r\n\x1a\x44\x53\x00") {
        pdb::parse(input, cb)
    } else {
        Err("unrecognized file format".into())
    }
}

pub fn parse_elf(input: &[u8], cb: &mut FnMut(&mut File) -> Result<()>) -> Result<()> {
    let elf = xmas_elf::ElfFile::new(input);
    let machine = elf.header
        .pt2?
        .machine();
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
        code: Some(CodeRegion {
                       machine: machine,
                       region: region,
                   }),
        units: units,
    };

    cb(&mut file)
}

#[derive(Debug, Clone, Copy,)]
enum DiffPrefix {
    None,
    Equal,
    Less,
    Greater,
}

struct PrintState<'a, 'input>
    where 'input: 'a
{
    indent: usize,
    prefix: DiffPrefix,
    // True if DiffPrefix::Less or DiffPrefix::Greater was printed.
    diff: bool,

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
            prefix: DiffPrefix::None,
            diff: false,
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

    fn prefix<F>(&mut self, prefix: DiffPrefix, mut f: F) -> Result<()>
        where F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>
    {
        let prev = self.prefix;
        self.prefix = prefix;
        let ret = f(self);
        self.prefix = prev;
        ret
    }

    fn line<F>(&mut self, w: &mut Write, mut f: F) -> Result<()>
        where F: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>
    {
        match self.prefix {
            DiffPrefix::None => {}
            DiffPrefix::Equal => write!(w, "  ")?,
            DiffPrefix::Less => {
                write!(w, "- ")?;
                self.diff = true;
            }
            DiffPrefix::Greater => {
                write!(w, "+ ")?;
                self.diff = true;
            }
        }
        for _ in 0..self.indent {
            write!(w, "\t")?;
        }
        f(w, self)?;
        write!(w, "\n")?;
        Ok(())
    }

    fn line_option<F>(&mut self, w: &mut Write, mut f: F) -> Result<()>
        where F: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>
    {
        let mut buf = Vec::new();
        let mut state = PrintState::new(self.file, self.all_subprograms, self.flags);
        f(&mut buf, &mut state)?;
        if !buf.is_empty() {
            self.line(w, |w, _state| w.write_all(&*buf).map_err(From::from))?;
        }
        Ok(())
    }
}

pub fn print_file(w: &mut Write, file: &mut File, flags: &Flags) -> Result<()> {
    let subprograms = file.subprograms();
    for unit in file.filter_units(flags, false).iter() {
        let mut state = PrintState::new(file, &subprograms, flags);
        if flags.unit.is_none() {
            state.line(w, |w, _state| {
                    write!(w, "Unit: ")?;
                    unit.print_ref(w)
                })?;
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
    flags: &'a Flags<'a>,
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
            flags: flags,
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

    fn diff<F>(&mut self, w: &mut Write, mut f: F) -> Result<()>
        where F: FnMut(&mut Write, &mut DiffState<'a, 'input>) -> Result<()>
    {
        let mut buf = Vec::new();
        self.a.diff = false;
        self.b.diff = false;
        f(&mut buf, self)?;
        if self.a.diff || self.b.diff {
            w.write_all(&*buf)?;
        }
        Ok(())
    }

    fn ignore_diff<F>(&mut self, flag: bool, mut f: F) -> Result<()>
        where F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>
    {
        let a_diff = self.a.diff;
        let b_diff = self.b.diff;
        f(self)?;
        if flag {
            self.a.diff = a_diff;
            self.b.diff = b_diff;
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
        self.a.prefix = DiffPrefix::Equal;
        self.b.prefix = DiffPrefix::Equal;
        let ret = f(self);
        self.a.prefix = prev_a;
        self.b.prefix = prev_b;
        ret
    }

    fn prefix_less<F>(&mut self, f: F) -> Result<()>
        where F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>
    {
        self.a.prefix(DiffPrefix::Less, f)
    }

    fn prefix_greater<F>(&mut self, f: F) -> Result<()>
        where F: FnMut(&mut PrintState<'a, 'input>) -> Result<()>
    {
        self.b.prefix(DiffPrefix::Greater, f)
    }

    fn prefix_diff<F>(&mut self, mut f: F) -> Result<()>
        where F: FnMut(&mut DiffState<'a, 'input>) -> Result<()>
    {
        let prev_a = self.a.prefix;
        let prev_b = self.b.prefix;
        self.a.prefix = DiffPrefix::Less;
        self.b.prefix = DiffPrefix::Greater;
        let ret = f(self);
        self.a.prefix = prev_a;
        self.b.prefix = prev_b;
        ret
    }

    fn line<A, B>(&mut self, w: &mut Write, mut f_a: A, mut f_b: B) -> Result<()>
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
                if !a.is_empty() {
                    state.a.line(w, |w, _state| w.write_all(&*a).map_err(From::from))?;
                }
                Ok(())
            })
        } else {
            self.prefix_diff(|state| {
                if !a.is_empty() {
                    state.a.line(w, |w, _state| w.write_all(&*a).map_err(From::from))?;
                }
                if !b.is_empty() {
                    state.b.line(w, |w, _state| w.write_all(&*b).map_err(From::from))?;
                }
                Ok(())
            })
        }
    }

    /// This is the same as `Self::line`. It exists for symmetry with `PrintState::line_option`.
    fn line_option<A, B>(&mut self, w: &mut Write, f_a: A, f_b: B) -> Result<()>
        where A: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>,
              B: FnMut(&mut Write, &mut PrintState<'a, 'input>) -> Result<()>
    {
        self.line(w, f_a, f_b)
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
                state.a
                    .line(w, |w, _state| {
                        write!(w, "Unit: ")?;
                        a.print_ref(w)
                    })?;
            }
            Unit::diff(a, b, w, state, flags)
        },
                |w, state, a| {
                    state.line(w, |w, _state| {
                write!(w, "Unit: ")?;
                a.print_ref(w)
            })
                },
                |w, state, b| {
                    state.line(w, |w, _state| {
                write!(w, "Unit: ")?;
                b.print_ref(w)
            })
                })?;
    Ok(())
}

#[derive(Debug, Default)]
struct Namespace<'input> {
    parent: Option<Rc<Namespace<'input>>>,
    name: Option<&'input [u8]>,
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
    fn new(parent: &Rc<Namespace<'input>>, name: Option<&'input [u8]>) -> Rc<Namespace<'input>> {
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
                Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
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
    name1: Option<&[u8]>,
    ns2: &Namespace,
    name2: Option<&[u8]>
) -> cmp::Ordering {
    match Namespace::cmp(ns1, ns2) {
        cmp::Ordering::Equal => name1.cmp(&name2),
        o => o,
    }
}

#[derive(Debug, Default)]
pub struct Unit<'input> {
    dir: Option<&'input [u8]>,
    name: Option<&'input [u8]>,
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
            ty.visit_members(&mut |t| if t.is_inline(self) {
                                      if let Some(offset) = t.ty {
                                          inline_types.insert(offset.0);
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
                TypeKind::Modifier(..) => return false,
            }
            // Filter out inline types.
            !inline_types.contains(&t.offset.0)
        };
        let mut types: Vec<_> = self.types
            .values()
            .filter(|a| filter_type(a))
            .collect();
        if diff || flags.sort {
            types.sort_by(|a, b| Type::cmp_id(a, b));
        }
        types
    }

    /// Filter and sort the list of subprograms using the options in the flags.
    /// Always sort when diffing.
    fn filter_subprograms(&self, flags: &Flags, diff: bool) -> Vec<&Subprogram> {
        let mut subprograms: Vec<_> = self.subprograms
            .values()
            .filter(|a| a.filter(flags))
            .collect();
        if diff || flags.sort {
            subprograms.sort_by(|a, b| Subprogram::cmp_id(a, b));
        }
        subprograms
    }

    /// Filter and sort the list of variables using the options in the flags.
    /// Always sort when diffing.
    fn filter_variables(&self, flags: &Flags, diff: bool) -> Vec<&Variable> {
        let mut variables: Vec<_> = self.variables
            .iter()
            .filter(|a| a.filter(flags))
            .collect();
        if diff || flags.sort {
            variables.sort_by(|a, b| Variable::cmp_id(a, b));
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

    fn print(&self, w: &mut Write, state: &mut PrintState, flags: &Flags) -> Result<()> {
        for ty in &self.filter_types(flags, false) {
            ty.print(w, state, self)?;
            writeln!(w, "")?;
        }
        for subprogram in &self.filter_subprograms(flags, false) {
            subprogram.print(w, state, self)?;
            writeln!(w, "")?;
        }
        for variable in &self.filter_variables(flags, false) {
            variable.print(w, state, self)?;
            writeln!(w, "")?;
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
                    |w, state, a, b| {
                state.diff(w, |w, state| {
                    Type::diff(w, state, unit_a, a, unit_b, b)?;
                    writeln!(w, "")?;
                    Ok(())
                })
            },
                    |w, state, a| {
                if !flags.ignore_deleted {
                    a.print(w, state, unit_a)?;
                    writeln!(w, "")?;
                }
                Ok(())
            },
                    |w, state, b| {
                if !flags.ignore_added {
                    b.print(w, state, unit_b)?;
                    writeln!(w, "")?;
                }
                Ok(())
            })?;
        state.merge(w,
                    &mut unit_a.filter_subprograms(flags, true).iter(),
                    &mut unit_b.filter_subprograms(flags, true).iter(),
                    |a, b| Subprogram::cmp_id(a, b),
                    |w, state, a, b| {
                state.diff(w, |w, state| {
                    Subprogram::diff(w, state, unit_a, a, unit_b, b)?;
                    writeln!(w, "")?;
                    Ok(())
                })
            },
                    |w, state, a| {
                if !flags.ignore_deleted {
                    a.print(w, state, unit_a)?;
                    writeln!(w, "")?;
                }
                Ok(())
            },
                    |w, state, b| {
                if !flags.ignore_added {
                    b.print(w, state, unit_b)?;
                    writeln!(w, "")?;
                }
                Ok(())
            })?;
        state.merge(w,
                    &mut unit_a.filter_variables(flags, true).iter(),
                    &mut unit_b.filter_variables(flags, true).iter(),
                    |a, b| Variable::cmp_id(a, b),
                    |w, state, a, b| {
                state.diff(w, |w, state| {
                    Variable::diff(w, state, unit_a, a, unit_b, b)?;
                    writeln!(w, "")?;
                    Ok(())
                })
            },
                    |w, state, a| {
                if !flags.ignore_deleted {
                    a.print(w, state, unit_a)?;
                    writeln!(w, "")?;
                }
                Ok(())
            },
                    |w, state, b| {
                if !flags.ignore_added {
                    b.print(w, state, unit_b)?;
                    writeln!(w, "")?;
                }
                Ok(())
            })?;
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
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct TypeOffset(usize);

impl From<gimli::UnitOffset> for TypeOffset {
    fn from(o: gimli::UnitOffset) -> TypeOffset {
        TypeOffset(o.0)
    }
}

#[derive(Debug)]
struct Type<'input> {
    offset: TypeOffset,
    kind: TypeKind<'input>,
}

impl<'input> Default for Type<'input> {
    fn default() -> Self {
        Type {
            offset: TypeOffset(0),
            kind: TypeKind::Base(BaseType::default()),
        }
    }
}

impl<'input> Type<'input> {
    fn from_offset<'a>(unit: &'a Unit<'input>, offset: TypeOffset) -> Option<&'a Type<'input>> {
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
            TypeKind::Modifier(..) => {}
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
            TypeKind::Modifier(..) => flags.name.is_none(),
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
            TypeKind::Modifier(..) => Err(format!("can't print {:?}", self).into()),
        }
    }

    fn print_ref(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        match self.kind {
            TypeKind::Base(ref val) => val.print_ref(w),
            TypeKind::Def(ref val) => val.print_ref(w),
            TypeKind::Struct(ref val) => val.print_ref(w),
            TypeKind::Union(ref val) => val.print_ref(w),
            TypeKind::Enumeration(ref val) => val.print_ref(w),
            TypeKind::Array(ref val) => val.print_ref(w, unit),
            TypeKind::Subroutine(ref val) => val.print_ref(w, unit),
            TypeKind::Modifier(ref val) => val.print_ref(w, unit),
        }
    }

    fn print_ref_from_offset(w: &mut Write, unit: &Unit, offset: TypeOffset) -> Result<()> {
        match Type::from_offset(unit, offset) {
            Some(ty) => ty.print_ref(w, unit)?,
            None => write!(w, "<invalid-type {}>", offset.0)?,
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
            TypeKind::Modifier(..) => false,
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
        }?;
        Ok(())
    }

    fn print_members(
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        ty: Option<&Type>,
        offset: Option<u64>
    ) -> Result<()> {
        if let Some(ty) = ty {
            match ty.kind {
                TypeKind::Struct(ref t) => return t.print_members(w, state, unit, offset),
                TypeKind::Union(ref t) => return t.print_members(w, state, unit, offset),
                _ => return Err(format!("can't print members {:?}", ty).into()),
            }
        }
        Ok(())
    }

    fn diff_members(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        type_a: Option<&Type>,
        offset_a: Option<u64>,
        unit_b: &Unit,
        type_b: Option<&Type>,
        offset_b: Option<u64>
    ) -> Result<()> {
        if let (Some(type_a), Some(type_b)) = (type_a, type_b) {
            match (&type_a.kind, &type_b.kind) {
                (&TypeKind::Struct(ref a), &TypeKind::Struct(ref b)) => {
                    return StructType::diff_members(w,
                                                    state,
                                                    unit_a,
                                                    a,
                                                    offset_a,
                                                    unit_b,
                                                    b,
                                                    offset_b);
                }
                (&TypeKind::Union(ref a), &TypeKind::Union(ref b)) => {
                    return UnionType::diff_members(w,
                                                   state,
                                                   unit_a,
                                                   a,
                                                   offset_a,
                                                   unit_b,
                                                   b,
                                                   offset_b);
                }
                _ => {}
            }
        }

        state.prefix_diff(|state| {
                              Type::print_members(w, &mut state.a, unit_a, type_a, offset_a)?;
                              Type::print_members(w, &mut state.b, unit_b, type_b, offset_b)
                          })
    }

    fn print_members_entries(
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        ty: Option<&Type>,
        offset: Option<u64>
    ) -> Result<()> {
        if let Some(ty) = ty {
            match ty.kind {
                TypeKind::Struct(ref t) => return t.print_members_entries(w, state, unit, offset),
                TypeKind::Union(ref t) => return t.print_members_entries(w, state, unit, offset),
                _ => return Err(format!("can't print members entries {:?}", ty).into()),
            }
        }
        Ok(())
    }

    fn diff_members_entries(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        type_a: Option<&Type>,
        offset_a: Option<u64>,
        unit_b: &Unit,
        type_b: Option<&Type>,
        offset_b: Option<u64>
    ) -> Result<()> {
        if let (Some(type_a), Some(type_b)) = (type_a, type_b) {
            match (&type_a.kind, &type_b.kind) {
                (&TypeKind::Struct(ref a), &TypeKind::Struct(ref b)) => {
                    return StructType::diff_members_entries(w,
                                                            state,
                                                            unit_a,
                                                            a,
                                                            offset_a,
                                                            unit_b,
                                                            b,
                                                            offset_b);
                }
                (&TypeKind::Union(ref a), &TypeKind::Union(ref b)) => {
                    return UnionType::diff_members_entries(w,
                                                           state,
                                                           unit_a,
                                                           a,
                                                           offset_a,
                                                           unit_b,
                                                           b,
                                                           offset_b);
                }
                _ => {}
            }
        }

        state.prefix_diff(|state| {
            Type::print_members_entries(w, &mut state.a, unit_a, type_a, offset_a)?;
            Type::print_members_entries(w, &mut state.b, unit_b, type_b, offset_b)
        })
    }
}

#[derive(Debug)]
struct TypeModifier<'input> {
    kind: TypeModifierKind,
    ty: Option<TypeOffset>,
    name: Option<&'input [u8]>,
    byte_size: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TypeModifierKind {
    Const,
    Pointer,
    Restrict,
    Other,
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
            TypeModifierKind::Restrict |
            TypeModifierKind::Other => self.ty(unit).and_then(|v| v.bit_size(unit)),
            TypeModifierKind::Pointer => unit.address_size.map(|v| v * 8),
        }
    }

    fn print_ref(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        if let Some(name) = self.name {
            write!(w, "{}", String::from_utf8_lossy(name))?;
        } else {
            match self.kind {
                TypeModifierKind::Const => write!(w, "const ")?,
                TypeModifierKind::Pointer => write!(w, "* ")?,
                TypeModifierKind::Restrict => write!(w, "restrict ")?,
                TypeModifierKind::Other => {}
            }
            match self.ty {
                Some(ty) => Type::print_ref_from_offset(w, unit, ty)?,
                None => write!(w, "<unknown-type>")?,
            }
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct BaseType<'input> {
    name: Option<&'input [u8]>,
    byte_size: Option<u64>,
}

impl<'input> BaseType<'input> {
    fn bit_size(&self, _unit: &Unit) -> Option<u64> {
        self.byte_size.map(|v| v * 8)
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon-base-type>")?,
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct TypeDef<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input [u8]>,
    ty: Option<TypeOffset>,
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
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon-typedef>")?,
        }
        Ok(())
    }

    fn print_name(&self, w: &mut Write, _state: &mut PrintState, unit: &Unit) -> Result<()> {
        write!(w, "type ")?;
        self.print_ref(w)?;
        write!(w, " = ")?;
        match self.ty {
            Some(ty) => Type::print_ref_from_offset(w, unit, ty)?,
            None => write!(w, "<unknown-type>")?,
        }
        Ok(())
    }

    fn print_bit_size(&self, w: &mut Write, _state: &mut PrintState, unit: &Unit) -> Result<()> {
        if let Some(bit_size) = self.bit_size(unit) {
            write!(w, "size: {}", format_bit(bit_size))?;
        }
        Ok(())
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        let ty = self.ty(unit);
        state.line(w, |w, state| self.print_name(w, state, unit))?;
        state.indent(|state| {
                state.line(w, |w, state| self.print_bit_size(w, state, unit))?;
                if let Some(ty) = ty {
                    if ty.is_anon() {
                        Type::print_members(w, state, unit, Some(ty), Some(0))?;
                    }
                }
                Ok(())
            })?;
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &TypeDef, b: &TypeDef) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &TypeDef,
        unit_b: &Unit,
        b: &TypeDef
    ) -> Result<()> {
        state.line(w,
                   |w, state| a.print_name(w, state, unit_a),
                   |w, state| b.print_name(w, state, unit_b))?;
        state.indent(|state| {
            state.line_option(w,
                              |w, state| a.print_bit_size(w, state, unit_a),
                              |w, state| b.print_bit_size(w, state, unit_b))?;
            let ty_a = filter_option(a.ty(unit_a), Type::is_anon);
            let ty_b = filter_option(b.ty(unit_b), Type::is_anon);
            Type::diff_members(w, state, unit_a, ty_a, Some(0), unit_b, ty_b, Some(0))
        })
    }
}

#[derive(Debug, Default)]
struct StructType<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input [u8]>,
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
        state.line(w, |w, _state| self.print_ref(w))?;
        state.indent(|state| {
                         state.line_option(w, |w, state| self.print_declaration(w, state))?;
                         state.line_option(w, |w, state| self.print_byte_size(w, state))?;
                         self.print_members(w, state, unit, Some(0))
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
        // The names should be the same, but we can't be sure.
        state.line(w, |w, _state| a.print_ref(w), |w, _state| b.print_ref(w))?;
        state.indent(|state| {
                state.line_option(w,
                                  |w, state| a.print_declaration(w, state),
                                  |w, state| b.print_declaration(w, state))?;
                state.line_option(w,
                                  |w, state| a.print_byte_size(w, state),
                                  |w, state| b.print_byte_size(w, state))?;
                Self::diff_members(w, state, unit_a, a, Some(0), unit_b, b, Some(0))
            })?;

        Ok(())
    }

    fn print_members(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        bit_offset: Option<u64>
    ) -> Result<()> {
        state.line_option(w, |w, state| self.print_members_label(w, state))?;
        state.indent(|state| self.print_members_entries(w, state, unit, bit_offset))
    }

    fn diff_members(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &StructType,
        bit_offset_a: Option<u64>,
        unit_b: &Unit,
        b: &StructType,
        bit_offset_b: Option<u64>
    ) -> Result<()> {
        state.line_option(w,
                          |w, state| a.print_members_label(w, state),
                          |w, state| b.print_members_label(w, state))?;
        state.indent(|state| {
            Self::diff_members_entries(w, state, unit_a, a, bit_offset_a, unit_b, b, bit_offset_b)
        })
    }

    fn print_byte_size(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size {
            write!(w, "size: {}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_members_label(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if !self.members.is_empty() {
            write!(w, "members:")?;
        }
        Ok(())
    }

    fn print_members_entries(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        mut bit_offset: Option<u64>
    ) -> Result<()> {
        for member in &self.members {
            state.line_option(w,
                              |w, _state| Member::print_padding(w, member.padding(bit_offset)))?;
            member.print(w, state, unit, &mut bit_offset)?;
        }
        state.line_option(w,
                          |w, _state| Member::print_padding(w, self.padding(bit_offset)))?;
        Ok(())
    }

    fn diff_members_entries(
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
        let mut members_a = a.members
            .iter()
            .enumerate()
            .filter(|a| a.1.name.is_some())
            .collect::<Vec<_>>();
        members_a.sort_by(|x, y| Member::cmp_id(x.1, y.1));
        let mut members_b = b.members
            .iter()
            .enumerate()
            .filter(|b| b.1.name.is_some())
            .collect::<Vec<_>>();
        members_b.sort_by(|x, y| Member::cmp_id(x.1, y.1));

        // Find pairs of members with the same name.
        let mut pairs = Vec::new();
        for m in MergeIterator::new(members_a.iter(),
                                    members_b.iter(),
                                    |a, b| Member::cmp_id(a.1, b.1)) {
            if let MergeResult::Both(a, b) = m {
                if a.1.name.is_some() {
                    pairs.push((a, b));
                }
            }
        }
        // TODO: For remaining members, find pairs of members with the same type.
        // This should also handle matching up anonymous members.

        // Sort pairs by the indices.
        // TODO: also sort by equality (eg print and compare).
        pairs.sort_by(|&(xa, xb), &(ya, yb)| match (xa.0.cmp(&ya.0), xb.0.cmp(&yb.0)) {
                          (cmp::Ordering::Less, cmp::Ordering::Less) => cmp::Ordering::Less,
                          (cmp::Ordering::Greater, cmp::Ordering::Greater) => {
                              cmp::Ordering::Greater
                          }
                          (_cmp_a, cmp_b) => cmp_b,
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
                index_a += 1;
            }
            while index_b < b.0 {
                if let Some(b) = iter_b.next() {
                    state.prefix_greater(|state| b.print(w, state, unit_b, &mut bit_offset_b))?;
                }
                index_b += 1;
            }

            // Diff the pair.
            if let (Some(a), Some(b)) = (iter_a.next(), iter_b.next()) {
                state.line_option(w,
                                  |w, _state| Member::print_padding(w, a.padding(bit_offset_a)),
                                  |w, _state| Member::print_padding(w, b.padding(bit_offset_b)))?;
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
            index_a += 1;
            index_b += 1;
        }

        // Print trailing members.
        for a in iter_a {
            state.prefix_less(|state| a.print(w, state, unit_a, &mut bit_offset_a))?;
        }
        for b in iter_b {
            state.prefix_greater(|state| b.print(w, state, unit_b, &mut bit_offset_b))?;
        }

        state.line_option(w,
                          |w, _state| Member::print_padding(w, a.padding(bit_offset_a)),
                          |w, _state| Member::print_padding(w, b.padding(bit_offset_b)))?;

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
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
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
}

#[derive(Debug, Default)]
struct UnionType<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input [u8]>,
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
        state.line(w, |w, _state| self.print_ref(w))?;
        state.indent(|state| {
                         state.line_option(w, |w, state| self.print_declaration(w, state))?;
                         state.line_option(w, |w, state| self.print_byte_size(w, state))?;
                         self.print_members(w, state, unit, Some(0))
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
        // The names should be the same, but we can't be sure.
        state.line(w, |w, _state| a.print_ref(w), |w, _state| b.print_ref(w))?;
        state.indent(|state| {
                state.line_option(w,
                                  |w, state| a.print_declaration(w, state),
                                  |w, state| b.print_declaration(w, state))?;
                state.line_option(w,
                                  |w, state| a.print_byte_size(w, state),
                                  |w, state| b.print_byte_size(w, state))?;
                Self::diff_members(w, state, unit_a, a, Some(0), unit_b, b, Some(0))
            })?;

        Ok(())
    }

    fn print_members(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        bit_offset: Option<u64>
    ) -> Result<()> {
        state.line_option(w, |w, state| self.print_members_label(w, state))?;
        state.indent(|state| self.print_members_entries(w, state, unit, bit_offset))
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
        state.line_option(w,
                          |w, state| a.print_members_label(w, state),
                          |w, state| b.print_members_label(w, state))?;
        state.indent(|state| {
            Self::diff_members_entries(w, state, unit_a, a, bit_offset_a, unit_b, b, bit_offset_b)
        })
    }

    fn print_byte_size(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size {
            write!(w, "size: {}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_members_label(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if !self.members.is_empty() {
            write!(w, "members:")?;
        }
        Ok(())
    }

    fn print_members_entries(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        bit_offset: Option<u64>
    ) -> Result<()> {
        for member in &self.members {
            let mut bit_offset = bit_offset;
            // TODO: padding?
            member.print(w, state, unit, &mut bit_offset)?;
        }
        // TODO: trailing padding?
        Ok(())
    }

    fn diff_members_entries(
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
                // TODO: padding?
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
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
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
}

#[derive(Debug, Default, Clone)]
struct Member<'input> {
    name: Option<&'input [u8]>,
    // TODO: treat padding as typeless member?
    ty: Option<TypeOffset>,
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
        state.line(w,
                   |w, state| self.print_name(w, state, unit, end_bit_offset))?;
        state.indent(|state| {
            let ty = if self.is_inline(unit) {
                self.ty(unit)
            } else {
                None
            };
            Type::print_members_entries(w, state, unit, ty, Some(self.bit_offset))
        })
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
        state.line(w,
                   |w, state| a.print_name(w, state, unit_a, end_bit_offset_a),
                   |w, state| b.print_name(w, state, unit_b, end_bit_offset_b))?;
        state.indent(|state| {
            let ty_a = if a.is_inline(unit_a) {
                a.ty(unit_a)
            } else {
                None
            };
            let ty_b = if b.is_inline(unit_b) {
                b.ty(unit_b)
            } else {
                None
            };
            Type::diff_members_entries(w,
                                       state,
                                       unit_a,
                                       ty_a,
                                       Some(a.bit_offset),
                                       unit_b,
                                       ty_b,
                                       Some(b.bit_offset))
        })
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

    fn print_padding(w: &mut Write, padding: Option<(u64, u64)>) -> Result<()> {
        if let Some((padding_bit_offset, padding_bit_size)) = padding {
            write!(w,
                   "{}[{}]\t<padding>",
                   format_bit(padding_bit_offset),
                   format_bit(padding_bit_size))?;
        }
        Ok(())
    }

    fn print_name(
        &self,
        w: &mut Write,
        _state: &mut PrintState,
        unit: &Unit,
        end_bit_offset: &mut Option<u64>
    ) -> Result<()> {
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
            Some(name) => write!(w, "\t{}", String::from_utf8_lossy(name))?,
            None => write!(w, "\t<anon>")?,
        }
        write!(w, ": ")?;
        match self.ty {
            Some(ty) => Type::print_ref_from_offset(w, unit, ty)?,
            None => write!(w, "<unknown-type>")?,
        }
        Ok(())
    }

    fn is_inline(&self, unit: &Unit) -> bool {
        match self.name {
            Some(s) => {
                if s.starts_with(b"RUST$ENCODED$ENUM$") {
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

    fn cmp_id(a: &Member, b: &Member) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}

#[derive(Debug, Default)]
struct EnumerationType<'input> {
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input [u8]>,
    declaration: bool,
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

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &EnumerationType, b: &EnumerationType) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn print(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line(w, |w, _state| self.print_ref(w))?;
        state.indent(|state| {
                         state.line_option(w, |w, _state| self.print_declaration(w))?;
                         state.line_option(w, |w, state| self.print_byte_size(w, state))?;
                         self.print_enumerators(w, state)
                     })
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &EnumerationType,
        _unit_b: &Unit,
        b: &EnumerationType
    ) -> Result<()> {
        // The names should be the same, but we can't be sure.
        state.line(w, |w, _state| a.print_ref(w), |w, _state| b.print_ref(w))?;
        state.indent(|state| {
                state.line_option(w,
                                  |w, _state| a.print_declaration(w),
                                  |w, _state| b.print_declaration(w))?;
                state.line_option(w,
                                  |w, state| a.print_byte_size(w, state),
                                  |w, state| b.print_byte_size(w, state))?;
                Self::diff_enumerators(w, state, a, b)
            })?;
        Ok(())
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        write!(w, "enum ")?;
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_byte_size(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size {
            write!(w, "size: {}", size)?;
        } else {
            debug!("enum with no size");
        }
        Ok(())
    }

    fn print_enumerators(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line_option(w, |w, state| self.print_enumerators_label(w, state))?;
        state.indent(|state| self.print_enumerators_entries(w, state))
    }

    fn diff_enumerators(
        w: &mut Write,
        state: &mut DiffState,
        a: &EnumerationType,
        b: &EnumerationType
    ) -> Result<()> {
        state.line_option(w,
                          |w, state| a.print_enumerators_label(w, state),
                          |w, state| b.print_enumerators_label(w, state))?;
        state.indent(|state| Self::diff_enumerators_entries(w, state, a, b))
    }

    fn print_enumerators_label(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if !self.enumerators.is_empty() {
            write!(w, "enumerators:")?;
        } else {
            debug!("enum with no enumerators");
        }
        Ok(())
    }

    fn print_enumerators_entries(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        for enumerator in &self.enumerators {
            enumerator.print(w, state)?;
        }
        Ok(())
    }

    fn diff_enumerators_entries(
        w: &mut Write,
        state: &mut DiffState,
        a: &EnumerationType,
        b: &EnumerationType
    ) -> Result<()> {
        // Sort by value.
        let mut enumerators_a = a.enumerators.iter().collect::<Vec<_>>();
        enumerators_a.sort_by(|x, y| x.value.cmp(&y.value));
        let mut enumerators_b = b.enumerators.iter().collect::<Vec<_>>();
        enumerators_b.sort_by(|x, y| x.value.cmp(&y.value));

        state.merge(w,
                    &mut enumerators_a.iter(),
                    &mut enumerators_b.iter(),
                    |a, b| if a.name.cmp(&b.name) == cmp::Ordering::Equal {
                        cmp::Ordering::Equal
                    } else {
                        a.value.cmp(&b.value)
                    },
                    |w, state, a, b| Enumerator::diff(w, state, a, b),
                    |w, state, a| a.print(w, state),
                    |w, state, b| b.print(w, state))?;
        Ok(())
    }
}

#[derive(Debug, Default, Clone)]
struct Enumerator<'input> {
    name: Option<&'input [u8]>,
    value: Option<i64>,
}

impl<'input> Enumerator<'input> {
    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line(w, |w, _state| self.print_name_value(w))
    }

    fn diff(w: &mut Write, state: &mut DiffState, a: &Enumerator, b: &Enumerator) -> Result<()> {
        state.line(w,
                   |w, _state| a.print_name_value(w),
                   |w, _state| b.print_name_value(w))
    }

    fn print_name_value(&self, w: &mut Write) -> Result<()> {
        self.print_ref(w)?;
        if let Some(value) = self.value {
            write!(w, "({})", value)?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct ArrayType<'input> {
    ty: Option<TypeOffset>,
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

    fn print_ref(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        write!(w, "[")?;
        match self.ty {
            Some(ty) => Type::print_ref_from_offset(w, unit, ty)?,
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
    return_type: Option<TypeOffset>,
}

impl<'input> SubroutineType<'input> {
    fn bit_size(&self, _unit: &Unit) -> Option<u64> {
        None
    }

    fn return_type<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.return_type.and_then(|v| unit.types.get(&v.0))
    }

    fn print_ref(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        let mut first = true;
        write!(w, "(")?;
        for parameter in &self.parameters {
            if first {
                first = false;
            } else {
                write!(w, ", ")?;
            }
            parameter.print(w, unit)?;
        }
        write!(w, ")")?;

        if let Some(return_type) = self.return_type(unit) {
            write!(w, " -> ")?;
            return_type.print_ref(w, unit)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
struct SubprogramOffset(usize);

impl From<gimli::UnitOffset> for SubprogramOffset {
    fn from(o: gimli::UnitOffset) -> SubprogramOffset {
        SubprogramOffset(o.0)
    }
}

#[derive(Debug)]
struct Subprogram<'input> {
    offset: SubprogramOffset,
    namespace: Rc<Namespace<'input>>,
    name: Option<&'input [u8]>,
    linkage_name: Option<&'input [u8]>,
    low_pc: Option<u64>,
    high_pc: Option<u64>,
    size: Option<u64>,
    inline: bool,
    declaration: bool,
    parameters: Vec<Parameter<'input>>,
    return_type: Option<TypeOffset>,
    inlined_subroutines: Vec<InlinedSubroutine<'input>>,
    variables: Vec<Variable<'input>>,
}

impl<'input> Subprogram<'input> {
    fn from_offset<'a>(
        unit: &'a Unit<'input>,
        offset: SubprogramOffset
    ) -> Option<&'a Subprogram<'input>> {
        unit.subprograms.get(&offset.0)
    }

    fn filter(&self, flags: &Flags) -> bool {
        flags.filter_name(self.name) && flags.filter_namespace(&*self.namespace)
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

    /// Compare the identifying information of two subprograms.
    /// This can be used to sort, and to determine if two subprograms refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &Subprogram, b: &Subprogram) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        self.namespace.print(w)?;
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
            state.indent(|state| {
                state.line_option(w, |w, _state| self.print_return_type(w, unit))
            })?;
            state.line_option(w, |w, _state| self.print_parameters_label(w))?;
            state.indent(|state| self.print_parameters(w, state, unit))?;
            if state.flags.inline_depth > 0 {
                state.line_option(w, |w, _state| self.print_inlined_subroutines_label(w))?;
                state.indent(|state| self.print_inlined_subroutines(w, state, unit))?;
            }
            if state.flags.calls {
                let calls = self.calls(&state.file);
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
        a: &Subprogram,
        unit_b: &Unit,
        b: &Subprogram
    ) -> Result<()> {
        state.line(w, |w, _state| a.print_name(w), |w, _state| b.print_name(w))?;
        state.indent(|state| {
            state.line_option(w,
                              |w, _state| a.print_linkage_name(w),
                              |w, _state| b.print_linkage_name(w))?;
            let flag = state.flags.ignore_function_address;
            state.ignore_diff(flag, |state| {
                    state.line_option(w,
                                      |w, _state| a.print_address(w),
                                      |w, _state| b.print_address(w))
                })?;
            let flag = state.flags.ignore_function_size;
            state.ignore_diff(flag, |state| {
                    state.line_option(w, |w, _state| a.print_size(w), |w, _state| b.print_size(w))
                })?;
            let flag = state.flags.ignore_function_inline;
            state.ignore_diff(flag, |state| {
                    state.line_option(w,
                                      |w, _state| a.print_inline(w),
                                      |w, _state| b.print_inline(w))
                })?;
            state.line_option(w,
                              |w, _state| a.print_declaration(w),
                              |w, _state| b.print_declaration(w))?;
            state.line_option(w,
                              |w, _state| a.print_return_type_label(w),
                              |w, _state| b.print_return_type_label(w))?;
            state.indent(|state| {
                             state.line_option(w,
                                               |w, _state| a.print_return_type(w, unit_a),
                                               |w, _state| b.print_return_type(w, unit_b))
                         })?;
            state.line_option(w,
                              |w, _state| a.print_parameters_label(w),
                              |w, _state| b.print_parameters_label(w))?;
            state.indent(|state| Subprogram::diff_parameters(w, state, unit_a, a, unit_b, b))?;
            // TODO
            if false && state.flags.inline_depth > 0 {
                state.line_option(w,
                                  |w, _state| a.print_inlined_subroutines_label(w),
                                  |w, _state| b.print_inlined_subroutines_label(w))?;
                state.indent(|state| {
                        Subprogram::diff_inlined_subroutines(w, state, unit_a, a, unit_b, b)
                    })?;
            }
            // TODO
            if false && state.flags.calls {
                let calls_a = a.calls(&state.a.file);
                let calls_b = b.calls(&state.b.file);
                state.line_option(w,
                                  |w, _state| {
                                      if !calls_a.is_empty() {
                                          a.print_calls_label(w)?;
                                      }
                                      Ok(())
                                  },
                                  |w, _state| {
                                      if !calls_b.is_empty() {
                                          b.print_calls_label(w)?;
                                      }
                                      Ok(())
                                  })?;
                state.indent(|state| Subprogram::diff_calls(w, state, &calls_a, &calls_b))?;
            }
            Ok(())
        })
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        write!(w, "fn ")?;
        self.namespace.print(w)?;
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
            debug!("non-inline subprogram with no address");
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

    fn print_return_type(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        if let Some(return_type) = self.return_type {
            match Type::from_offset(unit, return_type).and_then(|t| t.bit_size(unit)) {
                Some(bit_size) => write!(w, "[{}]", format_bit(bit_size))?,
                None => write!(w, "[??]")?,
            }
            write!(w, "\t")?;
            Type::print_ref_from_offset(w, unit, return_type)?;
        }
        Ok(())
    }

    fn print_parameters_label(&self, w: &mut Write) -> Result<()> {
        if !self.parameters.is_empty() {
            write!(w, "parameters:")?;
        }
        Ok(())
    }

    fn print_parameters(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        for parameter in &self.parameters {
            state.line(w, |w, _state| Self::print_parameter(w, unit, parameter))?;
        }
        Ok(())
    }

    fn diff_parameters(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Subprogram,
        unit_b: &Unit,
        b: &Subprogram
    ) -> Result<()> {
        // Enumerate parameters and sort by name. Exclude anonymous members.
        let mut parameters_a = a.parameters
            .iter()
            .enumerate()
            .filter(|a| a.1.name.is_some())
            .collect::<Vec<_>>();
        parameters_a.sort_by(|x, y| Parameter::cmp_id(x.1, y.1));
        let mut parameters_b = b.parameters
            .iter()
            .enumerate()
            .filter(|b| b.1.name.is_some())
            .collect::<Vec<_>>();
        parameters_b.sort_by(|x, y| Parameter::cmp_id(x.1, y.1));

        // Find pairs of parameters with the same name.
        let mut pairs = Vec::new();
        for m in MergeIterator::new(parameters_a.iter(),
                                    parameters_b.iter(),
                                    |a, b| Parameter::cmp_id(a.1, b.1)) {
            if let MergeResult::Both(a, b) = m {
                if a.1.name.is_some() {
                    pairs.push((a, b));
                }
            }
        }
        // TODO: For remaining parameters, find pairs of parameters with the same type.

        // Sort pairs by the indices.
        // TODO: also sort by equality (eg print and compare).
        pairs.sort_by(|&(xa, xb), &(ya, yb)| match (xa.0.cmp(&ya.0), xb.0.cmp(&yb.0)) {
                          (cmp::Ordering::Less, cmp::Ordering::Less) => cmp::Ordering::Less,
                          (cmp::Ordering::Greater, cmp::Ordering::Greater) => {
                              cmp::Ordering::Greater
                          }
                          (_cmp_a, cmp_b) => cmp_b,
                      });

        // Loop through the pairs.
        let mut index_a = 0;
        let mut index_b = 0;
        let mut iter_a = a.parameters.iter();
        let mut iter_b = b.parameters.iter();
        for &(a, b) in &pairs {
            // Skip pairs that are already partially printed.
            if a.0 < index_a || b.0 < index_b {
                continue;
            }

            // Print parameters leading up to the pair.
            while index_a < a.0 {
                if let Some(a) = iter_a.next() {
                    state.prefix_less(|state| {
                                          state.line(w, |w, _state| {
                                Self::print_parameter(w, unit_a, a)
                            })
                                      })?;
                }
                index_a += 1;
            }
            while index_b < b.0 {
                if let Some(b) = iter_b.next() {
                    state.prefix_greater(|state| {
                                             state.line(w, |w, _state| {
                                Self::print_parameter(w, unit_b, b)
                            })
                                         })?;
                }
                index_b += 1;
            }

            // Diff the pair.
            if let (Some(a), Some(b)) = (iter_a.next(), iter_b.next()) {
                state.line(w,
                           |w, _state| Self::print_parameter(w, unit_a, a),
                           |w, _state| Self::print_parameter(w, unit_b, b))?;
            }
            index_a += 1;
            index_b += 1;
        }

        // Print trailing parameters.
        for a in iter_a {
            state.prefix_less(|state| {
                                  state.line(w, |w, _state| Self::print_parameter(w, unit_a, a))
                              })?;
        }
        for b in iter_b {
            state.prefix_greater(|state| {
                                     state.line(w, |w, _state| Self::print_parameter(w, unit_b, b))
                                 })?;
        }

        Ok(())
    }

    fn print_parameter(w: &mut Write, unit: &Unit, parameter: &Parameter) -> Result<()> {
        match parameter.bit_size(unit) {
            Some(bit_size) => write!(w, "[{}]", format_bit(bit_size))?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        parameter.print(w, unit)
    }

    fn print_inlined_subroutines_label(&self, w: &mut Write) -> Result<()> {
        if !self.inlined_subroutines.is_empty() {
            write!(w, "inlined subroutines:")?;
        }
        Ok(())
    }

    fn print_inlined_subroutines(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit
    ) -> Result<()> {
        for subroutine in &self.inlined_subroutines {
            subroutine.print(w, state, unit, 1)?;
        }
        Ok(())
    }

    fn diff_inlined_subroutines(
        _w: &mut Write,
        _state: &mut DiffState,
        _unit_a: &Unit,
        _a: &Subprogram,
        _unit_b: &Unit,
        _b: &Subprogram
    ) -> Result<()> {
        // TODO
        Ok(())
    }

    fn print_calls_label(&self, w: &mut Write) -> Result<()> {
        if self.return_type.is_some() {
            write!(w, "calls:")?;
        }
        Ok(())
    }

    fn print_calls(&self, w: &mut Write, state: &mut PrintState, calls: &[u64]) -> Result<()> {
        for call in calls {
            state.line(w, |w, state| {
                    write!(w, "0x{:x}", call)?;
                    if let Some(subprogram) = state.all_subprograms.get(call) {
                        write!(w, " ")?;
                        subprogram.print_ref(w)?;
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
        _calls_b: &[u64]
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
    fn ty<'a>(&self, unit: &'a Unit<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| Type::from_offset(unit, v))
    }

    fn bit_size(&self, unit: &Unit) -> Option<u64> {
        self.ty(unit).and_then(|t| t.bit_size(unit))
    }

    fn cmp_id(a: &Parameter, b: &Parameter) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }

    fn print(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        if let Some(name) = self.name {
            write!(w, "{}: ", String::from_utf8_lossy(name))?;
        }
        match self.ty(unit) {
            Some(ty) => ty.print_ref(w, unit)?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct InlinedSubroutine<'input> {
    abstract_origin: Option<SubprogramOffset>,
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
        state.line(w, |w, _state| {
                match self.size {
                    Some(size) => write!(w, "[{}]", size)?,
                    None => write!(w, "[??]")?,
                }
                write!(w, "\t")?;
                match self.abstract_origin.and_then(|v| Subprogram::from_offset(unit, v)) {
                    Some(subprogram) => subprogram.print_ref(w)?,
                    None => write!(w, "<anon>")?,
                }
                Ok(())
            })?;

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
    name: Option<&'input [u8]>,
    linkage_name: Option<&'input [u8]>,
    ty: Option<TypeOffset>,
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

    /// Compare the identifying information of two variables.
    /// This can be used to sort, and to determine if two variables refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &Variable, b: &Variable) -> cmp::Ordering {
        cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        self.namespace.print(w)?;
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line(w, |w, _state| self.print_name(w, unit))?;
        state.indent(|state| {
                         state.line_option(w, |w, _state| self.print_linkage_name(w))?;
                         state.line_option(w, |w, _state| self.print_size(w, unit))?;
                         state.line_option(w, |w, _state| self.print_declaration(w))
                         // TODO: print anon type inline
                     })
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Variable,
        unit_b: &Unit,
        b: &Variable
    ) -> Result<()> {
        state.line(w,
                   |w, _state| a.print_name(w, unit_a),
                   |w, _state| b.print_name(w, unit_b))?;
        state.indent(|state| {
            state.line_option(w,
                              |w, _state| a.print_linkage_name(w),
                              |w, _state| b.print_linkage_name(w))?;
            state.line_option(w,
                              |w, _state| a.print_size(w, unit_a),
                              |w, _state| b.print_size(w, unit_b))?;
            state.line_option(w,
                              |w, _state| a.print_declaration(w),
                              |w, _state| b.print_declaration(w))
        })
    }

    fn print_name(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        write!(w, "var ")?;
        self.print_ref(w)?;
        write!(w, ": ")?;
        match self.ty {
            Some(offset) => Type::print_ref_from_offset(w, unit, offset)?,
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

    fn print_size(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        if let Some(bit_size) = self.bit_size(unit) {
            write!(w, "size: {}", format_bit(bit_size))?;
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

fn disassemble(code: &CodeRegion, low_pc: u64, high_pc: u64) -> Vec<u64> {
    match code.machine {
        xmas_elf::header::Machine::X86_64 => {
            disassemble_arch::<amd64::Amd64>(&code.region, low_pc, high_pc, amd64::Mode::Long)
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
