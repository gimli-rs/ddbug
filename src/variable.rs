use std::cmp;
use std::io::Write;
use std::rc::Rc;

use {Options, Result, Sort};
use file::FileHash;
use namespace::Namespace;
use print::{DiffList, DiffState, Print, PrintState, SortList};
use range::Range;
use source::Source;
use types::{Type, TypeOffset};
use unit::Unit;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct VariableOffset(pub usize);

#[derive(Debug, Default)]
pub(crate) struct Variable<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub linkage_name: Option<&'input [u8]>,
    pub symbol_name: Option<&'input [u8]>,
    pub ty: Option<TypeOffset>,
    pub source: Source<'input>,
    pub address: Option<u64>,
    pub size: Option<u64>,
    pub declaration: bool,
}

impl<'input> Variable<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.size.is_some() {
            self.size
        } else {
            self.ty(hash).and_then(|t| t.byte_size(hash))
        }
    }

    pub fn address(&self, hash: &FileHash) -> Option<Range> {
        match (self.address, self.byte_size(hash)) {
            (Some(begin), Some(size)) => Some(Range {
                begin,
                end: begin + size,
            }),
            _ => None,
        }
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

    pub fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.indent(
            |state| state.line(|w, state| self.print_name(w, state)),
            |state| {
                state.field("linkage name", |w, _state| self.print_linkage_name(w))?;
                state.field("symbol name", |w, _state| self.print_symbol_name(w))?;
                if state.options().print_source {
                    state.field("source", |w, _state| self.print_source(w, unit))?;
                }
                state.field("address", |w, _state| self.print_address(w))?;
                state.field("size", |w, state| self.print_size(w, state))?;
                state.field("declaration", |w, _state| self.print_declaration(w))
                // TODO: print anon type inline
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    pub fn diff(
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Variable,
        unit_b: &Unit,
        b: &Variable,
    ) -> Result<()> {
        state.indent(
            |state| state.line(a, b, |w, state, x| x.print_name(w, state)),
            |state| {
                state.field("linkage name", a, b, |w, _state, x| x.print_linkage_name(w))?;
                let flag = state.options().ignore_variable_symbol_name;
                state.ignore_diff(flag, |state| {
                    state.field("symbol name", a, b, |w, _state, x| x.print_symbol_name(w))
                })?;
                if state.options().print_source {
                    state.field("source", (unit_a, a), (unit_b, b), |w, _state, (unit, x)| {
                        x.print_source(w, unit)
                    })?;
                }
                let flag = state.options().ignore_variable_address;
                state.ignore_diff(flag, |state| {
                    state.field("address", a, b, |w, _state, x| x.print_address(w))
                })?;
                state.field("size", a, b, |w, state, x| x.print_size(w, state))?;
                state.field("declaration", a, b, |w, _state, x| x.print_declaration(w))
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn print_name(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        write!(w, "var ")?;
        self.print_ref(w)?;
        write!(w, ": ")?;
        Type::print_ref_from_offset(w, hash, self.ty)?;
        Ok(())
    }

    fn print_linkage_name(&self, w: &mut Write) -> Result<()> {
        if let Some(linkage_name) = self.linkage_name {
            write!(w, "{}", String::from_utf8_lossy(linkage_name))?;
        }
        Ok(())
    }

    fn print_symbol_name(&self, w: &mut Write) -> Result<()> {
        if let Some(symbol_name) = self.symbol_name {
            write!(w, "{}", String::from_utf8_lossy(symbol_name))?;
        }
        Ok(())
    }

    fn print_source(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        if self.source.is_some() {
            self.source.print(w, unit)?;
        }
        Ok(())
    }

    fn print_address(&self, w: &mut Write) -> Result<()> {
        if let Some(address) = self.address {
            write!(w, "0x{:x}", address)?;
        }
        Ok(())
    }

    fn print_size(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        if let Some(byte_size) = self.byte_size(hash) {
            write!(w, "{}", byte_size)?;
        } else if !self.declaration {
            debug!("variable with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write) -> Result<()> {
        if self.declaration {
            write!(w, "yes")?;
        }
        Ok(())
    }

    pub fn filter(&self, options: &Options) -> bool {
        if !self.declaration && self.address.is_none() {
            // TODO: make this configurable?
            return false;
        }
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }
}

impl<'input> Print for Variable<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        self.print(state, unit)
    }

    fn diff(state: &mut DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> Result<()> {
        Self::diff(state, unit_a, a, unit_b, b)
    }
}

impl<'input> SortList for Variable<'input> {
    fn cmp_id(
        _hash_a: &FileHash,
        a: &Self,
        _hash_b: &FileHash,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn cmp_by(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        match options.sort {
            // TODO: sort by offset?
            Sort::None => a.address.cmp(&b.address),
            Sort::Name => Self::cmp_id(hash_a, a, hash_b, b, options),
            Sort::Size => a.byte_size(hash_a).cmp(&b.byte_size(hash_b)),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct LocalVariable<'input> {
    pub offset: VariableOffset,
    pub name: Option<&'input [u8]>,
    pub ty: Option<TypeOffset>,
    pub source: Source<'input>,
    pub address: Option<u64>,
    pub size: Option<u64>,
}

impl<'input> LocalVariable<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.size.is_some() {
            self.size
        } else {
            self.ty(hash).and_then(|t| t.byte_size(hash))
        }
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_decl(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        self.print_ref(w)?;
        write!(w, ": ")?;
        Type::print_ref_from_offset(w, hash, self.ty)?;
        Ok(())
    }

    fn print_size_and_decl(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        match self.byte_size(hash) {
            Some(byte_size) => write!(w, "[{}]", byte_size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        self.print_decl(w, hash)
    }

    pub fn cmp_id(
        _hash_a: &FileHash,
        a: &Self,
        _hash_b: &FileHash,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}

impl<'input> Print for LocalVariable<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(|w, state| self.print_size_and_decl(w, state))
    }

    fn diff(
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(a, b, |w, state, x| x.print_size_and_decl(w, state))
    }
}

impl<'a, 'input> DiffList for &'a LocalVariable<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 1;
        }
        match (a.ty(state.hash_a()), b.ty(state.hash_b())) {
            (Some(ty_a), Some(ty_b)) => {
                if Type::cmp_id(state.hash_a(), ty_a, state.hash_b(), ty_b) != cmp::Ordering::Equal
                {
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
}
