use std::cmp;
use std::io::Write;
use std::rc::Rc;

use {Options, Result, Sort};
use file::FileHash;
use namespace::Namespace;
use print::{DiffList, DiffState, Print, PrintState, SortList};
use range::Range;
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
    pub declaration: bool,
    pub address: Option<u64>,
    pub size: Option<u64>,
}

impl<'input> Variable<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
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

    pub fn print(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        state.line(w, |w, state| self.print_name(w, state))?;
        state.indent(|state| {
            state.line_option(w, |w, _state| self.print_linkage_name(w))?;
            state.line_option(w, |w, _state| self.print_symbol_name(w))?;
            state.line_option(w, |w, _state| self.print_address(w))?;
            state.line_option(w, |w, state| self.print_size(w, state))?;
            state.line_option(w, |w, _state| self.print_declaration(w))
            // TODO: print anon type inline
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    pub fn diff(w: &mut Write, state: &mut DiffState, a: &Variable, b: &Variable) -> Result<()> {
        state.line(w, a, b, |w, state, x| x.print_name(w, state))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, _state, x| x.print_linkage_name(w))?;
            let flag = state.options.ignore_variable_symbol_name;
            state.ignore_diff(
                flag,
                |state| state.line_option(w, a, b, |w, _state, x| x.print_symbol_name(w)),
            )?;
            let flag = state.options.ignore_variable_address;
            state.ignore_diff(
                flag,
                |state| state.line_option(w, a, b, |w, _state, x| x.print_address(w)),
            )?;
            state.line_option(w, a, b, |w, state, x| x.print_size(w, state))?;
            state.line_option(w, a, b, |w, _state, x| x.print_declaration(w))
        })?;
        writeln!(w, "")?;
        Ok(())
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

    fn print_symbol_name(&self, w: &mut Write) -> Result<()> {
        if let Some(symbol_name) = self.symbol_name {
            write!(w, "symbol name: {}", String::from_utf8_lossy(symbol_name))?;
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

    pub fn filter(&self, options: &Options) -> bool {
        if !self.declaration && self.address.is_none() {
            // TODO: make this configurable?
            return false;
        }
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }
}

impl<'input> Print for Variable<'input> {
    type Arg = ();

    fn print(&self, w: &mut Write, state: &mut PrintState, _arg: &()) -> Result<()> {
        self.print(w, state)
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        _arg_a: &(),
        a: &Self,
        _arg_b: &(),
        b: &Self,
    ) -> Result<()> {
        Self::diff(w, state, a, b)
    }
}

impl<'input> SortList for Variable<'input> {
    fn cmp_id(
        _state_a: &PrintState,
        a: &Self,
        _state_b: &PrintState,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }

    fn cmp_by(
        state_a: &PrintState,
        a: &Self,
        state_b: &PrintState,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        match options.sort {
            // TODO: sort by offset?
            Sort::None => a.address.cmp(&b.address),
            Sort::Name => Self::cmp_id(state_a, a, state_b, b, options),
            Sort::Size => a.byte_size(state_a.hash).cmp(&b.byte_size(state_b.hash)),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct LocalVariable<'input> {
    pub offset: VariableOffset,
    pub name: Option<&'input [u8]>,
    pub ty: Option<TypeOffset>,
    pub address: Option<u64>,
    pub size: Option<u64>,
}

impl<'input> LocalVariable<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
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

    pub fn cmp_id(
        _state_a: &PrintState,
        a: &Self,
        _state_b: &PrintState,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}

impl<'input> Print for LocalVariable<'input> {
    type Arg = Unit<'input>;

    fn print(&self, w: &mut Write, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(w, |w, state| self.print_size_and_decl(w, state))
    }

    fn diff(
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

impl<'a, 'input> DiffList for &'a LocalVariable<'input> {
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
}
