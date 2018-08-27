use std::cmp;

use parser::{FileHash, Unit, Variable};
use print::{self, DiffState, Print, PrintState, SortList, ValuePrinter};
use {Options, Result, Sort};

pub(crate) fn print(v: &Variable, state: &mut PrintState, unit: &Unit) -> Result<()> {
    state.collapsed(
        |state| state.line(|w, state| print_name(v, w, state)),
        |state| {
            state.field("linkage name", |w, _state| print_linkage_name(v, w))?;
            state.field("symbol name", |w, _state| print_symbol_name(v, w))?;
            if state.options().print_source {
                state.field("source", |w, _state| print_source(v, w, unit))?;
            }
            state.field("address", |w, _state| print_address(v, w))?;
            state.field("size", |w, state| print_size(v, w, state))?;
            state.field("declaration", |w, _state| print_declaration(v, w))
            // TODO: print anon type inline
        },
    )?;
    state.line_break()?;
    Ok(())
}

pub(crate) fn diff(
    state: &mut DiffState,
    unit_a: &Unit,
    a: &Variable,
    unit_b: &Unit,
    b: &Variable,
) -> Result<()> {
    state.collapsed(
        |state| state.line(a, b, |w, state, x| print_name(x, w, state)),
        |state| {
            state.field("linkage name", a, b, |w, _state, x| {
                print_linkage_name(x, w)
            })?;
            let flag = state.options().ignore_variable_symbol_name;
            state.ignore_diff(flag, |state| {
                state.field("symbol name", a, b, |w, _state, x| print_symbol_name(x, w))
            })?;
            if state.options().print_source {
                state.field(
                    "source",
                    (unit_a, a),
                    (unit_b, b),
                    |w, _state, (unit, x)| print_source(x, w, unit),
                )?;
            }
            let flag = state.options().ignore_variable_address;
            state.ignore_diff(flag, |state| {
                state.field("address", a, b, |w, _state, x| print_address(x, w))
            })?;
            state.field("size", a, b, |w, state, x| print_size(x, w, state))?;
            state.field("declaration", a, b, |w, _state, x| print_declaration(x, w))
        },
    )?;
    state.line_break()?;
    Ok(())
}

fn print_name(v: &Variable, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    write!(w, "var ")?;
    if let Some(namespace) = v.namespace() {
        print::namespace::print(namespace, w)?;
    }
    write!(w, "{}: ", v.name().unwrap_or("<anon>"))?;
    print::types::print_ref(v.ty(hash), w, hash)?;
    Ok(())
}

fn print_linkage_name(v: &Variable, w: &mut ValuePrinter) -> Result<()> {
    if let Some(linkage_name) = v.linkage_name() {
        write!(w, "{}", linkage_name)?;
    }
    Ok(())
}

fn print_symbol_name(v: &Variable, w: &mut ValuePrinter) -> Result<()> {
    if let Some(symbol_name) = v.symbol_name() {
        write!(w, "{}", symbol_name)?;
    }
    Ok(())
}

fn print_source(v: &Variable, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
    print::source::print(v.source(), w, unit)
}

fn print_address(v: &Variable, w: &mut ValuePrinter) -> Result<()> {
    if let Some(address) = v.address() {
        write!(w, "0x{:x}", address)?;
    }
    Ok(())
}

fn print_size(v: &Variable, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    if let Some(byte_size) = v.byte_size(hash) {
        write!(w, "{}", byte_size)?;
    } else if !v.is_declaration() {
        debug!("variable with no size");
    }
    Ok(())
}

fn print_declaration(v: &Variable, w: &mut ValuePrinter) -> Result<()> {
    if v.is_declaration() {
        write!(w, "yes")?;
    }
    Ok(())
}

impl<'input> Print for Variable<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        print(self, state, unit)
    }

    fn diff(state: &mut DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> Result<()> {
        diff(state, unit_a, a, unit_b, b)
    }
}

impl<'input> SortList for Variable<'input> {
    fn cmp_id(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        Variable::cmp_id(hash_a, a, hash_b, b)
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
            Sort::None => a.address().cmp(&b.address()),
            Sort::Name => SortList::cmp_id(hash_a, a, hash_b, b, options),
            Sort::Size => a.byte_size(hash_a).cmp(&b.byte_size(hash_b)),
        }
    }
}
