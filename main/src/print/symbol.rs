use std::cmp;

use parser::{Symbol, SymbolKind};
use print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use Result;

fn print_name(symbol: &Symbol, w: &mut ValuePrinter) -> Result<()> {
    match symbol.kind() {
        SymbolKind::Variable => write!(w, "var ")?,
        SymbolKind::Function => write!(w, "fn ")?,
    }
    match symbol.name() {
        Some(name) => write!(w, "{}", name)?,
        None => write!(w, "<anon>")?,
    }
    Ok(())
}

fn print_address(symbol: &Symbol, w: &mut ValuePrinter) -> Result<()> {
    print::range::print_address(&symbol.address(), w)
}

impl<'input> Print for Symbol<'input> {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.collapsed(
            |state| state.line(|w, _state| print_name(self, w)),
            |state| {
                state.field("address", |w, _state| print_address(self, w))?;
                state.field_u64("size", self.size())
            },
        )
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.collapsed(
            |state| state.line(a, b, |w, _state, x| print_name(x, w)),
            |state| {
                state.field("address", a, b, |w, _state, x| print_address(x, w))?;
                state.field_u64("size", a.size(), b.size())
            },
        )
    }
}

impl<'input> DiffList for Symbol<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(_state: &DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        if a.name().cmp(&b.name()) != cmp::Ordering::Equal {
            cost += 2;
        }
        cost
    }
}
