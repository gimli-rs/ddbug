use std::cmp;

use parser::Section;
use print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use Result;

fn print_name(section: &Section, w: &mut ValuePrinter) -> Result<()> {
    if let Some(ref segment) = section.segment() {
        write!(w, "{},", segment)?;
    }
    match section.name() {
        Some(name) => write!(w, "{}", name)?,
        None => write!(w, "<anon-section>")?,
    }
    Ok(())
}

fn print_address(section: &Section, w: &mut ValuePrinter) -> Result<()> {
    if let Some(ref address) = section.address() {
        print::range::print_address(address, w)?;
    }
    Ok(())
}

impl<'input> Print for Section<'input> {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.collapsed(
            |state| state.line(|w, _state| print_name(self, w)),
            |state| {
                state.field("address", |w, _state| print_address(self, w))?;
                state.field_u64("size", self.size)
            },
        )
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.collapsed(
            |state| state.line(a, b, |w, _state, x| print_name(x, w)),
            |state| {
                state.field("address", a, b, |w, _state, x| print_address(x, w))?;
                state.field_u64("size", a.size, b.size)
            },
        )
    }
}

impl<'input> DiffList for Section<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(_state: &DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal
            || a.segment.cmp(&b.segment) != cmp::Ordering::Equal
        {
            cost += 2;
        }
        cost
    }
}
