use std::cmp;

use parser::{FileHash, Register};
use print::{DiffList, DiffState, Print, PrintState, ValuePrinter};
use Result;

pub(crate) fn print(register: &Register, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    match register.name(hash) {
        Some(name) => write!(w, "{}", name)?,
        None => write!(w, "r{}", register.0)?,
    };
    Ok(())
}

impl Print for Register {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(|w, hash| print(self, w, hash))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.line(a, b, |w, hash, x| print(x, w, hash))
    }
}

impl DiffList for Register {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(_state: &DiffState, _unit_a: &(), a: &Self, _unit_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        if a.0.cmp(&b.0) != cmp::Ordering::Equal {
            cost += 1;
        }
        cost
    }
}
