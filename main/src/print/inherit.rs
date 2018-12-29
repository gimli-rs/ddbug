use std::cmp;

use parser::{FileHash, Inherit, Type};

use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use crate::Result;

pub(crate) fn print_list(state: &mut PrintState, inherits: &[Inherit]) -> Result<()> {
    if inherits.len() > 1 {
        state.field_expanded("inherits", |state| state.list(&(), inherits))?;
    } else if let Some(inherit) = inherits.first() {
        state.field("inherits", |w, hash| print_inherit(inherit, w, hash))?;
    }
    Ok(())
}

pub(crate) fn diff_list(
    state: &mut DiffState,
    inherits_a: &[Inherit],
    inherits_b: &[Inherit],
) -> Result<()> {
    if inherits_a.len() > 1 || inherits_b.len() > 1 {
        state.field_expanded("inherits", |state| {
            state.list(&(), inherits_a, &(), inherits_b)
        })?;
    } else {
        let inherit_a = inherits_a.first();
        let inherit_b = inherits_b.first();
        state.field("inherits", inherit_a, inherit_b, |w, hash, inherit| {
            if let Some(inherit) = inherit {
                print_inherit(inherit, w, hash)?;
            }
            Ok(())
        })?;
    }
    Ok(())
}

fn print_inherit(inherit: &Inherit, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    print::types::print_ref(inherit.ty(hash), w, hash)
}

impl Print for Inherit {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(|w, hash| print_inherit(self, w, hash))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.line(a, b, |w, hash, x| print_inherit(x, w, hash))
    }
}

impl DiffList for Inherit {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        match (a.ty(state.hash_a()), b.ty(state.hash_b())) {
            (Some(ref ty_a), Some(ref ty_b)) => {
                if Type::cmp_id(state.hash_a(), ty_a, state.hash_b(), ty_b) != cmp::Ordering::Equal
                {
                    cost += 2;
                }
            }
            (None, None) => {}
            _ => {
                cost += 2;
            }
        }
        cost
    }
}
