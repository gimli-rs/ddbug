use std::cmp;

use file::FileHash;
use print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use types::Type;
use unit::Unit;
use variable::LocalVariable;
use Result;

fn print_decl(v: &LocalVariable, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    write!(w, "{}: ", v.name().unwrap_or("<anon>"))?;
    print::types::print_ref_from_offset(w, hash, v.ty)?;
    Ok(())
}

fn print_size_and_decl(v: &LocalVariable, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    // TODO: print address?
    match v.byte_size(hash) {
        Some(byte_size) => write!(w, "[{}]", byte_size)?,
        None => write!(w, "[??]")?,
    }
    write!(w, "\t")?;
    print_decl(v, w, hash)
}

impl<'input> Print for LocalVariable<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(|w, state| print_size_and_decl(self, w, state))
    }

    fn diff(
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(a, b, |w, state, x| print_size_and_decl(x, w, state))
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
            (Some(ref ty_a), Some(ref ty_b)) => {
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
