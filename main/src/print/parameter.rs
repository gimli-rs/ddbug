use std::cmp;

use file::FileHash;
use function::Parameter;
use print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use types::Type;
use unit::Unit;
use Result;

pub(crate) fn print_decl(p: &Parameter, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    if let Some(name) = p.name() {
        write!(w, "{}: ", name)?;
    }
    match p.ty(hash) {
        Some(ty) => print::types::print_ref(&ty, w, hash)?,
        None => write!(w, "<anon>")?,
    }
    Ok(())
}

fn print_size_and_decl(p: &Parameter, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    match p.byte_size(hash) {
        Some(byte_size) => write!(w, "[{}]", byte_size)?,
        None => write!(w, "[??]")?,
    }
    write!(w, "\t")?;
    print_decl(p, w, hash)
}

impl<'input> Print for Parameter<'input> {
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

impl<'input> DiffList for Parameter<'input> {
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
