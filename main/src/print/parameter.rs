use std::cmp;

use parser::{FileHash, Parameter, Type, Unit};

use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use crate::Result;

pub(crate) fn print_decl(p: &Parameter, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    if let Some(name) = p.name() {
        write!(w, "{}: ", name)?;
    }
    print::types::print_ref(p.ty(hash), w, hash)?;
    Ok(())
}

fn print_size_and_decl(p: &Parameter, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
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
        state.expanded(
            |state| state.line(|w, state| print_size_and_decl(self, w, state)),
            |state| {
                if state.options().print_variable_locations {
                    print::register::print_list(state, self.registers().collect())?;
                    print::frame_location::print_list(state, self.frame_locations().collect())?;
                }
                Ok(())
            },
        )
    }

    fn diff(
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.expanded(
            |state| state.line(a, b, |w, state, x| print_size_and_decl(x, w, state)),
            |state| {
                if state.options().print_variable_locations {
                    print::register::diff_list(
                        state,
                        a.registers().collect(),
                        b.registers().collect(),
                    )?;
                    print::frame_location::diff_list(
                        state,
                        a.frame_locations().collect(),
                        b.frame_locations().collect(),
                    )?;
                }
                Ok(())
            },
        )
    }
}

impl<'input> DiffList for Parameter<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name().cmp(&b.name()) != cmp::Ordering::Equal {
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
