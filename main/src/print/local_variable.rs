use std::cmp;

use parser::{FileHash, LocalVariable, Type, Unit};

use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use crate::Result;

pub(crate) fn print_decl(
    v: &LocalVariable,
    w: &mut dyn ValuePrinter,
    hash: &FileHash,
) -> Result<()> {
    write!(w, "{}: ", v.name().unwrap_or("<anon>"))?;
    print::types::print_ref(v.ty(hash), w, hash)?;
    Ok(())
}

fn print_size_and_decl(v: &LocalVariable, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    // TODO: print address?
    match v.byte_size(hash) {
        Some(byte_size) => write!(w, "[{}]", byte_size)?,
        None => write!(w, "[??]")?,
    }
    write!(w, "\t")?;
    print_decl(v, w, hash)
}

fn print_address(v: &LocalVariable, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(address) = v.address() {
        write!(w, "0x{:x}", address)?;
    }
    Ok(())
}

impl<'input> Print for LocalVariable<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.expanded(
            |state| state.line(|w, state| print_size_and_decl(self, w, state)),
            |state| {
                if state.options().print_variable_locations {
                    state.field("address", |w, _state| print_address(self, w))?;
                    print::register::print_list(state, self.registers().map(|x| x.1).collect())?;
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
                    // TODO: should we ignore diff for all locations?
                    let flag = state.options().ignore_variable_address;
                    state.ignore_diff(flag, |state| {
                        state.field("address", a, b, |w, _state, x| print_address(x, w))
                    })?;

                    print::register::diff_list(
                        state,
                        a.registers().map(|x| x.1).collect(),
                        b.registers().map(|x| x.1).collect(),
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

impl<'a, 'input> DiffList for &'a LocalVariable<'input> {
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
