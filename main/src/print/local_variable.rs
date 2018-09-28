use std::cmp;

use parser::{FileHash, LocalVariable, Type, Unit};
use print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use Result;

fn print_decl(v: &LocalVariable, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    write!(w, "{}: ", v.name().unwrap_or("<anon>"))?;
    print::types::print_ref(v.ty(hash), w, hash)?;
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

fn print_address(v: &LocalVariable, w: &mut ValuePrinter) -> Result<()> {
    if let Some(address) = v.address() {
        write!(w, "0x{:x}", address)?;
    }
    Ok(())
}

impl<'input> Print for LocalVariable<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.collapsed(
            |state| state.line(|w, state| print_size_and_decl(self, w, state)),
            |state| {
                if state.options().print_variable_locations {
                    state.field("address", |w, _state| print_address(self, w))?;

                    let mut registers: Vec<_> = self.registers().collect();
                    registers.sort_unstable();
                    registers.dedup();
                    state.field_collapsed("registers", |state| state.list(&(), &registers))?;

                    let mut frame_locations: Vec<_> = self.frame_locations().collect();
                    frame_locations.sort_unstable();
                    frame_locations.dedup();
                    if frame_locations.len() > 1 {
                        state.field_collapsed("stack frame", |state| {
                            state.list(&(), &frame_locations)
                        })?;
                    } else if let Some(frame_location) = frame_locations.first() {
                        state.field("stack frame", |w, _state| {
                            print::frame_location::print(frame_location, w)
                        })?;
                    }
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
        state.collapsed(
            |state| state.line(a, b, |w, state, x| print_size_and_decl(x, w, state)),
            |state| {
                if state.options().print_variable_locations {
                    // TODO: should we ignore diff for all locations?
                    let flag = state.options().ignore_variable_address;
                    state.ignore_diff(flag, |state| {
                        state.field("address", a, b, |w, _state, x| print_address(x, w))
                    })?;

                    let mut registers_a: Vec<_> = a.registers().collect();
                    registers_a.sort_unstable();
                    registers_a.dedup();
                    let mut registers_b: Vec<_> = b.registers().collect();
                    registers_b.sort_unstable();
                    registers_b.dedup();
                    state.field_collapsed("registers", |state| {
                        state.list(&(), &registers_a, &(), &registers_b)
                    })?;

                    let mut frame_locations_a: Vec<_> = a.frame_locations().collect();
                    frame_locations_a.sort_unstable();
                    frame_locations_a.dedup();
                    let mut frame_locations_b: Vec<_> = b.frame_locations().collect();
                    frame_locations_b.sort_unstable();
                    frame_locations_b.dedup();
                    if frame_locations_a.len() > 1 || frame_locations_a.len() > 1 {
                        state.field_collapsed("stack frame", |state| {
                            state.ord_list(&(), &frame_locations_a, &(), &frame_locations_b)
                        })?;
                    } else {
                        let location_a = frame_locations_a.first();
                        let location_b = frame_locations_b.first();
                        state.field(
                            "stack frame",
                            location_a,
                            location_b,
                            |w, _state, location| {
                                if let Some(location) = location {
                                    print::frame_location::print(location, w)?;
                                }
                                Ok(())
                            },
                        )?;
                    }
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
