use parser::{
    FunctionCall, FunctionCallIndirectOrigin, FunctionCallKind, FunctionCallOrigin,
    FunctionCallParameter, Unit,
};

use crate::Result;
use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};

fn print_kind(kind: FunctionCallKind, w: &mut dyn ValuePrinter) -> Result<()> {
    match kind {
        FunctionCallKind::Normal => write!(w, "call"),
        FunctionCallKind::Tail => write!(w, "tail call"),
    }?;
    Ok(())
}

fn print_address(f: &FunctionCall, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(address) = f.return_address() {
        write!(w, "{:#x}", address)?;
    }
    Ok(())
}

fn print_header(f: &FunctionCall, w: &mut dyn ValuePrinter) -> Result<()> {
    print_kind(f.kind(), w)?;
    write!(w, " at ")?;
    if let Some(addr) = f.called_from_address() {
        write!(w, "{:#x}", addr)?;
    } else if f.return_address().is_some() {
        write!(w, "<before return>")?;
    } else {
        write!(w, "<unknown>")?;
    }
    print_origin(f.origin(), w)?;
    Ok(())
}

fn print_origin(origin: Option<&FunctionCallOrigin>, w: &mut dyn ValuePrinter) -> Result<()> {
    match origin {
        Some(FunctionCallOrigin::Direct(f)) => {
            write!(w, " -> ")?;
            print::function::print_ref(f, w)?;
        }
        Some(FunctionCallOrigin::Indirect(indirect)) => {
            write!(w, " -> ")?;
            match indirect {
                FunctionCallIndirectOrigin::Variable(v) => {
                    write!(w, "indirect(global:{})", v.name().unwrap_or("<unknown>"))?;
                }
                FunctionCallIndirectOrigin::LocalVariable(_) => {
                    write!(w, "indirect(local variable)")?;
                }
                FunctionCallIndirectOrigin::Parameter(_param_offset) => {
                    write!(w, "indirect(parameter)")?;
                }
                FunctionCallIndirectOrigin::Member(_member_offset) => {
                    write!(w, "indirect(member)")?;
                }
            }
        }
        None => {} // Don't print anything if no origin information
    }
    Ok(())
}

impl<'input> Print for FunctionCall<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Self::Arg) -> parser::Result<()> {
        state.expanded(
            |state| state.line(|w, _state| print_header(self, w)),
            |state| {
                state.field("return address", |w, _state| print_address(self, w))?;

                if state.options().print_variable_locations {
                    state.field_expanded(
                        "target",
                        |state| {
                            print::register::print_list(
                                state,
                                self.target_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::print_list(
                                state,
                                self.target_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;
                }

                if state.options().print_source {
                    state.field("source", |w, _state| {
                        print::source::print(self.called_from_source(), w, unit)
                    })?;
                }

                state.field_expanded("parameters", |state| {
                    for param in self.parameter_inputs() {
                        param.print(state, unit)?;
                    }
                    Ok(())
                })?;

                Ok(())
            },
        )?;
        Ok(())
    }

    fn diff(
        state: &mut super::DiffState,
        arg_a: &Self::Arg,
        a: &Self,
        arg_b: &Self::Arg,
        b: &Self,
    ) -> parser::Result<()> {
        state.expanded(
            |state| state.line(a, b, |w, _state, x| print_header(x, w)),
            |state| {
                state.field("return address", a, b, |w, _state, x| {
                    print_address(x, w)
                })?;

                if state.options().print_variable_locations {
                    state.field_expanded(
                        "target",
                        |state| {
                            print::register::diff_list(
                                state,
                                a.target_registers().map(|x| x.1).collect(),
                                b.target_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::diff_list(
                                state,
                                a.target_frame_locations().map(|x| x.1).collect(),
                                b.target_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;
                }

                if state.options().print_source {
                    state.field("source", (arg_a, a), (arg_b, b), |w, _state, (unit, x)| {
                        print::source::print(x.called_from_source(), w, unit)
                    })?;
                }

                // Show detailed parameter diff
                if !a.parameter_inputs().is_empty() || !b.parameter_inputs().is_empty() {
                    state.field_expanded("parameters", |state| {
                        let params_a = a.parameter_inputs();
                        let params_b = b.parameter_inputs();
                        let max_len = params_a.len().max(params_b.len());

                        for i in 0..max_len {
                            match (params_a.get(i), params_b.get(i)) {
                                (Some(param_a), Some(param_b)) => {
                                    FunctionCallParameter::diff(
                                        state, arg_a, param_a, arg_b, param_b,
                                    )?;
                                }
                                (Some(param_a), None) => {
                                    state.prefix_delete(|state| param_a.print(state, arg_a))?;
                                }
                                (None, Some(param_b)) => {
                                    state.prefix_add(|state| param_b.print(state, arg_b))?;
                                }
                                (None, None) => unreachable!(),
                            }
                        }
                        Ok(())
                    })?;
                }

                Ok(())
            },
        )?;
        Ok(())
    }
}

impl<'input> DiffList for FunctionCall<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;

        // Compare call kind
        if a.kind().cmp(&b.kind()) != std::cmp::Ordering::Equal {
            cost += 1;
        }

        // Compare called from address
        if a.called_from_address().cmp(&b.called_from_address()) != std::cmp::Ordering::Equal {
            cost += 1;
        }

        // Compare return address
        if a.return_address().cmp(&b.return_address()) != std::cmp::Ordering::Equal {
            cost += 1;
        }

        // Compare origin
        match (a.origin(), b.origin()) {
            (Some(origin_a), Some(origin_b)) => {
                // This is a simplified comparison - could be more sophisticated
                if std::mem::discriminant(origin_a) != std::mem::discriminant(origin_b) {
                    cost += 2;
                } else {
                    match (origin_a, origin_b) {
                        (FunctionCallOrigin::Direct(f_a), FunctionCallOrigin::Direct(f_b)) => {
                            if parser::Function::cmp_id(state.hash_a(), f_a, state.hash_b(), f_b)
                                != std::cmp::Ordering::Equal
                            {
                                cost += 1;
                            }
                        }
                        (
                            FunctionCallOrigin::Indirect(ind_a),
                            FunctionCallOrigin::Indirect(ind_b),
                        ) => {
                            if std::mem::discriminant(ind_a) != std::mem::discriminant(ind_b) {
                                cost += 1;
                            }
                        }
                        _ => {}
                    }
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

fn print_parameter_header(
    param: &FunctionCallParameter,
    w: &mut dyn ValuePrinter,
    hash: &parser::FileHash,
) -> Result<()> {
    if let Some(param_type) = param.parameter() {
        if let Some(name) = param_type.name() {
            write!(w, "parameter: {}", name)?;
        } else {
            write!(w, "parameter: <unnamed>")?;
        }

        if let Some(ty) = param_type.ty(hash) {
            write!(w, " (")?;
            print::types::print_ref(Some(ty), w, hash)?;
            write!(w, ")")?;
        }
    } else {
        write!(w, "parameter: <unknown>")?;
    }
    Ok(())
}

impl<'input> Print for FunctionCallParameter<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Self::Arg) -> Result<()> {
        state.expanded(
            |state| state.line(|w, hash| print_parameter_header(self, w, hash)),
            |state| {
                if state.options().print_variable_locations {
                    state.field_expanded(
                        "location",
                        |state| {
                            print::register::print_list(
                                state,
                                self.registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::print_list(
                                state,
                                self.frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;

                    state.field_expanded(
                        "value",
                        |state| {
                            print::register::print_list(
                                state,
                                self.value_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::print_list(
                                state,
                                self.value_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;

                    state.field_expanded(
                        "data_location",
                        |state| {
                            print::register::print_list(
                                state,
                                self.dataref_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::print_list(
                                state,
                                self.dataref_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;

                    state.field_expanded(
                        "data_value_location",
                        |state| {
                            print::register::print_list(
                                state,
                                self.dataref_value_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::print_list(
                                state,
                                self.dataref_value_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;
                }

                Ok(())
            },
        )
    }

    fn diff(
        state: &mut print::DiffState,
        _unit_a: &Self::Arg,
        a: &Self,
        _unit_b: &Self::Arg,
        b: &Self,
    ) -> Result<()> {
        state.expanded(
            |state| {
                state.line(a, b, |w, hash, param| {
                    print_parameter_header(param, w, hash)
                })
            },
            |state| {
                if state.options().print_variable_locations {
                    state.field_expanded(
                        "location",
                        |state| {
                            print::register::diff_list(
                                state,
                                a.registers().map(|x| x.1).collect(),
                                b.registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::diff_list(
                                state,
                                a.frame_locations().map(|x| x.1).collect(),
                                b.frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;

                    state.field_expanded(
                        "value",
                        |state| {
                            print::register::diff_list(
                                state,
                                a.value_registers().map(|x| x.1).collect(),
                                b.value_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::diff_list(
                                state,
                                a.value_frame_locations().map(|x| x.1).collect(),
                                b.value_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;

                    state.field_expanded(
                        "data_location",
                        |state| {
                            print::register::diff_list(
                                state,
                                a.dataref_registers().map(|x| x.1).collect(),
                                b.dataref_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::diff_list(
                                state,
                                a.dataref_frame_locations().map(|x| x.1).collect(),
                                b.dataref_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;

                    state.field_expanded(
                        "data_value_location",
                        |state| {
                            print::register::diff_list(
                                state,
                                a.dataref_value_registers().map(|x| x.1).collect(),
                                b.dataref_value_registers().map(|x| x.1).collect(),
                            )?;
                            print::frame_location::diff_list(
                                state,
                                a.dataref_value_frame_locations().map(|x| x.1).collect(),
                                b.dataref_value_frame_locations().map(|x| x.1).collect(),
                            )?;
                            Ok(())
                        },
                    )?;
                }

                Ok(())
            },
        )
    }
}
