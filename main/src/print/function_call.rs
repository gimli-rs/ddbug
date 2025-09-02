use parser::{
    CalledFromAddress, FunctionCall, FunctionCallIndirectOrigin, FunctionCallKind,
    FunctionCallOrigin, FunctionCallParameter, Piece, Unit,
};

use crate::Result;
use crate::print::{self, Print, PrintState, ValuePrinter};

fn print_kind(kind: FunctionCallKind, w: &mut dyn ValuePrinter) -> Result<()> {
    match kind {
        FunctionCallKind::Normal => write!(w, "call"),
        FunctionCallKind::Tail => write!(w, "tail call"),
    }?;
    Ok(())
}

fn print_address(addr: Option<u64>, w: &mut dyn ValuePrinter) -> Result<()> {
    match addr {
        Some(addr) => write!(w, "{:#x}", addr),
        None => write!(w, "<unknown>"),
    }?;
    Ok(())
}

fn print_header(f: &FunctionCall, w: &mut dyn ValuePrinter) -> Result<()> {
    print_kind(f.kind(), w)?;
    write!(w, " at ")?;
    match f.called_from_address() {
        Some(addr) => match addr {
            CalledFromAddress::Specific(addr) => write!(w, "{:#x}", addr)?,
            CalledFromAddress::PreviousToReturnAddress => {
                write!(w, "<before return>")?;
            }
        },
        None => write!(w, "<unknown>")?,
    }
    print_origin(f.origin(), w)?;
    Ok(())
}

fn print_origin(origin: Option<&FunctionCallOrigin>, w: &mut dyn ValuePrinter) -> Result<()> {
    match origin {
        Some(FunctionCallOrigin::Direct(f)) => {
            write!(w, " -> {:?}", f.name())?;
        }
        Some(FunctionCallOrigin::Indirect(indirect)) => {
            write!(w, " -> ")?;
            match indirect {
                FunctionCallIndirectOrigin::Variable(v) => {
                    write!(w, "indirect(global:{})", v.name().unwrap_or("<unknown>"))?;
                }
                FunctionCallIndirectOrigin::LocalVariable(_) => {
                    write!(w, "indirect(local var)")?;
                }
                FunctionCallIndirectOrigin::Parameter(_param_offset) => {
                    write!(w, "indirect(param)")?;
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
                if let Some(return_addr) = self.return_address() {
                    state.field("return address", |w, _state| {
                        write!(w, "{:#x}", return_addr)?;
                        Ok(())
                    })?;
                }

                if !self.target().is_empty() {
                    state.field("target", |w, hash| print_pieces(self.target(), w, hash))?;
                }

                if let Some(source) = self.called_from_source() {
                    if state.options().print_source {
                        state.field("source", |w, _state| print::source::print(source, w, unit))?;
                    }
                }

                if !self.parameter_inputs().is_empty() {
                    state.field_expanded("parameters", |state| {
                        for param in self.parameter_inputs() {
                            param.print(state, unit)?;
                        }
                        Ok(())
                    })?;
                }

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
                    print_address(x.return_address(), w)
                })?;

                state.field("target", a, b, |w, hash, x| {
                    print_pieces(x.target(), w, hash)
                })?;

                if state.options().print_source {
                    state.field(
                        "source",
                        (arg_a, a),
                        (arg_b, b),
                        |w, _state, (unit, x)| match x.called_from_source() {
                            Some(source) => print::source::print(source, w, unit),
                            None => {
                                write!(w, "<none>")?;
                                Ok(())
                            }
                        },
                    )?;
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

fn print_pieces(pieces: &[Piece], w: &mut dyn ValuePrinter, hash: &parser::FileHash) -> Result<()> {
    if pieces.is_empty() {
        write!(w, "<none>")?;
        return Ok(());
    }

    for (i, piece) in pieces.iter().enumerate() {
        if i > 0 {
            write!(w, ", ")?;
        }
        match &piece.location {
            parser::Location::Address { address } => {
                write!(w, "{:#x}", address.get().unwrap_or(0))?;
            }
            parser::Location::Register { register } => {
                write!(w, "{}", register.name(hash).unwrap_or("<unknown reg>"))?;
            }
            parser::Location::RegisterOffset { register, offset } => {
                write!(
                    w,
                    "{}+{:#x}",
                    register.name(hash).unwrap_or("<unknown reg>"),
                    offset
                )?;
            }
            parser::Location::FrameOffset { offset } => {
                write!(w, "frame+{:#x}", offset)?;
            }
            parser::Location::CfaOffset { offset } => {
                write!(w, "cfa+{:#x}", offset)?;
            }
            parser::Location::Literal { value } => {
                write!(w, "lit:{:#x}", value)?;
            }
            parser::Location::TlsOffset { offset } => {
                write!(w, "tls+{:#x}", offset)?;
            }
            parser::Location::Empty => {
                write!(w, "<empty>")?;
            }
            parser::Location::Other => {
                write!(w, "<other>")?;
            }
        }
    }
    Ok(())
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
                if !self.location().is_empty() {
                    state.field("location", |w, hash| print_pieces(self.location(), w, hash))?;
                }

                if !self.value().is_empty() {
                    state.field("value", |w, hash| print_pieces(self.value(), w, hash))?;
                }

                if !self.data_location().is_empty() {
                    state.field("data_location", |w, hash| {
                        print_pieces(self.data_location(), w, hash)
                    })?;
                }

                if !self.data_value().is_empty() {
                    state.field("data_value", |w, hash| {
                        print_pieces(self.data_value(), w, hash)
                    })?;
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
                state.field("location", a, b, |w, hash, param| {
                    print_pieces(param.location(), w, hash)
                })?;

                state.field("value", a, b, |w, hash, param| {
                    print_pieces(param.value(), w, hash)
                })?;

                state.field("data_location", a, b, |w, hash, param| {
                    print_pieces(param.data_location(), w, hash)
                })?;

                state.field("data_value", a, b, |w, hash, param| {
                    print_pieces(param.data_value(), w, hash)
                })?;

                Ok(())
            },
        )
    }
}
