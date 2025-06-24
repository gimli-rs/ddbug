use parser::{
    CalledFromAddress, FunctionCall, FunctionCallIndirectOrigin, FunctionCallKind,
    FunctionCallOrigin, Piece, Unit,
};

use crate::print::{self, Print, PrintState, ValuePrinter};
use crate::Result;

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

fn print_target_location(pieces: &[Piece], w: &mut dyn ValuePrinter) -> Result<()> {
    if pieces.is_empty() {
        write!(w, "<unknown>")?;
        return Ok(());
    }

    // For now, just print the first piece - could be enhanced to show all pieces
    let piece = &pieces[0];
    match &piece.location {
        parser::Location::Address { address } => {
            write!(w, "{:#x}", address.get().unwrap_or(0))?;
        }
        parser::Location::Register { register } => {
            write!(w, "register {}", register.0)?;
        }
        parser::Location::RegisterOffset { register, offset } => {
            write!(w, "register {}+{:#x}", register.0, offset)?;
        }
        parser::Location::FrameOffset { offset } => {
            write!(w, "frame+{:#x}", offset)?;
        }
        parser::Location::CfaOffset { offset } => {
            write!(w, "cfa+{:#x}", offset)?;
        }
        parser::Location::Literal { value } => {
            write!(w, "value {:#x}", value)?;
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
                FunctionCallIndirectOrigin::Variable(_var_offset) => {
                    write!(w, "indirect(var)")?;
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
                    state.field("target", |w, _state| {
                        print_target_location(self.target(), w)
                    })?;
                }

                if let Some(source) = self.called_from_source() {
                    if state.options().print_source {
                        state.field("source", |w, _state| print::source::print(source, w, unit))?;
                    }
                }

                if !self.parameter_inputs().is_empty() {
                    state.field("parameters", |w, _state| {
                        write!(w, "{} parameters", self.parameter_inputs().len())?;
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

                state.field("target", a, b, |w, _state, x| {
                    print_target_location(x.target(), w)
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

                // TODO: Implement parameter diff when FunctionCallParameter gets its Print trait
                if !a.parameter_inputs().is_empty() || !b.parameter_inputs().is_empty() {
                    state.field("parameters", a, b, |w, _state, x| {
                        write!(w, "{} parameters", x.parameter_inputs().len())?;
                        Ok(())
                    })?;
                }

                Ok(())
            },
        )?;
        Ok(())
    }
}
