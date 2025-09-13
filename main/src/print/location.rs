use std::cmp;

use parser::{FileHash, Location, Piece};

use crate::Result;
use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};

pub(crate) fn print_list(state: &mut PrintState, locations: Vec<Location>) -> Result<()> {
    state.list(&(), &locations)
}

pub(crate) fn diff_list(
    state: &mut DiffState,
    locations_a: Vec<Location>,
    locations_b: Vec<Location>,
) -> Result<()> {
    state.list(&(), &locations_a, &(), &locations_b)
}

pub(crate) fn print_pieces(state: &mut PrintState, pieces: &[Piece]) -> Result<()> {
    print_list(state, pieces.iter().map(|p| p.location).collect())
}

pub(crate) fn diff_pieces(
    state: &mut DiffState,
    pieces_a: &[Piece],
    pieces_b: &[Piece],
) -> Result<()> {
    diff_list(
        state,
        pieces_a.iter().map(|p| p.location).collect(),
        pieces_b.iter().map(|p| p.location).collect(),
    )
}

pub(crate) fn print(location: Location, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    match location {
        Location::Empty => {}
        Location::Literal { value } => write!(w, "0x{:x}", value)?,
        Location::Register { register } => {
            print::register::print(register, w, hash)?;
        }
        Location::RegisterOffset { register, offset } => {
            print::register::print(register, w, hash)?;
            if offset < 0 {
                write!(w, "-0x{:x}", -offset)?;
            } else if offset > 0 {
                write!(w, "+0x{:x}", offset)?;
            }
        }
        Location::FrameOffset { offset } => {
            write!(w, "frame")?;
            if offset < 0 {
                write!(w, "-0x{:x}", -offset)?;
            } else if offset > 0 {
                write!(w, "+0x{:x}", offset)?;
            }
        }
        Location::CfaOffset { offset } => {
            write!(w, "cfa")?;
            if offset < 0 {
                write!(w, "-0x{:x}", -offset)?;
            } else if offset > 0 {
                write!(w, "+0x{:x}", offset)?;
            }
        }
        Location::Address { address } => {
            write!(w, "0x{:x}", address.get().unwrap_or(0))?;
        }
        Location::TlsOffset { offset } => {
            write!(w, "tls+0x{:x}", offset)?;
        }
        Location::Other => {
            write!(w, "<other>")?;
        }
    }
    Ok(())
}

impl Print for Location {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(|w, hash| print(*self, w, hash))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.line(a, b, |w, hash, x| print(*x, w, hash))
    }
}

impl DiffList for Location {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(_state: &DiffState, _unit_a: &(), a: &Self, _unit_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        if a.cmp(b) != cmp::Ordering::Equal {
            cost += 1;
        }
        cost
    }
}
