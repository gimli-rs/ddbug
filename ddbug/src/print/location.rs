use std::cmp;

use parser::{FileHash, Location, Piece, Range, Size, WasmSpace};

use crate::Result;
use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};

fn locations(pieces: &[(Range, Piece)]) -> Vec<(Location, Size)> {
    let mut locations: Vec<_> = pieces
        .iter()
        .filter_map(|(_range, piece)| {
            if piece.is_value {
                return None;
            }
            match piece.location {
                Location::Empty => None,
                // Variables display this separately.
                Location::Address { .. } => None,
                // We only display size for memory locations.
                Location::RegisterOffset { .. }
                | Location::FrameOffset { .. }
                | Location::CfaOffset { .. }
                | Location::WasmOffset { .. } => Some((piece.location, piece.bit_size)),
                // Size is not displayed, so omit it for dedup.
                _ => Some((piece.location, Size::none())),
            }
        })
        .collect();
    locations.sort_unstable();
    locations.dedup();
    locations
}

pub(crate) fn print_list(state: &mut PrintState, pieces: &[(Range, Piece)]) -> Result<()> {
    let locations = locations(pieces);
    if locations.len() > 1 {
        state.field_expanded("locations", |state| state.list(&(), &locations))?;
    } else if let Some((location, bit_size)) = locations.first() {
        state.field("location", |w, hash| print(*location, *bit_size, w, hash))?;
    }
    Ok(())
}

pub(crate) fn diff_list(
    state: &mut DiffState,
    pieces_a: &[(Range, Piece)],
    pieces_b: &[(Range, Piece)],
) -> Result<()> {
    let locations_a = locations(pieces_a);
    let locations_b = locations(pieces_b);
    if locations_a.len() > 1 || locations_b.len() > 1 {
        state.field_expanded("locations", |state| {
            state.ord_list(&(), &locations_a, &(), &locations_b)
        })?;
    } else if !locations_a.is_empty() || !locations_b.is_empty() {
        let location_a = locations_a.first();
        let location_b = locations_b.first();
        state.field("location", location_a, location_b, |w, hash, location| {
            if let Some((location, bit_size)) = location {
                print(*location, *bit_size, w, hash)?;
            }
            Ok(())
        })?;
    }
    Ok(())
}

pub(crate) fn print_pieces(state: &mut PrintState, pieces: &[Piece]) -> Result<()> {
    let locations: Vec<_> = pieces.iter().map(|p| (p.location, p.bit_size)).collect();
    state.list(&(), &locations)
}

pub(crate) fn diff_pieces(
    state: &mut DiffState,
    pieces_a: &[Piece],
    pieces_b: &[Piece],
) -> Result<()> {
    let locations_a: Vec<_> = pieces_a.iter().map(|p| (p.location, p.bit_size)).collect();
    let locations_b: Vec<_> = pieces_b.iter().map(|p| (p.location, p.bit_size)).collect();
    state.list(&(), &locations_a, &(), &locations_b)
}

pub(crate) fn print(
    location: Location,
    bit_size: Size,
    w: &mut dyn ValuePrinter,
    hash: &FileHash,
) -> Result<()> {
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
            } else {
                write!(w, "+0x{:x}", offset)?;
            }
            if let Some(bit_size) = bit_size.get() {
                write!(w, "[{}]", bit_size.div_ceil(8))?;
            }
        }
        Location::FrameOffset { offset } => {
            write!(w, "frame")?;
            if offset < 0 {
                write!(w, "-0x{:x}", -offset)?;
            } else {
                write!(w, "+0x{:x}", offset)?;
            }
            if let Some(bit_size) = bit_size.get() {
                write!(w, "[{}]", bit_size.div_ceil(8))?;
            }
        }
        Location::CfaOffset { offset } => {
            write!(w, "cfa")?;
            if offset < 0 {
                write!(w, "-0x{:x}", -offset)?;
            } else {
                write!(w, "+0x{:x}", offset)?;
            }
            if let Some(bit_size) = bit_size.get() {
                write!(w, "[{}]", bit_size.div_ceil(8))?;
            }
        }
        Location::Address { address } => {
            write!(w, "0x{:x}", address.get().unwrap_or(0))?;
        }
        Location::TlsOffset { offset } => {
            write!(w, "tls+0x{:x}", offset)?;
        }
        Location::Wasm { space, index } => {
            print_wasm_slot(space, index, w)?;
        }
        Location::WasmOffset {
            space,
            index,
            offset,
        } => {
            print_wasm_slot(space, index, w)?;
            if offset < 0 {
                write!(w, "-0x{:x}", -offset)?;
            } else {
                write!(w, "+0x{:x}", offset)?;
            }
            if let Some(bit_size) = bit_size.get() {
                write!(w, "[{}]", bit_size.div_ceil(8))?;
            }
        }
        Location::Other => {
            write!(w, "<other>")?;
        }
    }
    Ok(())
}

fn print_wasm_slot(space: WasmSpace, index: u32, w: &mut dyn ValuePrinter) -> Result<()> {
    let space = match space {
        WasmSpace::Local => "local",
        WasmSpace::Global => "global",
        WasmSpace::Stack => "stack",
    };
    write!(w, "wasm {} {}", space, index)?;
    Ok(())
}

impl Print for (Location, Size) {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(|w, hash| print(self.0, self.1, w, hash))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.line(a, b, |w, hash, x| print(x.0, x.1, w, hash))
    }
}

impl DiffList for (Location, Size) {
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
