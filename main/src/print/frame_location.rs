use std::cmp;

use parser::FrameLocation;

use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use crate::Result;

pub(crate) fn print_list(
    state: &mut PrintState,
    mut frame_locations: Vec<FrameLocation>,
) -> Result<()> {
    frame_locations.sort_unstable();
    frame_locations.dedup();
    if frame_locations.len() > 1 {
        state.field_expanded("stack frame", |state| state.list(&(), &frame_locations))?;
    } else if let Some(frame_location) = frame_locations.first() {
        state.field("stack frame", |w, _state| {
            print::frame_location::print(frame_location, w)
        })?;
    }
    Ok(())
}

pub(crate) fn diff_list(
    state: &mut DiffState,
    mut frame_locations_a: Vec<FrameLocation>,
    mut frame_locations_b: Vec<FrameLocation>,
) -> Result<()> {
    frame_locations_a.sort_unstable();
    frame_locations_a.dedup();
    frame_locations_b.sort_unstable();
    frame_locations_b.dedup();
    if frame_locations_a.len() > 1 || frame_locations_a.len() > 1 {
        state.field_expanded("stack frame", |state| {
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
    Ok(())
}

pub(crate) fn print(location: &FrameLocation, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "{}", location.offset)?;
    if let Some(bit_size) = location.bit_size.get() {
        write!(w, "[{}]", (bit_size + 7) / 8)?;
    }
    Ok(())
}

impl Print for FrameLocation {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(|w, _hash| print(self, w))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.line(a, b, |w, _hash, x| print(x, w))
    }
}

impl DiffList for FrameLocation {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(_state: &DiffState, _unit_a: &(), a: &Self, _unit_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        if a.cmp(&b) != cmp::Ordering::Equal {
            cost += 1;
        }
        cost
    }
}
