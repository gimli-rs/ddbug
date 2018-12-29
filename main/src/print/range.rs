use crate::parser::Range;
use crate::print::{DiffState, Print, PrintState, ValuePrinter};
use crate::Result;

pub(crate) fn print_address(range: &Range, w: &mut ValuePrinter) -> Result<()> {
    if range.end > range.begin {
        write!(w, "0x{:x}-0x{:x}", range.begin, range.end - 1)?;
    } else {
        write!(w, "0x{:x}", range.begin)?;
    }
    Ok(())
}

pub(crate) fn print_address_and_size(range: &Range, w: &mut ValuePrinter) -> Result<()> {
    if range.end > range.begin {
        write!(
            w,
            "0x{:x}-0x{:x} ({})",
            range.begin,
            range.end - 1,
            range.end - range.begin
        )?;
    } else {
        write!(w, "0x{:x}", range.begin)?;
    }
    Ok(())
}

impl Print for Range {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(|w, _state| print_address_and_size(self, w))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.line(a, b, |w, _state, x| print_address_and_size(x, w))
    }
}
