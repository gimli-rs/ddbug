use std::io::Write;
use std::mem;

use diffstate::{DiffList, DiffState, PrintList, PrintState};
use Result;

#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct Range {
    pub begin: u64,
    pub end: u64,
}

impl Range {
    pub fn print(&self, w: &mut Write) -> Result<()> {
        write!(w, "0x{:x}-0x{:x}", self.begin, self.end - 1)?;
        Ok(())
    }
}

impl PrintList for Range {
    type Arg = ();

    fn print_list(&self, w: &mut Write, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(w, |w, _state| self.print(w))
    }
}

impl DiffList for Range {
    fn step_cost() -> usize {
        3
    }

    fn diff_cost(_state: &DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        if a.begin != b.begin {
            cost += 4;
        }
        if a.end != b.end {
            cost += 2;
        }
        cost
    }

    fn diff_list(
        w: &mut Write,
        state: &mut DiffState,
        _arg_a: &(),
        a: &Self,
        _arg_b: &(),
        b: &Self,
    ) -> Result<()> {
        state.line(w, a, b, |w, _state, x| x.print(w))
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct RangeList {
    pub ranges: Vec<Range>,
}

impl RangeList {
    #[inline]
    pub fn list(&self) -> &[Range] {
        &self.ranges
    }

    pub fn size(&self) -> Option<u64> {
        let mut size = 0;
        for range in &self.ranges {
            size += range.end - range.begin;
        }
        if size != 0 {
            Some(size)
        } else {
            None
        }
    }

    // Append a range, combining with previous range if possible.
    pub fn push(&mut self, range: Range) {
        // Ranges starting at 0 are probably invalid.
        // TODO: is this always desired?
        if range.begin == 0 || range.end <= range.begin {
            return;
        }
        if let Some(prev) = self.ranges.last_mut() {
            // Assume up to 15 bytes of padding if range.begin is aligned.
            // (This may be a wrong assumption, but does it matter and
            // how do we do better?)
            // TODO: make alignment configurable
            let mut padding = 0;
            if range.begin == range.begin & !15 {
                padding = 15;
            }
            // Merge ranges if new range begins in or after previous range.
            // We don't care about merging in opposite order (that'll happen
            // when sorting).
            if range.begin >= prev.begin && range.begin <= prev.end + padding {
                if prev.end < range.end {
                    prev.end = range.end;
                }
                return;
            }
        }
        self.ranges.push(range);
    }

    pub fn sort(&mut self) {
        self.ranges.sort_by(|a, b| a.begin.cmp(&b.begin));
        // Combine ranges by adding to a new list.
        let mut ranges = Vec::new();
        mem::swap(&mut ranges, &mut self.ranges);
        for range in ranges {
            self.push(range);
        }
    }
}
