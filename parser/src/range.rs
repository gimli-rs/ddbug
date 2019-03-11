use std::mem;

/// An address range.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Range {
    /// The beginning of the address range (inclusive).
    pub begin: u64,

    /// The end of the address range (exclusive).
    pub end: u64,
}

impl Range {
    /// The size of the address range.
    #[inline]
    pub fn size(&self) -> u64 {
        self.end - self.begin
    }

    /// Return true if the range contains the value.
    #[inline]
    pub fn contains(&self, addr: u64) -> bool {
        self.begin <= addr && addr < self.end
    }
}

/// A list of address ranges.
#[derive(Debug, Default, Clone)]
pub struct RangeList {
    ranges: Vec<Range>,
}

impl RangeList {
    /// The ranges in the list.
    #[inline]
    pub fn list(&self) -> &[Range] {
        &self.ranges
    }

    /// The total size of the ranges in the list.
    pub fn size(&self) -> u64 {
        let mut size = 0;
        for range in &self.ranges {
            size += range.size();
        }
        size
    }

    /// Append a range, combining with previous range if possible.
    pub fn push(&mut self, range: Range) {
        if range.end <= range.begin {
            debug!("invalid range: {:?}", range);
            return;
        }
        if let Some(prev) = self.ranges.last_mut() {
            // Assume up to 15 bytes of padding if range.begin is aligned.
            // (This may be a wrong assumption, but does it matter and
            // how do we do better?)
            // TODO: make alignment configurable
            let padding = if range.begin == range.begin & !15 {
                15
            } else {
                0
            };
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

    /// Sort the ranges by beginning address, and combine ranges where possible.
    pub fn sort(&mut self) {
        self.ranges.sort_by(|a, b| a.begin.cmp(&b.begin));
        // Combine ranges by adding to a new list.
        let mut ranges = Vec::new();
        mem::swap(&mut ranges, &mut self.ranges);
        for range in ranges {
            self.push(range);
        }
    }

    /// Remove a list of ranges from the list.
    ///
    /// This handles ranges that only partially overlap with existing ranges.
    pub fn subtract(&self, other: &Self) -> Self {
        let mut ranges = RangeList::default();
        let mut other_ranges = other.ranges.iter();
        let mut other_range = other_ranges.next();
        for range in &*self.ranges {
            let mut range = *range;
            loop {
                match other_range {
                    Some(r) => {
                        // Is r completely before range?
                        if r.end <= range.begin {
                            other_range = other_ranges.next();
                            continue;
                        }
                        // Is r completely after range?
                        if r.begin >= range.end {
                            ranges.push(range);
                            break;
                        }
                        // Do we need to keep the head of the range?
                        if r.begin > range.begin {
                            ranges.push(Range {
                                begin: range.begin,
                                end: r.begin,
                            });
                        }
                        // Do we need to keep the tail of the range?
                        if r.end < range.end {
                            range.begin = r.end;
                            other_range = other_ranges.next();
                            continue;
                        }
                        break;
                    }
                    None => {
                        ranges.push(range);
                        break;
                    }
                }
            }
        }
        ranges.sort();
        ranges
    }
}
