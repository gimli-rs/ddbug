use std::borrow::Cow;
use std::ops::Deref;

use gimli;

use file::FileHash;
use function::Function;
use range::RangeList;
use types::Type;
use variable::Variable;

#[derive(Debug, Default)]
pub struct Unit<'input> {
    pub dir: Option<Cow<'input, str>>,
    pub name: Option<Cow<'input, str>>,
    pub language: Option<gimli::DwLang>,
    pub address_size: Option<u64>,
    pub low_pc: Option<u64>,
    pub ranges: RangeList,
    pub types: Vec<Type<'input>>,
    pub functions: Vec<Function<'input>>,
    pub variables: Vec<Variable<'input>>,
}

impl<'input> Unit<'input> {
    pub fn dir(&self) -> Option<&str> {
        self.dir.as_ref().map(Cow::deref)
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(Cow::deref)
    }

    // Does not include unknown ranges.
    pub fn ranges(&self, hash: &FileHash) -> RangeList {
        let mut ranges = RangeList::default();
        for function in &self.functions {
            if let Some(range) = function.range() {
                ranges.push(range);
            }
        }
        for variable in &self.variables {
            if let Some(range) = variable.range(hash) {
                ranges.push(range);
            }
        }
        ranges.sort();
        ranges
    }

    pub fn unknown_ranges(&self, hash: &FileHash) -> RangeList {
        let mut ranges = RangeList::default();
        for range in self.ranges.list() {
            ranges.push(*range);
        }
        ranges.sort();
        ranges.subtract(&self.ranges(hash))
    }

    pub fn size(&self, hash: &FileHash) -> u64 {
        // TODO: account for padding and overlap between functions and variables?
        self.function_size() + self.variable_size(hash)
    }

    pub fn function_size(&self) -> u64 {
        let mut ranges = RangeList::default();
        for function in &self.functions {
            if let Some(range) = function.range() {
                ranges.push(range);
            }
        }
        ranges.sort();
        ranges.size()
    }

    pub fn variable_size(&self, hash: &FileHash) -> u64 {
        let mut ranges = RangeList::default();
        for variable in &self.variables {
            if let Some(range) = variable.range(hash) {
                ranges.push(range);
            }
        }
        ranges.sort();
        ranges.size()
    }
}
