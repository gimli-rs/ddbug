use std::borrow::Cow;
use std::ops::Deref;

use gimli;

use file::FileHash;
use function::Function;
use print::{self, MergeResult};
use range::RangeList;
use types::Type;
use variable::Variable;
use Options;

#[derive(Debug, Default)]
pub(crate) struct Unit<'input> {
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

    pub fn assign_ids(&self, _options: &Options, mut id: usize) -> usize {
        for ty in &self.types {
            id += 1;
            ty.id.set(id);
        }
        for function in &self.functions {
            id += 1;
            function.id.set(id);
        }
        for variable in &self.variables {
            id += 1;
            variable.id.set(id);
        }
        id
    }

    pub fn assign_merged_ids(
        hash_a: &FileHash,
        unit_a: &Unit,
        hash_b: &FileHash,
        unit_b: &Unit,
        options: &Options,
        mut id: usize,
    ) -> usize {
        for ty in print::unit::merged_types(hash_a, unit_a, hash_b, unit_b, options) {
            id += 1;
            match ty {
                MergeResult::Both(a, b) => {
                    a.id.set(id);
                    b.id.set(id);
                }
                MergeResult::Left(a) => {
                    a.id.set(id);
                }
                MergeResult::Right(b) => {
                    b.id.set(id);
                }
            }
        }

        let (functions, inlined_functions) =
            print::unit::merged_functions(hash_a, unit_a, hash_b, unit_b, options);
        for function in functions.into_iter().chain(inlined_functions.into_iter()) {
            id += 1;
            match function {
                MergeResult::Both(a, b) => {
                    a.id.set(id);
                    b.id.set(id);
                }
                MergeResult::Left(a) => {
                    a.id.set(id);
                }
                MergeResult::Right(b) => {
                    b.id.set(id);
                }
            }
        }

        for variable in print::unit::merged_variables(hash_a, unit_a, hash_b, unit_b, options) {
            id += 1;
            match variable {
                MergeResult::Both(a, b) => {
                    a.id.set(id);
                    b.id.set(id);
                }
                MergeResult::Left(a) => {
                    a.id.set(id);
                }
                MergeResult::Right(b) => {
                    b.id.set(id);
                }
            }
        }

        id
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
