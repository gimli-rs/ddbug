use std::borrow::Cow;

use crate::file::FileHash;
use crate::function::Function;
use crate::range::RangeList;
use crate::types::Type;
use crate::variable::Variable;
use crate::Id;

/// A compilation unit.
#[derive(Debug, Default)]
pub struct Unit<'input> {
    pub(crate) id: Id,
    pub(crate) dir: Option<Cow<'input, str>>,
    pub(crate) name: Option<Cow<'input, str>>,
    pub(crate) language: Option<gimli::DwLang>,
    pub(crate) low_pc: Option<u64>,
    pub(crate) ranges: RangeList,
    pub(crate) types: Vec<Type<'input>>,
    pub(crate) functions: Vec<Function<'input>>,
    pub(crate) variables: Vec<Variable<'input>>,
}

impl<'input> Unit<'input> {
    /// The user defined id for this type.
    #[inline]
    pub fn id(&self) -> usize {
        self.id.get()
    }

    /// Set a user defined id for this type.
    #[inline]
    pub fn set_id(&self, id: usize) {
        self.id.set(id)
    }

    /// The working directory when the unit was compiled.
    pub fn dir(&self) -> Option<&str> {
        self.dir.as_deref()
    }

    /// The path of the primary source file.
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// The source language.
    // TODO: avoid gimli dependency.
    #[inline]
    pub fn language(&self) -> Option<gimli::DwLang> {
        self.language
    }

    /// The base address.
    #[inline]
    pub fn address(&self) -> Option<u64> {
        self.low_pc
    }

    /// The address ranges covered by functions and variables in the unit.
    ///
    /// Does not include unknown ranges.
    pub fn ranges(&self, hash: &FileHash) -> RangeList {
        let mut ranges = RangeList::default();
        for function in &self.functions {
            for range in function.ranges() {
                ranges.push(*range);
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

    /// The address ranges covered that are covered by the unit, but which
    /// are not known to be associated with any functions or variables.
    pub fn unknown_ranges(&self, hash: &FileHash) -> RangeList {
        let mut ranges = RangeList::default();
        for range in self.ranges.list() {
            ranges.push(*range);
        }
        ranges.sort();
        ranges.subtract(&self.ranges(hash))
    }

    /// The total size of all functions and variables.
    pub fn size(&self, hash: &FileHash) -> u64 {
        // TODO: account for padding and overlap between functions and variables?
        self.function_size() + self.variable_size(hash)
    }

    /// The total size of all functions.
    pub fn function_size(&self) -> u64 {
        let mut ranges = RangeList::default();
        for function in &self.functions {
            for range in function.ranges() {
                ranges.push(*range);
            }
        }
        ranges.sort();
        ranges.size()
    }

    /// The total size of all variables.
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

    /// The types declared or defined by this unit.
    #[inline]
    pub fn types(&self) -> &[Type<'input>] {
        &self.types
    }

    /// The functions declared or defined by this unit.
    #[inline]
    pub fn functions(&self) -> &[Function<'input>] {
        &self.functions
    }

    /// The variables declared or defined by this unit.
    #[inline]
    pub fn variables(&self) -> &[Variable<'input>] {
        &self.variables
    }
}
