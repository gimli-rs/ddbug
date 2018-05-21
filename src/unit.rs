use std::cmp;
use std::collections::HashSet;

use gimli;

use file::FileHash;
use function::Function;
use print::{DiffState, MergeIterator, MergeResult, Print, PrintState, SortList, ValuePrinter};
use range::{Range, RangeList};
use types::{Type, TypeKind};
use variable::Variable;
use {Options, Result, Sort};

#[derive(Debug, Default)]
pub(crate) struct Unit<'input> {
    pub dir: Option<&'input [u8]>,
    pub name: Option<&'input [u8]>,
    pub language: Option<gimli::DwLang>,
    pub address_size: Option<u64>,
    pub low_pc: Option<u64>,
    pub ranges: RangeList,
    pub types: Vec<Type<'input>>,
    pub functions: Vec<Function<'input>>,
    pub variables: Vec<Variable<'input>>,
}

impl<'input> Unit<'input> {
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
        for ty in Self::merged_types(hash_a, unit_a, hash_b, unit_b, options) {
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
            Self::merged_functions(hash_a, unit_a, hash_b, unit_b, options);
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

        for variable in Self::merged_variables(hash_a, unit_a, hash_b, unit_b, options) {
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

    fn merged_types<'a>(
        hash_a: &FileHash,
        unit_a: &'a Unit<'input>,
        hash_b: &FileHash,
        unit_b: &'a Unit<'input>,
        options: &Options,
    ) -> Vec<MergeResult<&'a Type<'input>, &'a Type<'input>>> {
        let mut types_a = unit_a.filter_types(hash_a, options, true);
        types_a.sort_by(|x, y| Type::cmp_id_for_sort(hash_a, x, hash_a, y, options));
        let mut types_b = unit_b.filter_types(hash_b, options, true);
        types_b.sort_by(|x, y| Type::cmp_id_for_sort(hash_b, x, hash_b, y, options));
        MergeIterator::new(types_a.into_iter(), types_b.into_iter(), |a, b| {
            Type::cmp_id(hash_a, a, hash_b, b)
        }).collect()
    }

    fn merged_functions<'a>(
        hash_a: &FileHash,
        unit_a: &'a Unit<'input>,
        hash_b: &FileHash,
        unit_b: &'a Unit<'input>,
        options: &Options,
    ) -> (
        Vec<MergeResult<&'a Function<'input>, &'a Function<'input>>>,
        Vec<MergeResult<&'a Function<'input>, &'a Function<'input>>>,
    ) {
        let mut functions_a = unit_a.filter_functions(options);
        functions_a.sort_by(|x, y| Function::cmp_id_for_sort(hash_a, x, hash_a, y, options));
        let mut functions_b = unit_b.filter_functions(options);
        functions_b.sort_by(|x, y| Function::cmp_id_for_sort(hash_b, x, hash_b, y, options));
        let mut functions = Vec::new();
        let mut inlined_functions = Vec::new();
        for function in
            MergeIterator::new(functions_a.into_iter(), functions_b.into_iter(), |a, b| {
                Function::cmp_id(hash_a, a, hash_b, b, options)
            }) {
            let inline = match function {
                MergeResult::Both(a, b) => a.size.is_none() || b.size.is_none(),
                MergeResult::Left(a) => a.size.is_none(),
                MergeResult::Right(b) => b.size.is_none(),
            };
            if inline {
                inlined_functions.push(function);
            } else {
                functions.push(function);
            }
        }
        (functions, inlined_functions)
    }

    fn merged_variables<'a>(
        hash_a: &FileHash,
        unit_a: &'a Unit<'input>,
        hash_b: &FileHash,
        unit_b: &'a Unit<'input>,
        options: &Options,
    ) -> Vec<MergeResult<&'a Variable<'input>, &'a Variable<'input>>> {
        let mut variables_a = unit_a.filter_variables(options);
        variables_a.sort_by(|x, y| Variable::cmp_id_for_sort(hash_a, x, hash_a, y, options));
        let mut variables_b = unit_b.filter_variables(options);
        variables_b.sort_by(|x, y| Variable::cmp_id_for_sort(hash_b, x, hash_b, y, options));
        MergeIterator::new(variables_a.into_iter(), variables_b.into_iter(), |a, b| {
            Variable::cmp_id(hash_a, a, hash_b, b, options)
        }).collect()
    }

    // Does not include unknown ranges.
    pub fn ranges(&self, hash: &FileHash) -> RangeList {
        let mut ranges = RangeList::default();
        for function in &self.functions {
            if let Some(range) = function.address() {
                ranges.push(range);
            }
        }
        for variable in &self.variables {
            if let Some(range) = variable.address(hash) {
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

    fn size(&self, hash: &FileHash) -> u64 {
        // TODO: account for padding and overlap between functions and variables?
        self.function_size() + self.variable_size(hash)
    }

    pub fn function_size(&self) -> u64 {
        let mut ranges = RangeList::default();
        for function in &self.functions {
            if let Some(range) = function.address() {
                ranges.push(range);
            }
        }
        ranges.sort();
        ranges.size()
    }

    pub fn variable_size(&self, hash: &FileHash) -> u64 {
        let mut ranges = RangeList::default();
        for variable in &self.variables {
            if let Some(range) = variable.address(hash) {
                ranges.push(range);
            }
        }
        ranges.sort();
        ranges.size()
    }

    /// The offsets of types that should be printed inline.
    fn inline_types(&self, hash: &FileHash) -> HashSet<usize> {
        let mut inline_types = HashSet::new();
        for ty in &self.types {
            // Assume all anonymous types are inline. We don't actually check
            // that they will be inline, but in future we could (eg for TypeDefs).
            // TODO: is this a valid assumption?
            if ty.is_anon() {
                inline_types.insert(ty.offset.0);
            }

            // Find all inline members.
            ty.visit_members(&mut |t| {
                if t.is_inline(hash) {
                    if let Some(offset) = t.ty {
                        inline_types.insert(offset.0);
                    }
                }
            });
        }
        inline_types
    }

    fn print_ref(&self, w: &mut ValuePrinter) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    pub fn print(&self, state: &mut PrintState) -> Result<()> {
        let options = state.options();

        let print_header = |state: &mut PrintState| {
            state.line(|w, _state| {
                write!(w, "unit ")?;
                self.print_ref(w)
            })
        };

        let print_unit = |state: &mut PrintState| {
            let unknown_ranges = self.unknown_ranges(state.hash());

            if options.print_unit_address {
                let ranges = self.ranges(state.hash());
                if ranges.list().len() > 1 {
                    state.field_collapsed("addresses", |state| state.list(&(), ranges.list()))?;
                } else {
                    let range = ranges.list().first().cloned();
                    state.field("address", |w, _state| self.print_address(w, range))?;
                }

                state.field_collapsed("unknown addresses", |state| {
                    state.list(&(), unknown_ranges.list())
                })?;
            }

            let fn_size = self.function_size();
            if fn_size != 0 {
                state.field_u64("fn size", fn_size)?;
            }

            let var_size = self.variable_size(state.hash());
            if var_size != 0 {
                state.field_u64("var size", var_size)?;
            }

            let unknown_size = unknown_ranges.size();
            if unknown_size != 0 {
                state.field_u64("unknown size", unknown_size)?;
            }

            state.line_break()?;
            Ok(())
        };

        let print_types = |state: &mut PrintState| -> Result<()> {
            if options.category_type {
                let mut types = self.filter_types(state.hash(), options, false);
                state.sort_list(self, &mut types)?;
            }
            Ok(())
        };
        let print_functions = |state: &mut PrintState| -> Result<()> {
            if options.category_function {
                let mut functions = self.filter_functions(options);
                state.sort_list(self, &mut functions)?;
            }
            Ok(())
        };
        let print_variables = |state: &mut PrintState| -> Result<()> {
            if options.category_variable {
                let mut variables = self.filter_variables(options);
                state.sort_list(self, &mut variables)?;
            }
            Ok(())
        };

        if options.html {
            state.collapsed(print_header, |state| {
                if options.category_unit {
                    print_unit(state)?;
                }
                state.field_collapsed("types", &print_types)?;
                state.field_collapsed("functions", &print_functions)?;
                state.field_collapsed("variables", &print_variables)?;
                Ok(())
            })?;
        } else {
            if options.category_unit {
                state.collapsed(print_header, print_unit)?;
            }
            print_types(state)?;
            print_functions(state)?;
            print_variables(state)?;
        }
        Ok(())
    }

    pub fn diff(state: &mut DiffState, unit_a: &Unit, unit_b: &Unit) -> Result<()> {
        let options = state.options();

        let diff_header = |state: &mut DiffState| {
            state.line(unit_a, unit_b, |w, _state, unit| {
                write!(w, "unit ")?;
                unit.print_ref(w)
            })
        };

        let diff_unit = |state: &mut DiffState| -> Result<()> {
            let unknown_ranges_a = unit_a.unknown_ranges(state.hash_a());
            let unknown_ranges_b = unit_b.unknown_ranges(state.hash_b());

            if options.print_unit_address {
                let ranges_a = unit_a.ranges(state.hash_a());
                let ranges_b = unit_b.ranges(state.hash_b());
                if ranges_a.list().len() > 1 || ranges_a.list().len() > 1 {
                    state.field_collapsed("addresses", |state| {
                        state.ord_list(&(), ranges_a.list(), &(), ranges_b.list())
                    })?;
                } else {
                    let range_a = ranges_a.list().first().cloned();
                    let range_b = ranges_b.list().first().cloned();
                    state.field(
                        "address",
                        (unit_a, range_a),
                        (unit_b, range_b),
                        |w, _state, (unit, range)| unit.print_address(w, range),
                    )?;
                }

                state.field_collapsed("unknown addresses", |state| {
                    state.ord_list(&(), unknown_ranges_a.list(), &(), unknown_ranges_b.list())
                })?;
            }

            let fn_size_a = unit_a.function_size();
            let fn_size_b = unit_b.function_size();
            if fn_size_a != 0 || fn_size_b != 0 {
                state.field_u64("fn size", fn_size_a, fn_size_b)?;
            }

            let var_size_a = unit_a.variable_size(state.hash_a());
            let var_size_b = unit_b.variable_size(state.hash_b());
            if var_size_a != 0 || var_size_b != 0 {
                state.field_u64("var size", var_size_a, var_size_b)?;
            }

            let unknown_size_a = unknown_ranges_a.size();
            let unknown_size_b = unknown_ranges_b.size();
            if unknown_size_a != 0 || unknown_size_b != 0 {
                state.field_u64("unknown size", unknown_size_a, unknown_size_b)?;
            }

            state.line_break()?;
            Ok(())
        };

        let diff_types = |state: &mut DiffState| -> Result<()> {
            if options.category_type {
                let mut types =
                    Self::merged_types(state.hash_a(), unit_a, state.hash_b(), unit_b, options);
                state.sort_list(unit_a, unit_b, &mut types)?;
            }
            Ok(())
        };
        let merged_functions = |state: &mut DiffState| {
            Self::merged_functions(state.hash_a(), unit_a, state.hash_b(), unit_b, options)
        };
        let diff_variables = |state: &mut DiffState| -> Result<()> {
            if options.category_variable {
                let mut variables =
                    Self::merged_variables(state.hash_a(), unit_a, state.hash_b(), unit_b, options);
                state.sort_list(unit_a, unit_b, &mut variables)?;
            }
            Ok(())
        };

        if options.html {
            state.collapsed(diff_header, |state| {
                if options.category_unit {
                    diff_unit(state)?;
                }
                state.field_collapsed("types", &diff_types)?;
                if options.category_function {
                    let (mut functions, mut inlined_functions) = merged_functions(state);
                    state.field_collapsed("functions", |state| {
                        state.sort_list(unit_a, unit_b, &mut functions)
                    })?;
                    state.field_collapsed("inlined functions", |state| {
                        state.sort_list(unit_a, unit_b, &mut inlined_functions)
                    })?;
                }
                state.field_collapsed("variables", &diff_variables)?;
                Ok(())
            })?;
        } else {
            if options.category_unit {
                state.collapsed(diff_header, diff_unit)?;
            }
            diff_types(state)?;
            if options.category_function {
                let (mut functions, mut inlined_functions) = merged_functions(state);
                state.sort_list(unit_a, unit_b, &mut functions)?;
                state.sort_list(unit_a, unit_b, &mut inlined_functions)?;
            }
            diff_variables(state)?;
        }
        Ok(())
    }

    fn print_address(&self, w: &mut ValuePrinter, range: Option<Range>) -> Result<()> {
        if let Some(range) = range {
            range.print_address(w)?;
        } else if let Some(low_pc) = self.low_pc {
            write!(w, "0x{:x}", low_pc)?;
        }
        Ok(())
    }

    /// Filter and the list of types using the options.
    /// Perform additional filtering when diffing.
    fn filter_types(&self, hash: &FileHash, options: &Options, diff: bool) -> Vec<&Type<'input>> {
        let inline_types = self.inline_types(hash);
        let filter_type = |t: &Type| {
            // Filter by user options.
            if !t.filter(options) {
                return false;
            }
            match t.kind {
                TypeKind::Struct(ref t) => {
                    // Hack for rust closures
                    // TODO: is there better way of identifying these, or a
                    // a way to match pairs for diffing?
                    if diff && t.name == Some(b"closure") {
                        return false;
                    }
                }
                TypeKind::Def(..) | TypeKind::Union(..) | TypeKind::Enumeration(..) => {}
                TypeKind::Base(..)
                | TypeKind::Array(..)
                | TypeKind::Function(..)
                | TypeKind::Unspecified(..)
                | TypeKind::PointerToMember(..)
                | TypeKind::Modifier(..) => return false,
            }
            // Filter out inline types.
            !inline_types.contains(&t.offset.0)
        };
        self.types.iter().filter(|a| filter_type(a)).collect()
    }

    fn filter_functions(&self, options: &Options) -> Vec<&Function<'input>> {
        self.functions
            .iter()
            .filter(|a| a.filter(options))
            .collect()
    }

    fn filter_variables(&self, options: &Options) -> Vec<&Variable<'input>> {
        self.variables
            .iter()
            .filter(|a| a.filter(options))
            .collect()
    }

    fn prefix_map(&self, options: &Options<'input>) -> (&'input [u8], &'input [u8]) {
        let name = self.name.unwrap_or(&[]);
        for &(old, new) in &options.prefix_map {
            if name.starts_with(old.as_bytes()) {
                return (new.as_bytes(), &name[old.len()..]);
            }
        }
        (&[], name)
    }

    /// Return true if this unit matches the filter options.
    pub fn filter(&self, options: &Options) -> bool {
        if let Some(filter) = options.filter_unit {
            let (prefix, suffix) = self.prefix_map(options);
            let iter = prefix.iter().chain(suffix);
            iter.cmp(filter.as_bytes()) == cmp::Ordering::Equal
        } else {
            true
        }
    }
}

impl<'input> Print for Unit<'input> {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        self.print(state)
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        Self::diff(state, a, b)
    }
}

impl<'input> SortList for Unit<'input> {
    fn cmp_id(
        _hash_a: &FileHash,
        a: &Self,
        _hash_b: &FileHash,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        let (prefix_a, suffix_a) = a.prefix_map(options);
        let (prefix_b, suffix_b) = b.prefix_map(options);
        let iter_a = prefix_a.iter().chain(suffix_a);
        let iter_b = prefix_b.iter().chain(suffix_b);
        iter_a.cmp(iter_b)
    }

    fn cmp_by(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        match options.sort {
            // TODO: sort by offset?
            Sort::None => cmp::Ordering::Equal,
            Sort::Name => Unit::cmp_id(hash_a, a, hash_b, b, options),
            Sort::Size => a.size(hash_a).cmp(&b.size(hash_b)),
        }
    }
}
