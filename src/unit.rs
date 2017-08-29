use std::collections::{BTreeMap, HashSet};
use std::cmp;
use std::io::Write;

use gimli;

use {Options, Result, Sort};
use file::FileHash;
use function::{Function, FunctionOffset};
use print::{DiffState, PrintState, SortList};
use range::RangeList;
use types::{Type, TypeKind, TypeOffset};
use variable::{Variable, VariableOffset};

#[derive(Debug, Default)]
pub(crate) struct Unit<'input> {
    pub dir: Option<&'input [u8]>,
    pub name: Option<&'input [u8]>,
    pub language: Option<gimli::DwLang>,
    pub address_size: Option<u64>,
    pub low_pc: Option<u64>,
    pub ranges: RangeList,
    pub types: BTreeMap<TypeOffset, Type<'input>>,
    pub functions: BTreeMap<FunctionOffset, Function<'input>>,
    pub variables: BTreeMap<VariableOffset, Variable<'input>>,
}

impl<'input> Unit<'input> {
    fn size(&self) -> Option<u64> {
        self.ranges.size()
    }

    fn function_size(&self) -> Option<u64> {
        let mut size = 0;
        for function in self.functions.values() {
            if function.low_pc.is_some() {
                size += function.size.unwrap_or(0);
            }
        }
        if size != 0 {
            Some(size)
        } else {
            None
        }
    }

    fn variable_size(&self, hash: &FileHash) -> Option<u64> {
        let mut size = 0;
        for variable in self.variables.values() {
            if variable.address.is_some() {
                size += variable.byte_size(hash).unwrap_or(0);
            }
        }
        if size != 0 {
            Some(size)
        } else {
            None
        }
    }

    /// The offsets of types that should be printed inline.
    fn inline_types(&self, state: &PrintState) -> HashSet<usize> {
        let mut inline_types = HashSet::new();
        for ty in self.types.values() {
            // Assume all anonymous types are inline. We don't actually check
            // that they will be inline, but in future we could (eg for TypeDefs).
            // TODO: is this a valid assumption?
            if ty.is_anon() {
                inline_types.insert(ty.offset.0);
            }

            // Find all inline members.
            ty.visit_members(&mut |t| if t.is_inline(state.hash) {
                if let Some(offset) = t.ty {
                    inline_types.insert(offset.0);
                }
            });
        }
        inline_types
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    pub fn print(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if state.options.category_unit {
            state.line(w, |w, _state| {
                write!(w, "unit ")?;
                self.print_ref(w)
            })?;
            state.indent(|state| {
                if self.ranges.list().len() > 1 {
                    state.list("addresses", w, &(), self.ranges.list())?;
                } else {
                    state.line_option(w, |w, _state| self.print_address(w))?;
                }
                state.line_option(w, |w, _state| self.print_size(w))?;
                state.line_option(w, |w, _state| self.print_function_size(w))?;
                state.line_option(w, |w, state| self.print_variable_size(w, state.hash))
            })?;
            writeln!(w, "")?;
        }

        if state.options.category_type {
            let mut types = self.filter_types(state, false);
            state.sort_list(w, self, &mut *types)?;
        }
        if state.options.category_function {
            state.sort_list(w, self, &mut *self.filter_functions(state.options))?;
        }
        if state.options.category_variable {
            state.sort_list(w, &(), &mut *self.filter_variables(state.options))?;
        }
        Ok(())
    }

    pub fn diff(w: &mut Write, state: &mut DiffState, unit_a: &Unit, unit_b: &Unit) -> Result<()> {
        if state.options.category_unit {
            state.line(w, unit_a, unit_b, |w, _state, unit| {
                write!(w, "unit ")?;
                unit.print_ref(w)
            })?;
            state.indent(|state| {
                if unit_a.ranges.list().len() > 1 || unit_b.ranges.list().len() > 1 {
                    state.list(
                        "addresses",
                        w,
                        &(),
                        unit_a.ranges.list(),
                        &(),
                        unit_b.ranges.list(),
                    )?;
                } else {
                    state.line_option(w, unit_a, unit_b, |w, _state, x| x.print_address(w))?;
                }
                state.line_option_u64(w, "size", unit_a.size(), unit_b.size())?;
                state
                    .line_option_u64(w, "fn size", unit_a.function_size(), unit_b.function_size())?;
                state.line_option_u64(
                    w,
                    "var size",
                    unit_a.variable_size(state.a.hash),
                    unit_b.variable_size(state.b.hash),
                )
            })?;
            writeln!(w, "")?;
        }

        if state.options.category_type {
            let mut types_a = unit_a.filter_types(&state.a, true);
            let mut types_b = unit_b.filter_types(&state.b, true);
            state.sort_list(w, unit_a, &mut *types_a, unit_b, &mut *types_b)?;
        }
        if state.options.category_function {
            state.sort_list(
                w,
                unit_a,
                &mut *unit_a.filter_functions(state.options),
                unit_b,
                &mut *unit_b.filter_functions(state.options),
            )?;
        }
        if state.options.category_variable {
            state.sort_list(
                w,
                &(),
                &mut *unit_a.filter_variables(state.options),
                &(),
                &mut *unit_b.filter_variables(state.options),
            )?;
        }
        Ok(())
    }

    fn print_address(&self, w: &mut Write) -> Result<()> {
        if self.ranges.list().is_empty() {
            if let Some(low_pc) = self.low_pc {
                write!(w, "address: 0x{:x}", low_pc)?;
            }
        } else if self.ranges.list().len() == 1 {
            write!(w, "address: ")?;
            self.ranges.list()[0].print(w)?;
        }
        Ok(())
    }

    fn print_size(&self, w: &mut Write) -> Result<()> {
        if let Some(size) = self.size() {
            write!(w, "size: {}", size)?;
        }
        Ok(())
    }

    fn print_function_size(&self, w: &mut Write) -> Result<()> {
        if let Some(size) = self.function_size() {
            write!(w, "fn size: {}", size)?;
        }
        Ok(())
    }

    fn print_variable_size(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        if let Some(size) = self.variable_size(hash) {
            write!(w, "var size: {}", size)?;
        }
        Ok(())
    }

    /// Filter and the list of types using the options.
    /// Perform additional filtering when diffing.
    fn filter_types(&self, state: &PrintState, diff: bool) -> Vec<&Type> {
        let inline_types = self.inline_types(state);
        let filter_type = |t: &Type| {
            // Filter by user options.
            if !t.filter(state.options) {
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
                TypeKind::Base(..) |
                TypeKind::Array(..) |
                TypeKind::Function(..) |
                TypeKind::Unspecified(..) |
                TypeKind::PointerToMember(..) |
                TypeKind::Modifier(..) => return false,
            }
            // Filter out inline types.
            !inline_types.contains(&t.offset.0)
        };
        self.types.values().filter(|a| filter_type(a)).collect()
    }

    fn filter_functions(&self, options: &Options) -> Vec<&Function> {
        self.functions.values().filter(|a| a.filter(options)).collect()
    }

    fn filter_variables(&self, options: &Options) -> Vec<&Variable> {
        self.variables.values().filter(|a| a.filter(options)).collect()
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

impl<'input> SortList for Unit<'input> {
    type Arg = ();

    fn print(&self, w: &mut Write, state: &mut PrintState, _arg: &()) -> Result<()> {
        self.print(w, state)
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        _arg_a: &(),
        a: &Self,
        _arg_b: &(),
        b: &Self,
    ) -> Result<()> {
        Self::diff(w, state, a, b)
    }

    fn cmp_id(
        _state_a: &PrintState,
        a: &Self,
        _state_b: &PrintState,
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
        state_a: &PrintState,
        a: &Self,
        state_b: &PrintState,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        match options.sort {
            // TODO: sort by offset?
            Sort::None => cmp::Ordering::Equal,
            Sort::Name => Self::cmp_id(state_a, a, state_b, b, options),
            Sort::Size => a.size().cmp(&b.size()),
        }
    }
}
