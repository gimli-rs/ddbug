use std::cmp;

use parser::{FileHash, Function, Range, Type, Unit, Variable};

use crate::filter;
use crate::print::{
    self, DiffState, MergeIterator, MergeResult, Print, PrintState, SortList, ValuePrinter,
};
use crate::{Options, Result, Sort};

pub(crate) fn merged_types<'a, 'input>(
    hash_a: &FileHash,
    unit_a: &'a Unit<'input>,
    hash_b: &FileHash,
    unit_b: &'a Unit<'input>,
    options: &Options,
) -> Vec<MergeResult<&'a Type<'input>, &'a Type<'input>>> {
    let mut types_a = filter::filter_types(unit_a, hash_a, options, true);
    types_a.sort_by(|x, y| Type::cmp_id_for_sort(hash_a, x, hash_a, y, options));
    let mut types_b = filter::filter_types(unit_b, hash_b, options, true);
    types_b.sort_by(|x, y| Type::cmp_id_for_sort(hash_b, x, hash_b, y, options));
    MergeIterator::new(types_a.into_iter(), types_b.into_iter(), |a, b| {
        Type::cmp_id(hash_a, a, hash_b, b)
    })
    .collect()
}

pub(crate) fn merged_functions<'a, 'input>(
    hash_a: &FileHash,
    unit_a: &'a Unit<'input>,
    hash_b: &FileHash,
    unit_b: &'a Unit<'input>,
    options: &Options,
) -> (
    Vec<MergeResult<&'a Function<'input>, &'a Function<'input>>>,
    Vec<MergeResult<&'a Function<'input>, &'a Function<'input>>>,
) {
    let mut functions_a = filter::filter_functions(unit_a, options);
    functions_a.sort_by(|x, y| Function::cmp_id_for_sort(hash_a, x, hash_a, y, options));
    let mut functions_b = filter::filter_functions(unit_b, options);
    functions_b.sort_by(|x, y| Function::cmp_id_for_sort(hash_b, x, hash_b, y, options));
    let mut functions = Vec::new();
    let mut inlined_functions = Vec::new();
    for function in MergeIterator::new(functions_a.into_iter(), functions_b.into_iter(), |a, b| {
        <Function as SortList>::cmp_id(hash_a, a, hash_b, b, options)
    }) {
        let inline = match function {
            MergeResult::Both(a, b) => a.size().is_none() || b.size().is_none(),
            MergeResult::Left(a) => a.size().is_none(),
            MergeResult::Right(b) => b.size().is_none(),
        };
        if inline {
            inlined_functions.push(function);
        } else {
            functions.push(function);
        }
    }
    (functions, inlined_functions)
}

pub(crate) fn merged_variables<'a, 'input>(
    hash_a: &FileHash,
    unit_a: &'a Unit<'input>,
    hash_b: &FileHash,
    unit_b: &'a Unit<'input>,
    options: &Options,
) -> Vec<MergeResult<&'a Variable<'input>, &'a Variable<'input>>> {
    let mut variables_a = filter::filter_variables(unit_a, options);
    variables_a.sort_by(|x, y| Variable::cmp_id_for_sort(hash_a, x, hash_a, y, options));
    let mut variables_b = filter::filter_variables(unit_b, options);
    variables_b.sort_by(|x, y| Variable::cmp_id_for_sort(hash_b, x, hash_b, y, options));
    MergeIterator::new(variables_a.into_iter(), variables_b.into_iter(), |a, b| {
        <Variable as SortList>::cmp_id(hash_a, a, hash_b, b, options)
    })
    .collect()
}

fn print_ref(unit: &Unit, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "{}", unit.name().unwrap_or("<anon>"))?;
    Ok(())
}

pub(crate) fn print(unit: &Unit, state: &mut PrintState) -> Result<()> {
    let options = state.options();

    let print_header = |state: &mut PrintState| {
        state.line(|w, _state| {
            write!(w, "unit ")?;
            print_ref(unit, w)
        })
    };

    let print_unit = |state: &mut PrintState| {
        let unknown_ranges = unit.unknown_ranges(state.hash());

        if options.print_unit_address {
            let ranges = unit.ranges(state.hash());
            if ranges.list().len() > 1 {
                state.field_collapsed("addresses", |state| state.list(&(), ranges.list()))?;
            } else {
                let range = ranges.list().first().cloned();
                state.field("address", |w, _state| print_address(unit, w, range))?;
            }

            state.field_collapsed("unknown addresses", |state| {
                state.list(&(), unknown_ranges.list())
            })?;
        }

        let fn_size = unit.function_size();
        if fn_size != 0 {
            state.field_u64("fn size", fn_size)?;
        }

        let var_size = unit.variable_size(state.hash());
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
            let mut types = filter::filter_types(unit, state.hash(), options, false);
            state.sort_list(unit, &mut types)?;
        }
        Ok(())
    };
    let print_functions = |state: &mut PrintState| -> Result<()> {
        if options.category_function {
            let mut functions = filter::filter_functions(unit, options);
            state.sort_list(unit, &mut functions)?;
        }
        Ok(())
    };
    let print_variables = |state: &mut PrintState| -> Result<()> {
        if options.category_variable {
            let mut variables = filter::filter_variables(unit, options);
            state.sort_list(unit, &mut variables)?;
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

pub(crate) fn diff(state: &mut DiffState, unit_a: &Unit, unit_b: &Unit) -> Result<()> {
    let options = state.options();

    let diff_header = |state: &mut DiffState| {
        state.line(unit_a, unit_b, |w, _state, unit| {
            write!(w, "unit ")?;
            print_ref(unit, w)
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
                    |w, _state, (unit, range)| print_address(unit, w, range),
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
            let mut types = merged_types(state.hash_a(), unit_a, state.hash_b(), unit_b, options);
            state.sort_list(unit_a, unit_b, &mut types)?;
        }
        Ok(())
    };
    let merged_functions = |state: &mut DiffState| {
        merged_functions(state.hash_a(), unit_a, state.hash_b(), unit_b, options)
    };
    let diff_variables = |state: &mut DiffState| -> Result<()> {
        if options.category_variable {
            let mut variables =
                merged_variables(state.hash_a(), unit_a, state.hash_b(), unit_b, options);
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

fn print_address(unit: &Unit, w: &mut dyn ValuePrinter, range: Option<Range>) -> Result<()> {
    if let Some(ref range) = range {
        print::range::print_address(range, w)?;
    } else if let Some(low_pc) = unit.address() {
        write!(w, "0x{:x}", low_pc)?;
    }
    Ok(())
}

impl<'input> Print for Unit<'input> {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        print(self, state)
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        diff(state, a, b)
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
        let (prefix_a, suffix_a) = options.prefix_map(a.name().unwrap_or(""));
        let (prefix_b, suffix_b) = options.prefix_map(b.name().unwrap_or(""));
        let iter_a = prefix_a.bytes().chain(suffix_a.bytes());
        let iter_b = prefix_b.bytes().chain(suffix_b.bytes());
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
