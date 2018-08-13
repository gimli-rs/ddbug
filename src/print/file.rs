use file::{File, FileHash};
use filter;
use print::{self, DiffState, MergeIterator, MergeResult, PrintState, Printer, SortList};
use unit::Unit;
use {Options, Result};

fn assign_ids(file: &File, options: &Options) {
    let mut id = 0;
    for unit in &file.units {
        id = assign_ids_in_unit(unit, options, id);
    }
}

pub(crate) fn assign_ids_in_unit(unit: &Unit, _options: &Options, mut id: usize) -> usize {
    for ty in &unit.types {
        id += 1;
        ty.id.set(id);
    }
    for function in &unit.functions {
        id += 1;
        function.id.set(id);
    }
    for variable in &unit.variables {
        id += 1;
        variable.id.set(id);
    }
    id
}

fn assign_merged_ids(
    hash_a: &FileHash,
    file_a: &File,
    hash_b: &FileHash,
    file_b: &File,
    options: &Options,
) {
    let mut id = 0;
    for unit in merged_units(hash_a, file_a, hash_b, file_b, options) {
        match unit {
            MergeResult::Both(a, b) => {
                id = assign_merged_ids_in_unit(hash_a, a, hash_b, b, options, id);
            }
            MergeResult::Left(a) => {
                id = assign_ids_in_unit(a, options, id);
            }
            MergeResult::Right(b) => {
                id = assign_ids_in_unit(b, options, id);
            }
        }
    }
}

fn assign_merged_ids_in_unit(
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

fn merged_units<'a, 'input>(
    hash_a: &FileHash,
    file_a: &'a File<'input>,
    hash_b: &FileHash,
    file_b: &'a File<'input>,
    options: &Options,
) -> Vec<MergeResult<&'a Unit<'input>, &'a Unit<'input>>> {
    let mut units_a = filter::filter_units(file_a, options);
    units_a.sort_by(|x, y| Unit::cmp_id(hash_a, x, hash_a, y, options));
    let mut units_b = filter::filter_units(file_b, options);
    units_b.sort_by(|x, y| Unit::cmp_id(hash_b, x, hash_b, y, options));
    MergeIterator::new(units_a.into_iter(), units_b.into_iter(), |a, b| {
        Unit::cmp_id(hash_a, a, hash_b, b, options)
    }).collect()
}

pub fn print(file: &File, printer: &mut Printer, options: &Options) -> Result<()> {
    assign_ids(file, options);
    let hash = FileHash::new(file);
    let mut state = PrintState::new(printer, &hash, options);

    if options.category_file {
        state.collapsed(
            |state| {
                state.line(|w, _hash| {
                    write!(w, "file {}", file.path)?;
                    Ok(())
                })
            },
            |state| {
                let ranges = file.ranges(state.hash());
                let size = ranges.size();
                let fn_size = file.function_size();
                let var_size = file.variable_size(state.hash());
                let other_size = size - fn_size - var_size;
                if options.print_file_address {
                    state.field_collapsed("addresses", |state| state.list(&(), ranges.list()))?;
                }
                state.field_u64("size", size)?;
                state.field_u64("fn size", fn_size)?;
                state.field_u64("var size", var_size)?;
                state.field_u64("other size", other_size)?;
                state.field_collapsed("sections", |state| state.list(&(), &*file.sections))?;
                Ok(())
            },
        )?;
        state.line_break()?;
    }

    state.sort_list(&(), &mut filter::filter_units(file, options))
}

pub fn diff(printer: &mut Printer, file_a: &File, file_b: &File, options: &Options) -> Result<()> {
    let hash_a = FileHash::new(file_a);
    let hash_b = FileHash::new(file_b);
    assign_merged_ids(&hash_a, file_a, &hash_b, file_b, options);

    let mut state = DiffState::new(printer, &hash_a, &hash_b, options);

    if options.category_file {
        state.collapsed(
            |state| {
                state.line(file_a, file_b, |w, _hash, x| {
                    write!(w, "file {}", x.path)?;
                    Ok(())
                })
            },
            |state| {
                let ranges_a = file_a.ranges(state.hash_a());
                let ranges_b = file_b.ranges(state.hash_b());
                let size_a = ranges_a.size();
                let size_b = ranges_b.size();
                let fn_size_a = file_a.function_size();
                let fn_size_b = file_b.function_size();
                let var_size_a = file_a.variable_size(state.hash_a());
                let var_size_b = file_b.variable_size(state.hash_b());
                let other_size_a = size_a - fn_size_a - var_size_a;
                let other_size_b = size_b - fn_size_b - var_size_b;
                if options.print_file_address {
                    state.field_collapsed("addresses", |state| {
                        state.ord_list(&(), ranges_a.list(), &(), ranges_b.list())
                    })?;
                }
                state.field_u64("size", size_a, size_b)?;
                state.field_u64("fn size", fn_size_a, fn_size_b)?;
                state.field_u64("var size", var_size_a, var_size_b)?;
                state.field_u64("other size", other_size_a, other_size_b)?;
                // TODO: sort sections
                state.field_collapsed("sections", |state| {
                    state.list(&(), &*file_a.sections, &(), &*file_b.sections)
                })?;
                Ok(())
            },
        )?;
        state.line_break()?;
    }

    state.sort_list(
        &(),
        &(),
        &mut merged_units(&hash_a, file_a, &hash_b, file_b, options),
    )
}
