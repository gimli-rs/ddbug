use parser::{File, FileHash, Function, Type, Unit, Variable};

use crate::code::Code;
use crate::filter;
use crate::print::{
    DiffState, Id, MergeIterator, MergeResult, PrintHeader, PrintState, Printer, SortList,
};
use crate::{Error, Options, Result};

pub fn assign_ids(file: &File, options: &Options) -> Vec<Id> {
    let mut ids = Vec::new();
    for (unit_index, unit) in file.units().iter().enumerate() {
        unit.set_id(ids.len());
        ids.push(Id::Unit { unit_index });
        assign_ids_in_unit(unit_index, unit, options, &mut ids);
    }
    ids
}

pub(crate) fn assign_ids_in_unit(
    unit_index: usize,
    unit: &Unit,
    _options: &Options,
    ids: &mut Vec<Id>,
) {
    for (type_index, ty) in unit.types().iter().enumerate() {
        ty.set_id(ids.len());
        ids.push(Id::Type {
            unit_index,
            type_index,
        });
    }
    for (function_index, function) in unit.functions().iter().enumerate() {
        function.set_id(ids.len());
        ids.push(Id::Function {
            unit_index,
            function_index,
        });
    }
    for (variable_index, variable) in unit.variables().iter().enumerate() {
        variable.set_id(ids.len());
        ids.push(Id::Variable {
            unit_index,
            variable_index,
        });
    }
}

pub fn assign_merged_ids(file_a: &File, file_b: &File, options: &Options) -> Vec<(Id, Id)> {
    let ref hash_a = FileHash::new(file_a);
    let ref hash_b = FileHash::new(file_b);

    let mut ids = Vec::new();
    let mut units_a = filter::enumerate_and_filter_units(file_a, options);
    units_a.sort_by(|x, y| Unit::cmp_id(hash_a, x.1, hash_a, y.1, options));
    let mut units_b = filter::enumerate_and_filter_units(file_b, options);
    units_b.sort_by(|x, y| Unit::cmp_id(hash_b, x.1, hash_b, y.1, options));
    let units = MergeIterator::new(units_a.into_iter(), units_b.into_iter(), |a, b| {
        Unit::cmp_id(hash_a, a.1, hash_b, b.1, options)
    });
    for unit in units {
        match unit {
            MergeResult::Both((unit_index_a, a), (unit_index_b, b)) => {
                a.set_id(ids.len());
                b.set_id(ids.len());
                ids.push((
                    Id::Unit {
                        unit_index: unit_index_a,
                    },
                    Id::Unit {
                        unit_index: unit_index_b,
                    },
                ));
                assign_merged_ids_in_unit(
                    hash_a,
                    unit_index_a,
                    a,
                    hash_b,
                    unit_index_b,
                    b,
                    options,
                    &mut ids,
                );
            }
            MergeResult::Left((unit_index, unit)) => {
                unit.set_id(ids.len());
                ids.push((Id::Unit { unit_index }, Id::None));
                assign_unmerged_ids_in_unit(unit_index, unit, options, &mut ids, true);
            }
            MergeResult::Right((unit_index, unit)) => {
                unit.set_id(ids.len());
                ids.push((Id::None, Id::Unit { unit_index }));
                assign_unmerged_ids_in_unit(unit_index, unit, options, &mut ids, false);
            }
        }
    }
    ids
}

pub(crate) fn assign_unmerged_ids_in_unit(
    unit_index: usize,
    unit: &Unit,
    _options: &Options,
    ids: &mut Vec<(Id, Id)>,
    left: bool,
) {
    for (type_index, ty) in unit.types().iter().enumerate() {
        ty.set_id(ids.len());
        let id = Id::Type {
            unit_index,
            type_index,
        };
        if left {
            ids.push((id, Id::None));
        } else {
            ids.push((Id::None, id));
        }
    }
    for (function_index, function) in unit.functions().iter().enumerate() {
        function.set_id(ids.len());
        let id = Id::Function {
            unit_index,
            function_index,
        };
        if left {
            ids.push((id, Id::None));
        } else {
            ids.push((Id::None, id));
        }
    }
    for (variable_index, variable) in unit.variables().iter().enumerate() {
        variable.set_id(ids.len());
        let id = Id::Variable {
            unit_index,
            variable_index,
        };
        if left {
            ids.push((id, Id::None));
        } else {
            ids.push((Id::None, id));
        }
    }
}

fn assign_merged_ids_in_unit(
    hash_a: &FileHash,
    unit_a_index: usize,
    unit_a: &Unit,
    hash_b: &FileHash,
    unit_b_index: usize,
    unit_b: &Unit,
    options: &Options,
    ids: &mut Vec<(Id, Id)>,
) {
    let mut types_a = filter::enumerate_and_filter_types(unit_a, hash_a, options, true);
    types_a.sort_by(|x, y| Type::cmp_id_for_sort(hash_a, x.1, hash_a, y.1, options));
    let mut types_b = filter::enumerate_and_filter_types(unit_b, hash_b, options, true);
    types_b.sort_by(|x, y| Type::cmp_id_for_sort(hash_b, x.1, hash_b, y.1, options));
    let types = MergeIterator::new(types_a.into_iter(), types_b.into_iter(), |a, b| {
        Type::cmp_id(hash_a, a.1, hash_b, b.1)
    });
    for ty in types {
        match ty {
            MergeResult::Both((type_index_a, a), (type_index_b, b)) => {
                a.set_id(ids.len());
                b.set_id(ids.len());
                ids.push((
                    Id::Type {
                        unit_index: unit_a_index,
                        type_index: type_index_a,
                    },
                    Id::Type {
                        unit_index: unit_b_index,
                        type_index: type_index_b,
                    },
                ));
            }
            MergeResult::Left((type_index, ty)) => {
                ty.set_id(ids.len());
                ids.push((
                    Id::Type {
                        unit_index: unit_a_index,
                        type_index,
                    },
                    Id::None,
                ));
            }
            MergeResult::Right((type_index, ty)) => {
                ty.set_id(ids.len());
                ids.push((
                    Id::None,
                    Id::Type {
                        unit_index: unit_b_index,
                        type_index,
                    },
                ));
            }
        }
    }

    let mut functions_a = filter::enumerate_and_filter_functions(unit_a, options);
    functions_a.sort_by(|x, y| Function::cmp_id_for_sort(hash_a, x.1, hash_a, y.1, options));
    let mut functions_b = filter::enumerate_and_filter_functions(unit_b, options);
    functions_b.sort_by(|x, y| Function::cmp_id_for_sort(hash_b, x.1, hash_b, y.1, options));
    let mut functions = Vec::new();
    let mut inlined_functions = Vec::new();
    for function in MergeIterator::new(functions_a.into_iter(), functions_b.into_iter(), |a, b| {
        <Function as SortList>::cmp_id(hash_a, a.1, hash_b, b.1, options)
    }) {
        let inline = match function {
            MergeResult::Both(a, b) => a.1.size().is_none() || b.1.size().is_none(),
            MergeResult::Left(a) => a.1.size().is_none(),
            MergeResult::Right(b) => b.1.size().is_none(),
        };
        if inline {
            inlined_functions.push(function);
        } else {
            functions.push(function);
        }
    }
    for function in functions.into_iter().chain(inlined_functions.into_iter()) {
        match function {
            MergeResult::Both((function_index_a, a), (function_index_b, b)) => {
                a.set_id(ids.len());
                b.set_id(ids.len());
                ids.push((
                    Id::Function {
                        unit_index: unit_a_index,
                        function_index: function_index_a,
                    },
                    Id::Function {
                        unit_index: unit_b_index,
                        function_index: function_index_b,
                    },
                ));
            }
            MergeResult::Left((function_index, function)) => {
                function.set_id(ids.len());
                ids.push((
                    Id::Function {
                        unit_index: unit_a_index,
                        function_index,
                    },
                    Id::None,
                ));
            }
            MergeResult::Right((function_index, function)) => {
                function.set_id(ids.len());
                ids.push((
                    Id::None,
                    Id::Function {
                        unit_index: unit_b_index,
                        function_index,
                    },
                ));
            }
        }
    }

    let mut variables_a = filter::enumerate_and_filter_variables(unit_a, options);
    variables_a.sort_by(|x, y| Variable::cmp_id_for_sort(hash_a, x.1, hash_a, y.1, options));
    let mut variables_b = filter::enumerate_and_filter_variables(unit_b, options);
    variables_b.sort_by(|x, y| Variable::cmp_id_for_sort(hash_b, x.1, hash_b, y.1, options));
    let variables = MergeIterator::new(variables_a.into_iter(), variables_b.into_iter(), |a, b| {
        <Variable as SortList>::cmp_id(hash_a, a.1, hash_b, b.1, options)
    });
    for variable in variables {
        match variable {
            MergeResult::Both((variable_index_a, a), (variable_index_b, b)) => {
                a.set_id(ids.len());
                b.set_id(ids.len());
                ids.push((
                    Id::Variable {
                        unit_index: unit_a_index,
                        variable_index: variable_index_a,
                    },
                    Id::Variable {
                        unit_index: unit_b_index,
                        variable_index: variable_index_b,
                    },
                ));
            }
            MergeResult::Left((variable_index, variable)) => {
                variable.set_id(ids.len());
                ids.push((
                    Id::Variable {
                        unit_index: unit_a_index,
                        variable_index,
                    },
                    Id::None,
                ));
            }
            MergeResult::Right((variable_index, variable)) => {
                variable.set_id(ids.len());
                ids.push((
                    Id::None,
                    Id::Variable {
                        unit_index: unit_b_index,
                        variable_index,
                    },
                ));
            }
        }
    }
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
    })
    .collect()
}

pub fn print(file: &File, printer: &mut dyn Printer, options: &Options) -> Result<()> {
    let hash = FileHash::new(file);
    let code = Code::new(file);
    let mut state = PrintState::new(printer, &hash, code.as_ref(), options);

    if options.category_file {
        state.collapsed(
            |state| {
                state.line(|w, _hash| {
                    write!(w, "file {}", file.path())?;
                    Ok(())
                })
            },
            |state| {
                let ranges = file.ranges(state.hash());
                let size = ranges.size();
                let fn_size = file.function_size();
                let var_size = file.variable_size(state.hash());
                let other_size = size.checked_sub(fn_size + var_size).unwrap_or_else(|| {
                    // TODO: fix our calculations so this doesn't happen
                    debug!("function or variable sizes are too large");
                    0
                });
                if options.print_file_address {
                    state.field_collapsed("addresses", |state| state.list(&(), ranges.list()))?;
                }
                state.field_u64("size", size)?;
                state.field_u64("fn size", fn_size)?;
                state.field_u64("var size", var_size)?;
                state.field_u64("other size", other_size)?;
                state.field_collapsed("sections", |state| state.list(&(), file.sections()))?;
                Ok(())
            },
        )?;
        state.line_break()?;
    }

    state.sort_list(&(), &mut filter::filter_units(file, options))
}

pub fn parent_id(id: Id, file: &File) -> Option<usize> {
    match id {
        Id::Type { unit_index, .. }
        | Id::Function { unit_index, .. }
        | Id::Variable { unit_index, .. } => {
            if let Some(unit) = file.units().get(unit_index) {
                return Some(unit.id());
            }
        }
        _ => {}
    }
    None
}

pub fn print_id(
    id: Id,
    detail: Option<&str>,
    file: &File,
    printer: &mut dyn Printer,
    options: &Options,
) -> Result<()> {
    match id {
        Id::Unit { unit_index } => {
            if let Some(unit) = file.units().get(unit_index) {
                let hash = FileHash::new(file);
                let code = Code::new(file);
                let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
                return super::unit::print_body(unit, &mut state);
            }
        }
        Id::Type {
            unit_index,
            type_index,
        } => {
            if let Some(unit) = file.units().get(unit_index) {
                if let Some(ty) = unit.types().get(type_index) {
                    let hash = FileHash::new(file);
                    let code = Code::new(file);
                    let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
                    let kind = super::types::kind(ty)?;
                    return kind.print_body(&mut state, unit);
                }
            }
        }
        Id::Function {
            unit_index,
            function_index,
        } => {
            if let Some(unit) = file.units().get(unit_index) {
                if let Some(function) = unit.functions().get(function_index) {
                    let hash = FileHash::new(file);
                    let code = Code::new(file);
                    let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
                    match detail {
                        None => return function.print_body(&mut state, unit),
                        Some("code") => {
                            let details = function.details(state.hash());
                            return super::function::print_instructions(
                                &mut state, function, &details,
                            );
                        }
                        _ => {}
                    }
                }
            }
        }
        _ => {}
    }
    Ok(())
}

pub fn diff(
    printer: &mut dyn Printer,
    file_a: &File,
    file_b: &File,
    options: &Options,
) -> Result<()> {
    let hash_a = FileHash::new(file_a);
    let hash_b = FileHash::new(file_b);
    let code_a = Code::new(file_a);
    let code_b = Code::new(file_b);

    let mut state = DiffState::new(
        printer,
        &hash_a,
        &hash_b,
        code_a.as_ref(),
        code_b.as_ref(),
        options,
    );

    if options.category_file {
        state.collapsed(
            |state| {
                state.line(file_a, file_b, |w, _hash, x| {
                    write!(w, "file {}", x.path())?;
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
                    state.list(&(), file_a.sections(), &(), file_b.sections())
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

pub fn diff_id(
    id: (Id, Id),
    file_a: &File,
    file_b: &File,
    printer: &mut dyn Printer,
    options: &Options,
) -> Result<()> {
    match id {
        (
            Id::Unit {
                unit_index: unit_index_a,
            },
            Id::Unit {
                unit_index: unit_index_b,
            },
        ) => || -> Option<Result<()>> {
            let unit_a = file_a.units().get(unit_index_a)?;
            let unit_b = file_b.units().get(unit_index_b)?;
            let hash_a = FileHash::new(file_a);
            let hash_b = FileHash::new(file_b);
            let code_a = Code::new(file_a);
            let code_b = Code::new(file_b);
            let mut state = DiffState::new(
                printer,
                &hash_a,
                &hash_b,
                code_a.as_ref(),
                code_b.as_ref(),
                options,
            );
            Some(super::unit::diff_body(&mut state, unit_a, unit_b))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (Id::Unit { unit_index }, Id::None) => || -> Option<Result<()>> {
            let unit = file_a.units().get(unit_index)?;
            let hash = FileHash::new(file_a);
            let code = Code::new(file_a);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            Some(super::unit::print_body(unit, &mut state))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (Id::None, Id::Unit { unit_index }) => || -> Option<Result<()>> {
            let unit = file_b.units().get(unit_index)?;
            let hash = FileHash::new(file_b);
            let code = Code::new(file_b);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            Some(super::unit::print_body(unit, &mut state))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (
            Id::Type {
                unit_index: unit_index_a,
                type_index: type_index_a,
            },
            Id::Type {
                unit_index: unit_index_b,
                type_index: type_index_b,
            },
        ) => || -> Option<Result<()>> {
            let unit_a = file_a.units().get(unit_index_a)?;
            let unit_b = file_b.units().get(unit_index_b)?;
            let type_a = unit_a.types().get(type_index_a)?;
            let type_b = unit_b.types().get(type_index_b)?;
            let hash_a = FileHash::new(file_a);
            let hash_b = FileHash::new(file_b);
            let code_a = Code::new(file_a);
            let code_b = Code::new(file_b);
            let mut state = DiffState::new(
                printer,
                &hash_a,
                &hash_b,
                code_a.as_ref(),
                code_b.as_ref(),
                options,
            );
            Some(super::types::diff_body(
                &mut state, unit_a, type_a, unit_b, type_b,
            ))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (
            Id::Type {
                unit_index,
                type_index,
            },
            Id::None,
        ) => || -> Option<Result<()>> {
            let unit = file_a.units().get(unit_index)?;
            let ty = unit.types().get(type_index)?;
            let hash = FileHash::new(file_a);
            let code = Code::new(file_a);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            Some(super::types::kind(ty).and_then(|kind| kind.print_body(&mut state, unit)))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (
            Id::None,
            Id::Type {
                unit_index,
                type_index,
            },
        ) => || -> Option<Result<()>> {
            let unit = file_b.units().get(unit_index)?;
            let ty = unit.types().get(type_index)?;
            let hash = FileHash::new(file_b);
            let code = Code::new(file_b);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            Some(super::types::kind(ty).and_then(|kind| kind.print_body(&mut state, unit)))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (
            Id::Function {
                unit_index: unit_index_a,
                function_index: function_index_a,
            },
            Id::Function {
                unit_index: unit_index_b,
                function_index: function_index_b,
            },
        ) => || -> Option<Result<()>> {
            let unit_a = file_a.units().get(unit_index_a)?;
            let unit_b = file_b.units().get(unit_index_b)?;
            let function_a = unit_a.functions().get(function_index_a)?;
            let function_b = unit_b.functions().get(function_index_b)?;
            let hash_a = FileHash::new(file_a);
            let hash_b = FileHash::new(file_b);
            let code_a = Code::new(file_a);
            let code_b = Code::new(file_b);
            let mut state = DiffState::new(
                printer,
                &hash_a,
                &hash_b,
                code_a.as_ref(),
                code_b.as_ref(),
                options,
            );
            Some(PrintHeader::diff_body(
                &mut state, unit_a, function_a, unit_b, function_b,
            ))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (
            Id::Function {
                unit_index,
                function_index,
            },
            Id::None,
        ) => || -> Option<Result<()>> {
            let unit = file_a.units().get(unit_index)?;
            let function = unit.functions().get(function_index)?;
            let hash = FileHash::new(file_a);
            let code = Code::new(file_a);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            Some(function.print_body(&mut state, unit))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        (
            Id::None,
            Id::Function {
                unit_index,
                function_index,
            },
        ) => || -> Option<Result<()>> {
            let unit = file_b.units().get(unit_index)?;
            let function = unit.functions().get(function_index)?;
            let hash = FileHash::new(file_b);
            let code = Code::new(file_b);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            Some(function.print_body(&mut state, unit))
        }()
        .unwrap_or(Err(Error("invalid id".into()))),
        _ => Err(Error("invalid id".into())),
    }
}
