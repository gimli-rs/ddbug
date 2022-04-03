use std::collections::HashMap;

use parser::{File, FileHash, Function, Type, Unit, Variable};

use crate::code::Code;
use crate::filter;
use crate::print::{
    self, DiffState, Id, MergeIterator, MergeResult, PrintHeader, PrintState, Printer, SortList,
};
use crate::{Options, Result};

fn assign_ids(file: &File, options: &Options) -> Vec<Id> {
    let mut ids = Vec::new();
    for (unit_index, unit) in file.units().iter().enumerate() {
        unit.set_id(ids.len());
        ids.push(Id::Unit { unit_index });
        assign_ids_in_unit(unit_index, unit, options, &mut ids);
    }
    ids
}

fn assign_ids_in_unit(unit_index: usize, unit: &Unit, _options: &Options, ids: &mut Vec<Id>) {
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

fn assign_merged_ids(file_a: &File, file_b: &File, options: &Options) -> Vec<(Id, Id)> {
    let hash_a = &FileHash::new(file_a);
    let hash_b = &FileHash::new(file_b);

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

fn assign_unmerged_ids_in_unit(
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

#[allow(clippy::too_many_arguments)]
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

pub struct PrintIndex {
    ids: Vec<Id>,
}

pub fn print_index(file: &File, options: &Options) -> PrintIndex {
    let ids = assign_ids(file, options);
    PrintIndex { ids }
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

pub fn print_parent(id: usize, file: &File, index: &PrintIndex) -> Option<usize> {
    let id = index.ids.get(id)?;
    match *id {
        Id::Type { unit_index, .. }
        | Id::Function { unit_index, .. }
        | Id::Variable { unit_index, .. } => {
            let unit = file.units().get(unit_index)?;
            Some(unit.id())
        }
        _ => None,
    }
}

pub fn print_id(
    id: usize,
    detail: Option<&str>,
    file: &File,
    printer: &mut dyn Printer,
    options: &Options,
    index: &PrintIndex,
) -> Option<()> {
    let id = index.ids.get(id)?;
    match *id {
        Id::Unit { unit_index } => {
            let unit = file.units().get(unit_index)?;
            let hash = FileHash::new(file);
            let code = Code::new(file);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            print::unit::print_body(unit, &mut state).ok()
        }
        Id::Type {
            unit_index,
            type_index,
        } => {
            let unit = file.units().get(unit_index)?;
            let ty = unit.types().get(type_index)?;
            let hash = FileHash::new(file);
            let code = Code::new(file);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            let kind = print::types::kind(ty).ok()?;
            kind.print_body(&mut state, unit).ok()
        }
        Id::Function {
            unit_index,
            function_index,
        } => {
            let unit = file.units().get(unit_index)?;
            let function = unit.functions().get(function_index)?;
            let hash = FileHash::new(file);
            let code = Code::new(file);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            match detail {
                None => function.print_body(&mut state, unit).ok(),
                Some("code") => {
                    let details = function.details(state.hash());
                    print::function::print_instructions(&mut state, function, &details).ok()
                }
                _ => None,
            }
        }
        Id::Variable {
            unit_index,
            variable_index,
        } => {
            let unit = file.units().get(unit_index)?;
            let variable = unit.variables().get(variable_index)?;
            let hash = FileHash::new(file);
            let code = Code::new(file);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            variable.print_body(&mut state, unit).ok()
        }
        _ => None,
    }
}

pub struct DiffIndex {
    ids: Vec<(Id, Id)>,
}

pub fn diff_index(file_a: &File, file_b: &File, options: &Options) -> DiffIndex {
    let ids = assign_merged_ids(file_a, file_b, options);
    DiffIndex { ids }
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
    id: usize,
    file_a: &File,
    file_b: &File,
    printer: &mut dyn Printer,
    options: &Options,
    index: &DiffIndex,
) -> Option<()> {
    let id = index.ids.get(id).unwrap();
    match *id {
        (
            Id::Unit {
                unit_index: unit_index_a,
            },
            Id::Unit {
                unit_index: unit_index_b,
            },
        ) => {
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
            print::unit::diff_body(&mut state, unit_a, unit_b).ok()
        }
        (Id::Unit { unit_index }, Id::None) => {
            let unit = file_a.units().get(unit_index)?;
            let hash = FileHash::new(file_a);
            let code = Code::new(file_a);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            print::unit::print_body(unit, &mut state).ok()
        }
        (Id::None, Id::Unit { unit_index }) => {
            let unit = file_b.units().get(unit_index)?;
            let hash = FileHash::new(file_b);
            let code = Code::new(file_b);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            print::unit::print_body(unit, &mut state).ok()
        }
        (
            Id::Type {
                unit_index: unit_index_a,
                type_index: type_index_a,
            },
            Id::Type {
                unit_index: unit_index_b,
                type_index: type_index_b,
            },
        ) => {
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
            print::types::diff_body(&mut state, unit_a, type_a, unit_b, type_b).ok()
        }
        (
            Id::Type {
                unit_index,
                type_index,
            },
            Id::None,
        ) => {
            let unit = file_a.units().get(unit_index)?;
            let ty = unit.types().get(type_index)?;
            let hash = FileHash::new(file_a);
            let code = Code::new(file_a);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            print::types::kind(ty)
                .and_then(|kind| kind.print_body(&mut state, unit))
                .ok()
        }
        (
            Id::None,
            Id::Type {
                unit_index,
                type_index,
            },
        ) => {
            let unit = file_b.units().get(unit_index)?;
            let ty = unit.types().get(type_index)?;
            let hash = FileHash::new(file_b);
            let code = Code::new(file_b);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            print::types::kind(ty)
                .and_then(|kind| kind.print_body(&mut state, unit))
                .ok()
        }
        (
            Id::Function {
                unit_index: unit_index_a,
                function_index: function_index_a,
            },
            Id::Function {
                unit_index: unit_index_b,
                function_index: function_index_b,
            },
        ) => {
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
            PrintHeader::diff_body(&mut state, unit_a, function_a, unit_b, function_b).ok()
        }
        (
            Id::Function {
                unit_index,
                function_index,
            },
            Id::None,
        ) => {
            let unit = file_a.units().get(unit_index)?;
            let function = unit.functions().get(function_index)?;
            let hash = FileHash::new(file_a);
            let code = Code::new(file_a);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            function.print_body(&mut state, unit).ok()
        }
        (
            Id::None,
            Id::Function {
                unit_index,
                function_index,
            },
        ) => {
            let unit = file_b.units().get(unit_index)?;
            let function = unit.functions().get(function_index)?;
            let hash = FileHash::new(file_b);
            let code = Code::new(file_b);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            function.print_body(&mut state, unit).ok()
        }
        (
            Id::Variable {
                unit_index: unit_index_a,
                variable_index: variable_index_a,
            },
            Id::Variable {
                unit_index: unit_index_b,
                variable_index: variable_index_b,
            },
        ) => {
            let unit_a = file_a.units().get(unit_index_a)?;
            let unit_b = file_b.units().get(unit_index_b)?;
            let variable_a = unit_a.variables().get(variable_index_a)?;
            let variable_b = unit_b.variables().get(variable_index_b)?;
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
            PrintHeader::diff_body(&mut state, unit_a, variable_a, unit_b, variable_b).ok()
        }
        (
            Id::Variable {
                unit_index,
                variable_index,
            },
            Id::None,
        ) => {
            let unit = file_a.units().get(unit_index)?;
            let variable = unit.variables().get(variable_index)?;
            let hash = FileHash::new(file_a);
            let code = Code::new(file_a);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            variable.print_body(&mut state, unit).ok()
        }
        (
            Id::None,
            Id::Variable {
                unit_index,
                variable_index,
            },
        ) => {
            let unit = file_b.units().get(unit_index)?;
            let variable = unit.variables().get(variable_index)?;
            let hash = FileHash::new(file_b);
            let code = Code::new(file_b);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            variable.print_body(&mut state, unit).ok()
        }
        _ => None,
    }
}

pub struct BloatIndex {
    ids: Vec<Id>,
    function_totals: Vec<(FunctionId, FunctionTotal)>,
    callers: HashMap<u64, Vec<Caller>>,
}

// Treat functions as copies if they have the same name and source location.
// This isn't exact, but good enough.
#[derive(Clone, PartialEq, Eq, Hash)]
struct FunctionId {
    name: Vec<u8>,
    source: Vec<u8>,
}

#[derive(Default)]
struct FunctionTotal {
    size: u64,
    functions: Vec<(usize, usize)>,
}

struct Caller {
    unit_index: usize,
    function_index: usize,
    _address: u64,
}

pub fn bloat_index(file: &File, options: &Options) -> BloatIndex {
    let ids = assign_ids(file, options);
    let code = Code::new(file);

    // Build a list of copies of functions.
    let mut function_totals = HashMap::new();
    // Also build a map of callers.
    let mut callers = HashMap::new();
    for (unit_index, unit) in file.units().iter().enumerate() {
        for (function_index, function) in unit.functions().iter().enumerate() {
            if let Some(size) = function.size() {
                let mut name = Vec::new();
                print::function::print_ref(function, &mut name).unwrap();
                let mut source = Vec::new();
                print::source::print(function.source(), &mut source, unit).unwrap();
                let id = FunctionId { name, source };
                let mut function_total = function_totals
                    .entry(id)
                    .or_insert_with(FunctionTotal::default);
                function_total.size += size;
                function_total.functions.push((unit_index, function_index));

                if let Some(code) = code.as_ref() {
                    for range in function.ranges() {
                        for call in code.calls(*range) {
                            let entry = callers.entry(call.to).or_insert(Vec::new());
                            entry.push(Caller {
                                unit_index,
                                function_index,
                                _address: call.from,
                            });
                        }
                    }
                }
            }
        }
    }

    let mut function_totals: Vec<_> = function_totals.into_iter().collect();
    function_totals.sort_by(|a, b| b.1.size.cmp(&a.1.size));

    BloatIndex {
        ids,
        function_totals,
        callers,
    }
}

pub fn bloat(
    file: &File,
    printer: &mut dyn Printer,
    options: &Options,
    index: &BloatIndex,
) -> Result<()> {
    let hash = FileHash::new(file);

    let state = &mut PrintState::new(printer, &hash, None, options);
    for (id, function_total) in &index.function_totals {
        state.collapsed(
            |state| {
                state.line(|w, _hash| {
                    write!(w, "{} ", function_total.size)?;
                    w.write_all(&id.name)?;
                    if !id.source.is_empty() {
                        write!(w, " ")?;
                        w.write_all(&id.source)?;
                    }
                    Ok(())
                })
            },
            |state| {
                for (unit_index, function_index) in &function_total.functions {
                    let unit = &file.units()[*unit_index];
                    let function = &unit.functions()[*function_index];
                    let address = function.address().unwrap();
                    let size = function.size().unwrap();
                    state.id(
                        function.id(),
                        |state| {
                            state.line(|w, _hash| {
                                write!(w, "{} ", size)?;
                                print::unit::print_ref(unit, w)?;
                                Ok(())
                            })
                        },
                        |state| bloat_callers(state, file, index, address),
                    )?;
                }
                Ok(())
            },
        )?;
    }

    Ok(())
}

fn bloat_callers(
    state: &mut PrintState,
    file: &File,
    index: &BloatIndex,
    address: u64,
) -> Result<()> {
    if let Some(calls) = index.callers.get(&address) {
        for caller in calls {
            state.line(|w, _hash| {
                // TODO: print inlined functions too
                let unit = &file.units()[caller.unit_index];
                let function = &unit.functions()[caller.function_index];
                print::function::print_ref(function, w)?;
                // TODO: print source of from_address instead
                let mut source = Vec::new();
                print::source::print(function.source(), &mut source, unit)?;
                if !source.is_empty() {
                    write!(w, " ")?;
                    w.write_all(&source)?;
                }
                Ok(())
            })?;
        }
    }
    Ok(())
}

pub fn bloat_id(
    id: usize,
    file: &File,
    printer: &mut dyn Printer,
    options: &Options,
    index: &BloatIndex,
) -> Option<()> {
    let id = index.ids.get(id)?;
    match *id {
        Id::Function {
            unit_index,
            function_index,
        } => {
            let unit = file.units().get(unit_index)?;
            let function = unit.functions().get(function_index)?;
            let hash = FileHash::new(file);
            let code = Code::new(file);
            let mut state = PrintState::new(printer, &hash, code.as_ref(), options);
            bloat_callers(&mut state, file, index, function.address().unwrap()).ok()
        }
        _ => None,
    }
}
