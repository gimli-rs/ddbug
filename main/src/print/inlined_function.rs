use std::cmp;

use parser::{FileHash, Function, InlinedFunction, LocalVariable, Unit};

use crate::print::{self, DiffList, DiffState, Print, PrintState, SortList, ValuePrinter};
use crate::Result;

fn print_size_and_decl(f: &InlinedFunction, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    match f.size() {
        Some(size) => write!(w, "[{}]", size)?,
        None => write!(w, "[??]")?,
    }
    write!(w, "\t")?;
    match f.abstract_origin(hash) {
        Some(function) => print::function::print_ref(function, w)?,
        None => write!(w, "<anon>")?,
    }
    Ok(())
}

fn print_call_source(f: &InlinedFunction, w: &mut dyn ValuePrinter, unit: &Unit) -> Result<()> {
    print::source::print(f.call_source(), w, unit)
}

impl<'input> Print for InlinedFunction<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.collapsed(
            |state| state.line(|w, state| print_size_and_decl(self, w, state)),
            |state| {
                if state.options().print_source {
                    state.field("call source", |w, _state| print_call_source(self, w, unit))?;
                }
                if state.options().print_inlined_function_parameters {
                    state.field_expanded("parameters", |state| {
                        state.list(unit, self.parameters())
                    })?;
                }
                if state.options().print_function_variables {
                    state
                        .field_collapsed("variables", |state| state.list(unit, self.variables()))?;
                }
                state.inline(|state| state.list(unit, self.inlined_functions()))?;
                Ok(())
            },
        )?;
        Ok(())
    }

    fn diff(state: &mut DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> Result<()> {
        state.collapsed(
            |state| state.line(a, b, |w, state, x| print_size_and_decl(x, w, state)),
            |state| {
                if state.options().print_source {
                    state.field(
                        "call source",
                        (unit_a, a),
                        (unit_b, b),
                        |w, _state, (unit, x)| print_call_source(x, w, unit),
                    )?;
                }
                if state.options().print_inlined_function_parameters {
                    state.field_expanded("parameters", |state| {
                        state.list(unit_a, a.parameters(), unit_b, b.parameters())
                    })?;
                }
                if state.options().print_function_variables {
                    let mut variables_a: Vec<_> = a.variables().iter().collect();
                    variables_a.sort_by(|x, y| {
                        LocalVariable::cmp_id(state.hash_a(), x, state.hash_a(), y)
                    });
                    let mut variables_b: Vec<_> = b.variables().iter().collect();
                    variables_b.sort_by(|x, y| {
                        LocalVariable::cmp_id(state.hash_b(), x, state.hash_b(), y)
                    });
                    state.field_collapsed("variables", |state| {
                        state.list(unit_a, &variables_a, unit_b, &variables_b)
                    })?;
                }
                state.inline(|state| {
                    state.list(unit_a, a.inlined_functions(), unit_b, b.inlined_functions())
                })?;
                Ok(())
            },
        )?;

        Ok(())
    }
}

impl<'input> DiffList for InlinedFunction<'input> {
    // Make the cost proportional to the size, so that we give priority to matching large
    // functions. Probably not ideal, but seemed to help for one test case.
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        // Ensure cost is at least 1.
        1 + 4 * self.size().unwrap_or(0) as usize
    }

    // TODO: other options to consider:
    // - include diff cost of lower levels of inlined functions
    fn diff_cost(state: &DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        let function_a = a.abstract_origin(state.hash_a());
        let function_b = b.abstract_origin(state.hash_b());
        match (function_a, function_b) {
            (Some(function_a), Some(function_b)) => {
                if <Function as SortList>::cmp_id(
                    state.hash_a(),
                    function_a,
                    state.hash_b(),
                    function_b,
                    state.options(),
                ) != cmp::Ordering::Equal
                {
                    cost += 3;
                }
            }
            (None, None) => {}
            _ => {
                cost += 3;
            }
        }

        let path_a = a.call_source().path(unit_a);
        let path_b = b.call_source().path(unit_b);
        if path_a.cmp(&path_b) != cmp::Ordering::Equal
            || a.call_source().line().cmp(&b.call_source().line()) != cmp::Ordering::Equal
            || a.call_source().column().cmp(&b.call_source().column()) != cmp::Ordering::Equal
        {
            cost += 1;
        }

        // max diff_cost needs be a.step_cost + b.step_cost = 2 + 4 * a.size + 4 * b.size
        // max cost so far is 4
        cost *= 1 + (a.size().unwrap_or(0) + b.size().unwrap_or(0)) as usize;
        cost
    }
}
