use std::cmp;

use parser::{
    FileHash, Function, FunctionDetails, InlinedFunction, LocalVariable, Parameter, ParameterType,
    Type, TypeOffset, Unit,
};

use crate::code::{Call, Code};
use crate::print::{self, DiffList, DiffState, Print, PrintState, SortList, ValuePrinter};
use crate::{Options, Result, Sort};

pub(crate) fn print_ref(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    w.link(f.id(), &mut |w| {
        if let Some(namespace) = f.namespace() {
            print::namespace::print(namespace, w)?;
        }
        write!(w, "{}", f.name().unwrap_or("<anon>"))?;
        Ok(())
    })
}

fn print_name(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "fn ")?;
    if let Some(namespace) = f.namespace() {
        print::namespace::print(namespace, w)?;
    }
    write!(w, "{}", f.name().unwrap_or("<anon>"))?;
    Ok(())
}

fn print_linkage_name(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(linkage_name) = f.linkage_name() {
        write!(w, "{}", linkage_name)?;
    }
    Ok(())
}

fn print_symbol_name(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(symbol_name) = f.symbol_name() {
        write!(w, "{}", symbol_name)?;
    }
    Ok(())
}

fn print_source(f: &Function, w: &mut dyn ValuePrinter, unit: &Unit) -> Result<()> {
    print::source::print(f.source(), w, unit)
}

fn print_address(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(ref range) = f.range() {
        print::range::print_address(range, w)?;
    }
    Ok(())
}

fn print_size(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(size) = f.size() {
        write!(w, "{}", size)?;
    }
    Ok(())
}

fn print_inline(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    if f.is_inline() {
        write!(w, "yes")?;
    }
    Ok(())
}

fn print_declaration(f: &Function, w: &mut dyn ValuePrinter) -> Result<()> {
    if f.is_declaration() {
        write!(w, "yes")?;
    }
    Ok(())
}

fn print_return_type(f: &Function, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    let ty = f.return_type(hash);
    if ty.as_ref().map(|t| t.is_void()) != Some(true) {
        match ty.as_ref().and_then(|t| t.byte_size(hash)) {
            Some(byte_size) => write!(w, "[{}]", byte_size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        print::types::print_ref(ty, w, hash)?;
    }
    Ok(())
}

impl<'input> Print for Function<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Self::Arg) -> Result<()> {
        state.collapsed(
            |state| state.id(self.id(), |w, _state| print_name(self, w)),
            |state| {
                state.field("linkage name", |w, _state| print_linkage_name(self, w))?;
                state.field("symbol name", |w, _state| print_symbol_name(self, w))?;
                if state.options().print_source {
                    state.field("source", |w, _state| print_source(self, w, unit))?;
                }
                state.field("address", |w, _state| print_address(self, w))?;
                state.field("size", |w, _state| print_size(self, w))?;
                state.field("inline", |w, _state| print_inline(self, w))?;
                state.field("declaration", |w, _state| print_declaration(self, w))?;
                state.field_expanded("return type", |state| {
                    state.line(|w, state| print_return_type(self, w, state))
                })?;
                let details = self.details(state.hash());
                state
                    .field_expanded("parameters", |state| state.list(unit, details.parameters()))?;
                if state.options().print_function_variables {
                    state.field_collapsed("variables", |state| {
                        state.list(unit, details.variables())
                    })?;
                }
                if state.options().print_function_stack_frame {
                    let variables = frame_variables(&details, state.hash());
                    state.field_collapsed("stack frame", |state| state.list(&(), &variables))?;
                }
                state.inline(|state| {
                    state.field_collapsed("inlined functions", |state| {
                        state.list(unit, details.inlined_functions())
                    })
                })?;
                if state.options().print_function_calls {
                    let calls = calls(self, state.code);
                    state.field_collapsed("calls", |state| state.list(&(), &calls))?;
                }
                if state.options().print_function_instructions {
                    state
                        .field_collapsed("instructions", |state| print_instructions(state, self))?;
                }
                Ok(())
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn diff(
        state: &mut DiffState,
        unit_a: &Self::Arg,
        a: &Self,
        unit_b: &Self::Arg,
        b: &Self,
    ) -> Result<()> {
        state.collapsed(
            |state| state.id(a.id(), a, b, |w, _state, x| print_name(x, w)),
            |state| {
                state.field("linkage name", a, b, |w, _state, x| {
                    print_linkage_name(x, w)
                })?;
                let flag = state.options().ignore_function_symbol_name;
                state.ignore_diff(flag, |state| {
                    state.field("symbol name", a, b, |w, _state, x| print_symbol_name(x, w))
                })?;
                if state.options().print_source {
                    state.field(
                        "source",
                        (unit_a, a),
                        (unit_b, b),
                        |w, _state, (unit, x)| print_source(x, w, unit),
                    )?;
                }
                let flag = state.options().ignore_function_address;
                state.ignore_diff(flag, |state| {
                    state.field("address", a, b, |w, _state, x| print_address(x, w))
                })?;
                let flag = state.options().ignore_function_size;
                state.ignore_diff(flag, |state| {
                    state.field("size", a, b, |w, _state, x| print_size(x, w))
                })?;
                let flag = state.options().ignore_function_inline;
                state.ignore_diff(flag, |state| {
                    state.field("inline", a, b, |w, _state, x| print_inline(x, w))
                })?;
                state.field("declaration", a, b, |w, _state, x| print_declaration(x, w))?;
                state.field_expanded("return type", |state| {
                    state.line(a, b, |w, state, x| print_return_type(x, w, state))
                })?;
                let details_a = a.details(state.hash_a());
                let details_b = b.details(state.hash_b());
                state.field_expanded("parameters", |state| {
                    state.list(
                        unit_a,
                        details_a.parameters(),
                        unit_b,
                        details_b.parameters(),
                    )
                })?;
                if state.options().print_function_variables {
                    let mut variables_a: Vec<_> = details_a.variables().iter().collect();
                    variables_a.sort_by(|x, y| {
                        LocalVariable::cmp_id(state.hash_a(), x, state.hash_a(), y)
                    });
                    let mut variables_b: Vec<_> = details_b.variables().iter().collect();
                    variables_b.sort_by(|x, y| {
                        LocalVariable::cmp_id(state.hash_b(), x, state.hash_b(), y)
                    });
                    state.field_collapsed("variables", |state| {
                        state.list(unit_a, &variables_a, unit_b, &variables_b)
                    })?;
                }
                if state.options().print_function_stack_frame {
                    let variables_a = frame_variables(&details_a, state.hash_a());
                    let variables_b = frame_variables(&details_b, state.hash_b());
                    state.field_collapsed("stack frame", |state| {
                        state.ord_list(&(), &variables_a, &(), &variables_b)
                    })?;
                }
                state.inline(|state| {
                    state.field_collapsed("inlined functions", |state| {
                        state.list(
                            unit_a,
                            details_a.inlined_functions(),
                            unit_b,
                            details_b.inlined_functions(),
                        )
                    })
                })?;
                if state.options().print_function_calls {
                    let calls_a = calls(a, state.code_a);
                    let calls_b = calls(b, state.code_b);
                    state.field_collapsed("calls", |state| {
                        state.list(&(), &calls_a, &(), &calls_b)
                    })?;
                }
                if state.options().print_function_instructions {
                    state.field_collapsed("instructions", |state| {
                        // TODO: diff instructions
                        state.ignore_diff(true, |state| {
                            state.block(a, b, |state, x| print_instructions(state, x))
                        })
                    })?;
                }
                Ok(())
            },
        )?;
        state.line_break()?;
        Ok(())
    }
}

impl<'input> SortList for Function<'input> {
    fn cmp_id(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        Function::cmp_id(hash_a, a, hash_b, b)
    }

    // This function is a bit of a hack. We use it for sorting, but not for
    // equality, in the hopes that we'll get better results in the presence
    // of overloading, while still coping with changed function signatures.
    // TODO: do something smarter
    fn cmp_id_for_sort(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        let ord = Function::cmp_id(hash_a, a, hash_b, b);
        if ord != cmp::Ordering::Equal {
            return ord;
        }

        for (parameter_a, parameter_b) in a.parameters().iter().zip(b.parameters().iter()) {
            let ord = ParameterType::cmp_id(hash_a, parameter_a, hash_b, parameter_b);
            if ord != cmp::Ordering::Equal {
                return ord;
            }
        }

        a.parameters().len().cmp(&b.parameters().len())
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
            Sort::None => a.address().cmp(&b.address()),
            Sort::Name => Self::cmp_id_for_sort(hash_a, a, hash_b, b, options),
            Sort::Size => a.size().cmp(&b.size()),
        }
    }
}

fn print_call(
    call: &Call,
    w: &mut dyn ValuePrinter,
    hash: &FileHash,
    options: &Options,
) -> Result<()> {
    if !options.ignore_function_address {
        // FIXME: it would be nice to display this in a way that doesn't clutter the output
        // when diffing
        write!(w, "0x{:x} -> 0x{:x} ", call.from, call.to)?;
    }
    if let Some(function) = hash.functions_by_address.get(&call.to) {
        print_ref(function, w)?;
    } else if options.ignore_function_address {
        // We haven't displayed an address yet, so we need to display something.
        write!(w, "0x{:x}", call.to)?;
    }
    Ok(())
}

impl Print for Call {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        let options = state.options();
        state.line(|w, hash| print_call(self, w, hash, options))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        let options = state.options();
        state.line(a, b, |w, hash, x| print_call(x, w, hash, options))
    }
}

impl DiffList for Call {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        match (
            state.hash_a().functions_by_address.get(&a.to),
            state.hash_b().functions_by_address.get(&b.to),
        ) {
            (Some(function_a), Some(function_b)) => {
                if <Function as SortList>::cmp_id(
                    state.hash_a(),
                    function_a,
                    state.hash_b(),
                    function_b,
                    state.options(),
                ) != cmp::Ordering::Equal
                {
                    cost += 1;
                }
            }
            (None, None) => {}
            _ => {
                cost += 1;
            }
        }
        cost
    }
}

fn calls(f: &Function, code: Option<&Code>) -> Vec<Call> {
    if let (Some(code), Some(range)) = (code, f.range()) {
        return code.calls(range);
    }
    Vec::new()
}

fn print_instructions(state: &mut PrintState, f: &Function) -> Result<()> {
    let range = match f.range() {
        Some(x) => x,
        None => return Ok(()),
    };
    let code = match state.code {
        Some(x) => x,
        None => return Ok(()),
    };
    let disassembler = match code.disassembler() {
        Some(x) => x,
        None => return Ok(()),
    };
    let insns = match disassembler.instructions(range) {
        Some(x) => x,
        None => return Ok(()),
    };
    for insn in insns.iter() {
        insn.print(state, &disassembler, range)?;
    }
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
struct FrameVariable<'input> {
    prev_offset: Option<i64>,
    offset: i64,
    size: Option<u64>,
    name: Option<&'input str>,
    ty: TypeOffset,
}

// Ignore prev_offset for ordering.
impl<'input> Ord for FrameVariable<'input> {
    fn cmp(&self, other: &FrameVariable<'input>) -> cmp::Ordering {
        self.offset
            .cmp(&other.offset)
            .then_with(|| self.size.cmp(&other.size))
            .then_with(|| self.name.cmp(&other.name))
            .then_with(|| self.ty.cmp(&other.ty))
    }
}

impl<'input> PartialOrd for FrameVariable<'input> {
    fn partial_cmp(&self, other: &FrameVariable<'input>) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn print_frame_unknown(variable: &FrameVariable, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(offset) = variable.prev_offset {
        if offset < variable.offset {
            write!(w, "{}[{}]\t<unknown>", offset, variable.offset - offset)?;
        }
    }
    Ok(())
}

fn print_frame_variable(
    variable: &FrameVariable,
    w: &mut dyn ValuePrinter,
    hash: &FileHash,
) -> Result<()> {
    write!(w, "{}", variable.offset)?;
    match variable.size {
        Some(size) => {
            write!(w, "[{}]", size)?;
        }
        None => {
            debug!("no size for {:?}", variable);
            write!(w, "[??]")?;
        }
    }
    write!(w, "\t{}: ", variable.name.unwrap_or("<anon>"))?;
    print::types::print_ref(Type::from_offset(hash, variable.ty), w, hash)?;
    Ok(())
}

fn frame_variables<'input>(
    details: &FunctionDetails<'input>,
    hash: &FileHash<'input>,
) -> Vec<FrameVariable<'input>> {
    let mut frame_variables = Vec::new();
    for parameter in details.parameters() {
        add_parameter_frame_locations(parameter, hash, &mut frame_variables);
    }
    for variable in details.variables() {
        add_variable_frame_locations(variable, hash, &mut frame_variables);
    }
    for inlined_function in details.inlined_functions() {
        add_inlined_function_frame_locations(inlined_function, hash, &mut frame_variables);
    }

    frame_variables.sort_unstable();
    frame_variables.dedup();

    let mut prev_offset = None;
    for variable in &mut frame_variables {
        variable.prev_offset = prev_offset;
        prev_offset = variable.size.map(|size| variable.offset + size as i64);
    }

    frame_variables
}

fn add_inlined_function_frame_locations<'input>(
    inlined_function: &InlinedFunction<'input>,
    hash: &FileHash<'input>,
    variables: &mut Vec<FrameVariable<'input>>,
) {
    for parameter in inlined_function.parameters() {
        add_parameter_frame_locations(parameter, hash, variables);
    }
    for variable in inlined_function.variables() {
        add_variable_frame_locations(variable, hash, variables);
    }
    for inlined_function in inlined_function.inlined_functions() {
        add_inlined_function_frame_locations(inlined_function, hash, variables);
    }
}

fn add_parameter_frame_locations<'input>(
    parameter: &Parameter<'input>,
    hash: &FileHash<'input>,
    variables: &mut Vec<FrameVariable<'input>>,
) {
    let size = parameter.byte_size(hash);
    let name = parameter.name();
    let ty = parameter.type_offset();
    for location in parameter.frame_locations() {
        let offset = location.offset;
        let size = if let Some(bit_size) = location.bit_size.get() {
            Some((bit_size + 7) / 8)
        } else {
            size
        };
        variables.push(FrameVariable {
            prev_offset: None,
            offset,
            size,
            name,
            ty,
        });
    }
}

fn add_variable_frame_locations<'input>(
    v: &LocalVariable<'input>,
    hash: &FileHash<'input>,
    variables: &mut Vec<FrameVariable<'input>>,
) {
    let size = v.byte_size(hash);
    let name = v.name();
    let ty = v.type_offset();
    for location in v.frame_locations() {
        let offset = location.offset;
        let size = if let Some(bit_size) = location.bit_size.get() {
            Some((bit_size + 7) / 8)
        } else {
            size
        };
        variables.push(FrameVariable {
            prev_offset: None,
            offset,
            size,
            name,
            ty,
        });
    }
}

impl<'input> Print for FrameVariable<'input> {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(|w, _hash| print_frame_unknown(self, w))?;
        state.line(|w, hash| print_frame_variable(self, w, hash))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        state.line(a, b, |w, _hash, x| print_frame_unknown(x, w))?;
        state.line(a, b, |w, hash, x| print_frame_variable(x, w, hash))
    }
}
