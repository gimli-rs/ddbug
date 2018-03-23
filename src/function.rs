use std::borrow;
use std::cmp;
use std::fmt::Debug;
use std::io::Write;
use std::rc::Rc;

use amd64;
use panopticon;

use {Options, Result, Sort};
use file::{CodeRegion, File, FileHash};
use namespace::Namespace;
use print::{DiffList, DiffState, Print, PrintState, SortList};
use range::Range;
use source::Source;
use types::{Type, TypeOffset};
use variable::LocalVariable;
use unit::Unit;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct FunctionOffset(pub usize);

#[derive(Debug, Default)]
pub(crate) struct Function<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub linkage_name: Option<&'input [u8]>,
    pub symbol_name: Option<&'input [u8]>,
    pub source: Source<'input>,
    pub address: Option<u64>,
    pub size: Option<u64>,
    pub inline: bool,
    pub declaration: bool,
    pub parameters: Vec<Parameter<'input>>,
    pub return_type: Option<TypeOffset>,
    pub variables: Vec<LocalVariable<'input>>,
    pub inlined_functions: Vec<InlinedFunction<'input>>,
}

impl<'input> Function<'input> {
    fn from_offset<'a>(
        unit: &'a Unit<'input>,
        offset: FunctionOffset,
    ) -> Option<&'a Function<'input>> {
        unit.functions.get(&offset)
    }

    fn name(&self) -> borrow::Cow<'input, str> {
        match self.name {
            Some(name) => String::from_utf8_lossy(name),
            None => borrow::Cow::Borrowed("<anon>"),
        }
    }

    pub fn address(&self) -> Option<Range> {
        if let (Some(address), Some(size)) = (self.address, self.size) {
            Some(Range {
                begin: address,
                end: address + size,
            })
        } else {
            None
        }
    }

    fn return_type<'a>(&self, hash: &'a FileHash<'input>) -> Option<&'a Type<'input>> {
        self.return_type.and_then(|v| Type::from_offset(hash, v))
    }

    fn calls(&self, file: &File) -> Vec<Call> {
        if let Some(address) = self.address() {
            if let Some(code) = file.code() {
                return disassemble(code, address);
            }
        }
        Vec::new()
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        write!(w, "{}", self.name())?;
        Ok(())
    }

    pub fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.indent(
            |state| state.line(|w, _state| self.print_name(w)),
            |state| {
                state.line(|w, _state| self.print_linkage_name(w))?;
                state.line(|w, _state| self.print_symbol_name(w))?;
                if state.options().print_source {
                    state.line(|w, _state| self.print_source(w, unit))?;
                }
                state.line(|w, _state| self.print_address(w))?;
                state.line(|w, _state| self.print_size(w))?;
                state.line(|w, _state| self.print_inline(w))?;
                state.line(|w, _state| self.print_declaration(w))?;
                state.labelled_indent("return type", |state| {
                    state.line(|w, state| self.print_return_type(w, state))
                })?;
                state.labelled_indent("parameters", |state| state.list(unit, &self.parameters))?;
                if state.options().print_function_variables {
                    state.labelled_indent("variables", |state| state.list(unit, &self.variables))?;
                }
                state.inline(|state| {
                    state.labelled_indent("inlined functions", |state| {
                        state.list(unit, &self.inlined_functions)
                    })
                })?;
                if state.options().print_function_calls {
                    let calls = self.calls(state.hash().file);
                    state.labelled_indent("calls", |state| state.list(&(), &calls))?;
                }
                Ok(())
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    pub fn diff(
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Function,
        unit_b: &Unit,
        b: &Function,
    ) -> Result<()> {
        state.indent(
            |state| state.line(a, b, |w, _state, x| x.print_name(w)),
            |state| {
                state.line(a, b, |w, _state, x| x.print_linkage_name(w))?;
                let flag = state.options().ignore_function_symbol_name;
                state.ignore_diff(flag, |state| {
                    state.line(a, b, |w, _state, x| x.print_symbol_name(w))
                })?;
                if state.options().print_source {
                    state.line((unit_a, a), (unit_b, b), |w, _state, (unit, x)| {
                        x.print_source(w, unit)
                    })?;
                }
                let flag = state.options().ignore_function_address;
                state.ignore_diff(flag, |state| {
                    state.line(a, b, |w, _state, x| x.print_address(w))
                })?;
                let flag = state.options().ignore_function_size;
                state.ignore_diff(flag, |state| state.line(a, b, |w, _state, x| x.print_size(w)))?;
                let flag = state.options().ignore_function_inline;
                state
                    .ignore_diff(flag, |state| state.line(a, b, |w, _state, x| x.print_inline(w)))?;
                state.line(a, b, |w, _state, x| x.print_declaration(w))?;
                state.labelled_indent("return type", |state| {
                    state.line(a, b, |w, state, x| x.print_return_type(w, state))
                })?;
                state.labelled_indent("parameters", |state| {
                    state.list(unit_a, &a.parameters, unit_b, &b.parameters)
                })?;
                if state.options().print_function_variables {
                    let mut variables_a: Vec<_> = a.variables.iter().collect();
                    variables_a.sort_by(|x, y| {
                        LocalVariable::cmp_id(state.hash_a(), x, state.hash_a(), y, state.options())
                    });
                    let mut variables_b: Vec<_> = b.variables.iter().collect();
                    variables_b.sort_by(|x, y| {
                        LocalVariable::cmp_id(state.hash_b(), x, state.hash_b(), y, state.options())
                    });
                    state.labelled_indent("variables", |state| {
                        state.list(unit_a, &variables_a, unit_b, &variables_b)
                    })?;
                }
                state.inline(|state| {
                    state.labelled_indent("inlined functions", |state| {
                        state.list(unit_a, &a.inlined_functions, unit_b, &b.inlined_functions)
                    })
                })?;
                if state.options().print_function_calls {
                    let calls_a = a.calls(state.hash_a().file);
                    let calls_b = b.calls(state.hash_b().file);
                    state.labelled_indent("calls", |state| {
                        state.list(&(), &calls_a, &(), &calls_b)
                    })?;
                }
                Ok(())
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        write!(w, "fn ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        write!(w, "{}", self.name())?;
        Ok(())
    }

    fn print_linkage_name(&self, w: &mut Write) -> Result<()> {
        if let Some(linkage_name) = self.linkage_name {
            write!(w, "linkage name: {}", String::from_utf8_lossy(linkage_name))?;
        }
        Ok(())
    }

    fn print_symbol_name(&self, w: &mut Write) -> Result<()> {
        if let Some(symbol_name) = self.symbol_name {
            write!(w, "symbol name: {}", String::from_utf8_lossy(symbol_name))?;
        }
        Ok(())
    }

    fn print_source(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        if self.source.is_some() {
            write!(w, "source: ")?;
            self.source.print(w, unit)?;
        }
        Ok(())
    }

    fn print_address(&self, w: &mut Write) -> Result<()> {
        if let Some(range) = self.address() {
            write!(w, "address: ")?;
            range.print_address(w)?;
        }
        Ok(())
    }

    fn print_size(&self, w: &mut Write) -> Result<()> {
        if let Some(size) = self.size {
            write!(w, "size: {}", size)?;
        }
        Ok(())
    }

    fn print_inline(&self, w: &mut Write) -> Result<()> {
        if self.inline {
            write!(w, "inline: yes")?;
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_return_type(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        if self.return_type.is_some() {
            match self.return_type(hash).and_then(|t| t.byte_size(hash)) {
                Some(byte_size) => write!(w, "[{}]", byte_size)?,
                None => write!(w, "[??]")?,
            }
            write!(w, "\t")?;
            Type::print_ref_from_offset(w, hash, self.return_type)?;
        }
        Ok(())
    }

    pub fn filter(&self, options: &Options) -> bool {
        if !self.inline && (self.address.is_none() || self.size.is_none()) {
            // This is either a declaration or a dead function that was removed
            // from the code, but wasn't removed from the debuginfo.
            // TODO: make this configurable?
            return false;
        }
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
            && options.filter_function_inline(self.inline)
    }
}

impl<'input> Print for Function<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Self::Arg) -> Result<()> {
        self.print(state, unit)
    }

    fn diff(
        state: &mut DiffState,
        unit_a: &Self::Arg,
        a: &Self,
        unit_b: &Self::Arg,
        b: &Self,
    ) -> Result<()> {
        Self::diff(state, unit_a, a, unit_b, b)
    }
}

impl<'input> SortList for Function<'input> {
    fn cmp_id(
        _hash_a: &FileHash,
        a: &Self,
        _hash_b: &FileHash,
        b: &Self,
        _options: &Options,
    ) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
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
        options: &Options,
    ) -> cmp::Ordering {
        let ord = Self::cmp_id(hash_a, a, hash_b, b, options);
        if ord != cmp::Ordering::Equal {
            return ord;
        }

        for (parameter_a, parameter_b) in a.parameters.iter().zip(b.parameters.iter()) {
            let ord = Parameter::cmp_type(hash_a, parameter_a, hash_b, parameter_b);
            if ord != cmp::Ordering::Equal {
                return ord;
            }
        }

        a.parameters.len().cmp(&b.parameters.len())
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
            Sort::None => a.address.cmp(&b.address),
            Sort::Name => Self::cmp_id_for_sort(hash_a, a, hash_b, b, options),
            Sort::Size => a.size.cmp(&b.size),
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ParameterOffset(pub usize);

#[derive(Debug, Default, Clone)]
pub(crate) struct Parameter<'input> {
    pub offset: Option<ParameterOffset>,
    pub name: Option<&'input [u8]>,
    pub ty: Option<TypeOffset>,
}

impl<'input> Parameter<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<&'a Type<'input>> {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash))
    }

    pub fn print_decl(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        if let Some(name) = self.name {
            write!(w, "{}: ", String::from_utf8_lossy(name))?;
        }
        match self.ty(hash) {
            Some(ty) => ty.print_ref(w, hash)?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_size_and_decl(&self, w: &mut Write, hash: &FileHash) -> Result<()> {
        match self.byte_size(hash) {
            Some(byte_size) => write!(w, "[{}]", byte_size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        self.print_decl(w, hash)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    #[allow(dead_code)]
    fn cmp_id(hash_a: &FileHash, a: &Parameter, hash_b: &FileHash, b: &Parameter) -> cmp::Ordering {
        let ord = Self::cmp_type(hash_a, a, hash_b, b);
        if ord != cmp::Ordering::Equal {
            return ord;
        }
        a.name.cmp(&b.name)
    }

    pub fn cmp_type(
        hash_a: &FileHash,
        a: &Parameter,
        hash_b: &FileHash,
        b: &Parameter,
    ) -> cmp::Ordering {
        match (a.ty(hash_a), b.ty(hash_b)) {
            (Some(ty_a), Some(ty_b)) => Type::cmp_id(hash_a, ty_a, hash_b, ty_b),
            (Some(_), None) => cmp::Ordering::Less,
            (None, Some(_)) => cmp::Ordering::Greater,
            (None, None) => cmp::Ordering::Equal,
        }
    }
}

impl<'input> Print for Parameter<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(|w, state| self.print_size_and_decl(w, state))
    }

    fn diff(
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(a, b, |w, state, x| x.print_size_and_decl(w, state))
    }
}

impl<'input> DiffList for Parameter<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 1;
        }
        match (a.ty(state.hash_a()), b.ty(state.hash_b())) {
            (Some(ty_a), Some(ty_b)) => {
                if Type::cmp_id(state.hash_a(), ty_a, state.hash_b(), ty_b) != cmp::Ordering::Equal
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

#[derive(Debug, Default)]
pub(crate) struct InlinedFunction<'input> {
    pub abstract_origin: Option<FunctionOffset>,
    pub size: Option<u64>,
    pub parameters: Vec<Parameter<'input>>,
    pub variables: Vec<LocalVariable<'input>>,
    pub inlined_functions: Vec<InlinedFunction<'input>>,
    pub call_source: Source<'input>,
}

impl<'input> InlinedFunction<'input> {
    fn print_size_and_decl(&self, w: &mut Write, _hash: &FileHash, unit: &Unit) -> Result<()> {
        match self.size {
            Some(size) => write!(w, "[{}]", size)?,
            None => write!(w, "[??]")?,
        }
        write!(w, "\t")?;
        match self.abstract_origin.and_then(|v| Function::from_offset(unit, v)) {
            Some(function) => function.print_ref(w)?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_call_source(&self, w: &mut Write, unit: &Unit) -> Result<()> {
        if self.call_source.is_some() {
            write!(w, "call source: ")?;
            self.call_source.print(w, unit)?;
        }
        Ok(())
    }
}

impl<'input> Print for InlinedFunction<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.indent(
            |state| state.line(|w, state| self.print_size_and_decl(w, state, unit)),
            |state| {
                // TODO: print parameters and variables?
                if state.options().print_source {
                    state.line(|w, _state| self.print_call_source(w, unit))?;
                }
                state.inline(|state| state.list(unit, &self.inlined_functions))?;
                Ok(())
            },
        )?;
        Ok(())
    }

    fn diff(state: &mut DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> Result<()> {
        state.indent(
            |state| {
                state.line((unit_a, a), (unit_b, b), |w, state, (unit, x)| {
                    x.print_size_and_decl(w, state, unit)
                })
            },
            |state| {
                // TODO: diff parameters and variables?
                if state.options().print_source {
                    state.line((unit_a, a), (unit_b, b), |w, _state, (unit, x)| {
                        x.print_call_source(w, unit)
                    })?;
                }
                state.inline(|state| {
                    state.list(unit_a, &a.inlined_functions, unit_b, &b.inlined_functions)
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
        1 + 4 * self.size.unwrap_or(0) as usize
    }

    // TODO: other options to consider:
    // - include diff cost of lower levels of inlined functions
    fn diff_cost(state: &DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        let function_a = a.abstract_origin.and_then(|v| Function::from_offset(unit_a, v));
        let function_b = b.abstract_origin.and_then(|v| Function::from_offset(unit_b, v));
        match (function_a, function_b) {
            (Some(function_a), Some(function_b)) => {
                if Function::cmp_id(
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

        let path_a = a.call_source.path(unit_a);
        let path_b = b.call_source.path(unit_b);
        if path_a.cmp(&path_b) != cmp::Ordering::Equal
            || a.call_source.line.cmp(&b.call_source.line) != cmp::Ordering::Equal
            || a.call_source.column.cmp(&b.call_source.column) != cmp::Ordering::Equal
        {
            cost += 1;
        }

        // max diff_cost needs be a.step_cost + b.step_cost = 2 + 4 * a.size + 4 * b.size
        // max cost so far is 4
        cost *= 1 + (a.size.unwrap_or(0) + b.size.unwrap_or(0)) as usize;
        cost
    }
}

fn disassemble(code: &CodeRegion, range: Range) -> Vec<Call> {
    match code.machine {
        panopticon::Machine::Amd64 => {
            disassemble_arch::<amd64::Amd64>(&code.region, range, amd64::Mode::Long)
        }
        _ => Vec::new(),
    }
}

fn disassemble_arch<A>(
    region: &panopticon::Region,
    range: Range,
    cfg: A::Configuration,
) -> Vec<Call>
where
    A: panopticon::Architecture + Debug,
    A::Configuration: Debug,
{
    let mut calls = Vec::new();
    let mut addr = range.begin;
    while addr < range.end {
        let m = match A::decode(region, addr, &cfg) {
            Ok(m) => m,
            Err(e) => {
                error!("failed to disassemble: {}", e);
                return calls;
            }
        };

        for mnemonic in m.mnemonics {
            for instruction in &mnemonic.instructions {
                match *instruction {
                    panopticon::Statement {
                        op: panopticon::Operation::Call(ref call),
                        ..
                    } => match *call {
                        panopticon::Rvalue::Constant {
                            ref value,
                            ..
                        } => {
                            calls.push(Call {
                                from: mnemonic.area.start,
                                to: *value,
                            });
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
            addr = mnemonic.area.end;
        }
    }
    calls
}

struct Call {
    from: u64,
    to: u64,
}

impl Call {
    fn print(&self, w: &mut Write, hash: &FileHash, options: &Options) -> Result<()> {
        if !options.ignore_function_address {
            // FIXME: it would be nice to display this in a way that doesn't clutter the output
            // when diffing
            write!(w, "0x{:x} -> 0x{:x} ", self.from, self.to)?;
        }
        if let Some(function) = hash.functions.get(&self.to) {
            function.print_ref(w)?;
        } else if options.ignore_function_address {
            // We haven't displayed an address yet, so we need to display something.
            write!(w, "0x{:x}", self.to)?;
        }
        Ok(())
    }
}

impl Print for Call {
    type Arg = ();

    fn print(&self, state: &mut PrintState, _arg: &()) -> Result<()> {
        let options = state.options();
        state.line(|w, hash| self.print(w, hash, options))
    }

    fn diff(state: &mut DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> Result<()> {
        let options = state.options();
        state.line(a, b, |w, hash, x| x.print(w, hash, options))
    }
}

impl DiffList for Call {
    fn step_cost(&self, _state: &DiffState, _arg: &()) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        match (state.hash_a().functions.get(&a.to), state.hash_b().functions.get(&b.to)) {
            (Some(function_a), Some(function_b)) => {
                if Function::cmp_id(
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
