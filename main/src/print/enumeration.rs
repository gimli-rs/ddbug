use std::cmp;

use file::FileHash;
use print::{DiffList, DiffState, Print, PrintState, ValuePrinter};
use types::{EnumerationType, Enumerator, TypeOffset};
use unit::Unit;
use Result;

fn print_name(ty: &EnumerationType, w: &mut ValuePrinter) -> Result<()> {
    write!(w, "enum ")?;
    if let Some(ref namespace) = ty.namespace {
        namespace.print(w)?;
    }
    write!(w, "{}", ty.name().unwrap_or("<anon>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &EnumerationType, w: &mut ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| print_name(ty, w))
}

pub(crate) fn print(
    ty: &EnumerationType,
    state: &mut PrintState,
    unit: &Unit,
    id: usize,
    offset: TypeOffset,
) -> Result<()> {
    state.collapsed(
        |state| state.id(id, |w, _state| print_name(ty, w)),
        |state| {
            if state.options().print_source {
                state.field("source", |w, _state| print_source(ty, w, unit))?;
            }
            state.field("declaration", |w, _state| print_declaration(ty, w))?;
            state.field("size", |w, state| print_byte_size(ty, w, state))?;
            let enumerators = state.hash().file.get_enumerators(offset);
            state.field_expanded("enumerators", |state| state.list(unit, &enumerators))
        },
    )?;
    state.line_break()?;
    Ok(())
}

pub(crate) fn diff(
    state: &mut DiffState,
    id: usize,
    unit_a: &Unit,
    a: &EnumerationType,
    offset_a: TypeOffset,
    unit_b: &Unit,
    b: &EnumerationType,
    offset_b: TypeOffset,
) -> Result<()> {
    // The names should be the same, but we can't be sure.
    state.collapsed(
        |state| state.id(id, a, b, |w, _state, x| print_name(x, w)),
        |state| {
            if state.options().print_source {
                state.field(
                    "source",
                    (unit_a, a),
                    (unit_b, b),
                    |w, _state, (unit, x)| print_source(x, w, unit),
                )?;
            }
            state.field("declaration", a, b, |w, _state, x| print_declaration(x, w))?;
            state.field("size", a, b, |w, state, x| print_byte_size(x, w, state))?;
            // TODO: handle reordering better
            let enumerators_a = state.hash_a().file.get_enumerators(offset_a);
            let enumerators_b = state.hash_b().file.get_enumerators(offset_b);
            state.field_expanded("enumerators", |state| {
                state.list(unit_a, &enumerators_a, unit_b, &enumerators_b)
            })
        },
    )?;
    state.line_break()?;
    Ok(())
}

fn print_source(ty: &EnumerationType, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
    if ty.source.is_some() {
        ty.source.print(w, unit)?;
    }
    Ok(())
}

fn print_declaration(ty: &EnumerationType, w: &mut ValuePrinter) -> Result<()> {
    if ty.declaration {
        write!(w, "yes")?;
    }
    Ok(())
}

fn print_byte_size(ty: &EnumerationType, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    if let Some(size) = ty.byte_size(hash) {
        write!(w, "{}", size)?;
    } else {
        debug!("enum with no size");
    }
    Ok(())
}

fn print_enumerator(ty: &Enumerator, w: &mut ValuePrinter) -> Result<()> {
    write!(w, "{}", ty.name().unwrap_or("<anon>"))?;
    if let Some(value) = ty.value {
        write!(w, "({})", value)?;
    }
    Ok(())
}

impl<'input> Print for Enumerator<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(|w, _state| print_enumerator(self, w))
    }

    fn diff(
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(a, b, |w, _state, x| print_enumerator(x, w))
    }
}

impl<'input> DiffList for Enumerator<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        3
    }

    fn diff_cost(_state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        // A difference in name is usually more significant than a difference in value,
        // such as for enums where the value is assigned by the compiler.
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 4;
        }
        if a.value.cmp(&b.value) != cmp::Ordering::Equal {
            cost += 2;
        }
        cost
    }
}
