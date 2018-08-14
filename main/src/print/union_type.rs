use file::FileHash;
use print::{DiffState, PrintState, ValuePrinter};
use types::UnionType;
use unit::Unit;
use Result;

fn print_name(ty: &UnionType, w: &mut ValuePrinter) -> Result<()> {
    write!(w, "union ")?;
    if let Some(ref namespace) = ty.namespace {
        namespace.print(w)?;
    }
    write!(w, "{}", ty.name().unwrap_or("<anon>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &UnionType, w: &mut ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| print_name(ty, w))
}

pub(crate) fn print(ty: &UnionType, state: &mut PrintState, unit: &Unit, id: usize) -> Result<()> {
    state.collapsed(
        |state| state.id(id, |w, _state| print_name(ty, w)),
        |state| {
            if state.options().print_source {
                state.field("source", |w, _state| print_source(ty, w, unit))?;
            }
            state.field("declaration", |w, state| print_declaration(ty, w, state))?;
            state.field("size", |w, state| print_byte_size(ty, w, state))?;
            state.field_expanded("members", |state| print_members(ty, state, unit))
        },
    )?;
    state.line_break()?;
    Ok(())
}

pub(crate) fn diff(
    state: &mut DiffState,
    id: usize,
    unit_a: &Unit,
    a: &UnionType,
    unit_b: &Unit,
    b: &UnionType,
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
            state.field("declaration", a, b, |w, state, x| {
                print_declaration(x, w, state)
            })?;
            state.field("size", a, b, |w, state, x| print_byte_size(x, w, state))?;
            state.field_expanded("members", |state| diff_members(state, unit_a, a, unit_b, b))
        },
    )?;
    state.line_break()?;
    Ok(())
}

fn print_source(ty: &UnionType, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
    if ty.source.is_some() {
        ty.source.print(w, unit)?;
    }
    Ok(())
}

fn print_byte_size(ty: &UnionType, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
    if let Some(size) = ty.byte_size() {
        write!(w, "{}", size)?;
    } else if !ty.declaration {
        debug!("struct with no size");
    }
    Ok(())
}

fn print_declaration(ty: &UnionType, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
    if ty.declaration {
        write!(w, "yes")?;
    }
    Ok(())
}

pub(crate) fn print_members(ty: &UnionType, state: &mut PrintState, unit: &Unit) -> Result<()> {
    state.list(unit, &ty.members)
}

pub(crate) fn diff_members(
    state: &mut DiffState,
    unit_a: &Unit,
    a: &UnionType,
    unit_b: &Unit,
    b: &UnionType,
) -> Result<()> {
    // TODO: handle reordering better
    state.list(unit_a, &a.members, unit_b, &b.members)
}
