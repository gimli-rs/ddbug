use parser::{FileHash, StructType, Unit};
use print::{self, DiffState, PrintState, ValuePrinter};
use Result;

fn print_name(ty: &StructType, w: &mut ValuePrinter) -> Result<()> {
    write!(w, "struct ")?;
    if let Some(namespace) = ty.namespace() {
        print::namespace::print(namespace, w)?;
    }
    write!(w, "{}", ty.name().unwrap_or("<anon>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &StructType, w: &mut ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| print_name(ty, w))
}

pub(crate) fn print(ty: &StructType, state: &mut PrintState, unit: &Unit, id: usize) -> Result<()> {
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
    a: &StructType,
    unit_b: &Unit,
    b: &StructType,
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

fn print_source(ty: &StructType, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
    print::source::print(ty.source(), w, unit)
}

fn print_byte_size(ty: &StructType, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
    if let Some(size) = ty.byte_size() {
        write!(w, "{}", size)?;
    } else if !ty.is_declaration() {
        debug!("struct with no size");
    }
    Ok(())
}

fn print_declaration(ty: &StructType, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
    if ty.is_declaration() {
        write!(w, "yes")?;
    }
    Ok(())
}

pub(crate) fn print_members(ty: &StructType, state: &mut PrintState, unit: &Unit) -> Result<()> {
    state.list(unit, ty.members())
}

pub(crate) fn diff_members(
    state: &mut DiffState,
    unit_a: &Unit,
    a: &StructType,
    unit_b: &Unit,
    b: &StructType,
) -> Result<()> {
    state.list(unit_a, a.members(), unit_b, b.members())
}
