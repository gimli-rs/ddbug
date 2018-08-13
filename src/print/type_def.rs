use std::borrow::Cow;
use std::ops::Deref;

use file::FileHash;
use print::{self, DiffState, PrintState, ValuePrinter};
use types::TypeDef;
use unit::Unit;
use Result;

fn print_name(ty: &TypeDef, w: &mut ValuePrinter) -> Result<()> {
    if let Some(ref namespace) = ty.namespace {
        namespace.print(w)?;
    }
    write!(w, "{}", ty.name().unwrap_or("<anon-typedef>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &TypeDef, w: &mut ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| print_name(ty, w))
}

fn print_def(ty: &TypeDef, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    write!(w, "type ")?;
    print_name(ty, w)?;
    write!(w, " = ")?;
    print::types::print_ref_from_offset(w, hash, ty.ty)?;
    Ok(())
}

fn print_source(ty: &TypeDef, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
    if ty.source.is_some() {
        ty.source.print(w, unit)?;
    }
    Ok(())
}

fn print_byte_size(ty: &TypeDef, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
    if let Some(byte_size) = ty.byte_size(hash) {
        write!(w, "{}", byte_size)?;
    }
    Ok(())
}

pub(crate) fn print(x: &TypeDef, state: &mut PrintState, unit: &Unit, id: usize) -> Result<()> {
    let ty = x.ty(state.hash());
    state.collapsed(
        |state| state.id(id, |w, state| print_def(x, w, state)),
        |state| {
            if state.options().print_source {
                state.field("source", |w, _state| print_source(x, w, unit))?;
            }
            state.field("size", |w, state| print_byte_size(x, w, state))?;
            if let Some(ref ty) = ty {
                if ty.is_anon() {
                    state.field_expanded("members", |state| {
                        print::types::print_members(state, unit, Some(ty))
                    })?;
                }
            }
            Ok(())
        },
    )?;
    state.line_break()?;
    Ok(())
}

pub(crate) fn diff(
    state: &mut DiffState,
    id: usize,
    unit_a: &Unit,
    a: &TypeDef,
    unit_b: &Unit,
    b: &TypeDef,
) -> Result<()> {
    state.collapsed(
        |state| state.id(id, a, b, |w, state, x| print_def(x, w, state)),
        |state| {
            if state.options().print_source {
                state.field(
                    "source",
                    (unit_a, a),
                    (unit_b, b),
                    |w, _state, (unit, x)| print_source(x, w, unit),
                )?;
            }
            state.field("size", a, b, |w, state, x| print_byte_size(x, w, state))?;
            let ty_a = filter_option(a.ty(state.hash_a()), |ty| ty.is_anon());
            let ty_a = ty_a.as_ref().map(Cow::deref);
            let ty_b = filter_option(b.ty(state.hash_b()), |ty| ty.is_anon());
            let ty_b = ty_b.as_ref().map(Cow::deref);
            state.field_expanded("members", |state| {
                print::types::diff_members(state, unit_a, ty_a, unit_b, ty_b)
            })
        },
    )?;
    state.line_break()?;
    Ok(())
}

fn filter_option<T, F>(o: Option<T>, f: F) -> Option<T>
where
    F: FnOnce(&T) -> bool,
{
    o.and_then(|v| if f(&v) { Some(v) } else { None })
}
