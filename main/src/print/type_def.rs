use std::borrow::Cow;
use std::ops::Deref;

use parser::{FileHash, TypeDef, Unit};

use crate::print::{self, DiffState, PrintHeader, PrintState, ValuePrinter};
use crate::Result;

fn print_name(ty: &TypeDef, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(namespace) = ty.namespace() {
        print::namespace::print(namespace, w)?;
    }
    w.name(ty.name().unwrap_or("<anon-typedef>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &TypeDef, w: &mut dyn ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| print_name(ty, w))
}

fn print_def(ty: &TypeDef, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    write!(w, "type ")?;
    print_name(ty, w)?;
    write!(w, " = ")?;
    print::types::print_ref(ty.ty(hash), w, hash)?;
    Ok(())
}

fn print_source(ty: &TypeDef, w: &mut dyn ValuePrinter, unit: &Unit) -> Result<()> {
    print::source::print(ty.source(), w, unit)
}

fn print_byte_size(ty: &TypeDef, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    if let Some(byte_size) = ty.byte_size(hash) {
        write!(w, "{}", byte_size)?;
    }
    Ok(())
}

impl<'input> PrintHeader for TypeDef<'input> {
    fn print_header(&self, state: &mut PrintState) -> Result<()> {
        state.line(|w, state| print_def(self, w, state))
    }

    fn print_body(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        let ty = self.ty(state.hash());
        if state.options().print_source {
            state.field("source", |w, _state| print_source(self, w, unit))?;
        }
        state.field("size", |w, state| print_byte_size(self, w, state))?;
        if let Some(ref ty) = ty {
            if ty.is_anon() {
                state.field_expanded("members", |state| {
                    print::types::print_members(state, unit, Some(ty))
                })?;
            }
        }
        Ok(())
    }

    fn diff_header(state: &mut DiffState, a: &Self, b: &Self) -> Result<()> {
        state.line(a, b, |w, state, x| print_def(x, w, state))
    }

    fn diff_body(
        state: &mut DiffState,
        unit_a: &parser::Unit,
        a: &Self,
        unit_b: &parser::Unit,
        b: &Self,
    ) -> Result<()> {
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
    }
}

fn filter_option<T, F>(o: Option<T>, f: F) -> Option<T>
where
    F: FnOnce(&T) -> bool,
{
    o.and_then(|v| if f(&v) { Some(v) } else { None })
}
