use parser::{FileHash, StructType, Unit};

use crate::print::{self, DiffState, PrintHeader, PrintState, ValuePrinter};
use crate::Result;

fn print_name(ty: &StructType, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "struct ")?;
    if let Some(namespace) = ty.namespace() {
        print::namespace::print(namespace, w)?;
    }
    write!(w, "{}", ty.name().unwrap_or("<anon>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &StructType, w: &mut dyn ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| print_name(ty, w))
}

impl<'input> PrintHeader for StructType<'input> {
    fn print_header(&self, state: &mut PrintState) -> Result<()> {
        state.line(|w, _state| print_name(self, w))
    }

    fn print_body(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        if state.options().print_source {
            state.field("source", |w, _state| print_source(self, w, unit))?;
        }
        state.field("declaration", |w, state| print_declaration(self, w, state))?;
        state.field("size", |w, state| print_byte_size(self, w, state))?;
        print::inherit::print_list(state, self.inherits())?;
        state.field_expanded("members", |state| print_members(self, state, unit))
    }

    fn diff_header(state: &mut DiffState, a: &Self, b: &Self) -> Result<()> {
        state.line(a, b, |w, _state, x| print_name(x, w))
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
        state.field("declaration", a, b, |w, state, x| {
            print_declaration(x, w, state)
        })?;
        state.field("size", a, b, |w, state, x| print_byte_size(x, w, state))?;
        print::inherit::diff_list(state, a.inherits(), b.inherits())?;
        state.field_expanded("members", |state| diff_members(state, unit_a, a, unit_b, b))
    }
}

fn print_source(ty: &StructType, w: &mut dyn ValuePrinter, unit: &Unit) -> Result<()> {
    print::source::print(ty.source(), w, unit)
}

fn print_byte_size(ty: &StructType, w: &mut dyn ValuePrinter, _hash: &FileHash) -> Result<()> {
    if let Some(size) = ty.byte_size() {
        write!(w, "{}", size)?;
    } else if !ty.is_declaration() {
        debug!("struct with no size");
    }
    Ok(())
}

fn print_declaration(ty: &StructType, w: &mut dyn ValuePrinter, _hash: &FileHash) -> Result<()> {
    if ty.is_declaration() {
        write!(w, "yes")?;
    }
    Ok(())
}

pub(crate) fn print_members(ty: &StructType, state: &mut PrintState, unit: &Unit) -> Result<()> {
    let layout = ty.layout(state.hash());
    state.list(unit, &layout)
}

pub(crate) fn diff_members(
    state: &mut DiffState,
    unit_a: &Unit,
    a: &StructType,
    unit_b: &Unit,
    b: &StructType,
) -> Result<()> {
    let layout_a = a.layout(state.hash_a());
    let layout_b = b.layout(state.hash_b());
    state.list(unit_a, &layout_a, unit_b, &layout_b)
}
