use std::cmp;

use parser::{EnumerationType, Enumerator, FileHash, Unit};

use crate::print::{self, DiffList, DiffState, Print, PrintHeader, PrintState, ValuePrinter};
use crate::Result;

fn print_name(ty: &EnumerationType, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "enum ")?;
    if let Some(namespace) = ty.namespace() {
        print::namespace::print(namespace, w)?;
    }
    write!(w, "{}", ty.name().unwrap_or("<anon>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &EnumerationType, w: &mut dyn ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| print_name(ty, w))
}

impl<'input> PrintHeader for EnumerationType<'input> {
    fn print_header(&self, state: &mut PrintState) -> Result<()> {
        state.line(|w, _state| print_name(self, w))
    }

    fn print_body(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        if state.options().print_source {
            state.field("source", |w, _state| print_source(self, w, unit))?;
        }
        state.field("declaration", |w, _state| print_declaration(self, w))?;
        state.field("size", |w, state| print_byte_size(self, w, state))?;
        let enumerators = self.enumerators(state.hash());
        state.field_expanded("enumerators", |state| state.list(unit, &enumerators))
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
        state.field("declaration", a, b, |w, _state, x| print_declaration(x, w))?;
        state.field("size", a, b, |w, state, x| print_byte_size(x, w, state))?;
        // TODO: handle reordering better
        let enumerators_a = a.enumerators(state.hash_a());
        let enumerators_b = b.enumerators(state.hash_b());
        state.field_expanded("enumerators", |state| {
            state.list(unit_a, &enumerators_a, unit_b, &enumerators_b)
        })
    }
}

fn print_source(ty: &EnumerationType, w: &mut dyn ValuePrinter, unit: &Unit) -> Result<()> {
    print::source::print(ty.source(), w, unit)
}

fn print_declaration(ty: &EnumerationType, w: &mut dyn ValuePrinter) -> Result<()> {
    if ty.is_declaration() {
        write!(w, "yes")?;
    }
    Ok(())
}

fn print_byte_size(ty: &EnumerationType, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    if let Some(size) = ty.byte_size(hash) {
        write!(w, "{}", size)?;
    } else {
        debug!("enum with no size");
    }
    Ok(())
}

fn print_enumerator(ty: &Enumerator, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "{}", ty.name().unwrap_or("<anon>"))?;
    if let Some(value) = ty.value() {
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
        if a.name().cmp(&b.name()) != cmp::Ordering::Equal {
            cost += 4;
        }
        if a.value().cmp(&b.value()) != cmp::Ordering::Equal {
            cost += 2;
        }
        cost
    }
}
