use parser::{BaseType, BaseTypeEncoding, Endianity, FileHash, Unit};

use crate::print::{DiffState, PrintHeader, PrintState, ValuePrinter};
use crate::Result;

fn print_name(ty: &BaseType, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(w, "base {}", ty.name().unwrap_or("<anon>"))?;
    Ok(())
}

pub(crate) fn print_ref(ty: &BaseType, w: &mut dyn ValuePrinter, id: usize) -> Result<()> {
    w.link(id, &mut |w| {
        write!(w, "{}", ty.name().unwrap_or("<anon-base-type>"))?;
        Ok(())
    })
}

impl<'input> PrintHeader for BaseType<'input> {
    fn print_header(&self, state: &mut PrintState) -> Result<()> {
        state.line(|w, _state| print_name(self, w))
    }

    fn print_body(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.field("size", |w, state| print_byte_size(self, w, state))?;
        state.field("encoding", |w, state| print_encoding(self, w, state))?;
        state.field("endianity", |w, state| print_endianity(self, w, state))
    }

    fn diff_header(state: &mut DiffState, a: &Self, b: &Self) -> Result<()> {
        state.line(a, b, |w, _state, x| print_name(x, w))
    }

    fn diff_body(
        state: &mut DiffState,
        _unit_a: &parser::Unit,
        a: &Self,
        _unit_b: &parser::Unit,
        b: &Self,
    ) -> Result<()> {
        state.field("size", a, b, |w, state, x| print_byte_size(x, w, state))?;
        state.field("encoding", a, b, |w, state, x| print_encoding(x, w, state))?;
        state.field("endianity", a, b, |w, state, x| {
            print_endianity(x, w, state)
        })
    }
}

fn print_byte_size(ty: &BaseType, w: &mut dyn ValuePrinter, _hash: &FileHash) -> Result<()> {
    if let Some(size) = ty.byte_size() {
        write!(w, "{}", size)?;
    } else {
        debug!("base type with no size");
    }
    Ok(())
}

fn print_encoding(ty: &BaseType, w: &mut dyn ValuePrinter, _hash: &FileHash) -> Result<()> {
    let name = match ty.encoding() {
        BaseTypeEncoding::Other => return Ok(()),
        BaseTypeEncoding::Boolean => "boolean",
        BaseTypeEncoding::Address => "address",
        BaseTypeEncoding::Signed => "signed",
        BaseTypeEncoding::SignedChar => "signed char",
        BaseTypeEncoding::Unsigned => "unsigned",
        BaseTypeEncoding::UnsignedChar => "unsigned char",
        BaseTypeEncoding::Float => "floating-point",
    };
    write!(w, "{}", name)?;
    Ok(())
}

fn print_endianity(ty: &BaseType, w: &mut dyn ValuePrinter, _hash: &FileHash) -> Result<()> {
    let name = match ty.endianity() {
        Endianity::Default => return Ok(()),
        Endianity::Big => "big",
        Endianity::Little => "little",
    };
    write!(w, "{}", name)?;
    Ok(())
}
