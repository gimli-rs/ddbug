use parser::{BaseType, BaseTypeEncoding, Endianity, FileHash};

use crate::print::{DiffState, PrintState, ValuePrinter};
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

pub(crate) fn print(ty: &BaseType, state: &mut PrintState, id: usize) -> Result<()> {
    state.collapsed(
        |state| state.id(id, |w, _state| print_name(ty, w)),
        |state| {
            state.field("size", |w, state| print_byte_size(ty, w, state))?;
            state.field("encoding", |w, state| print_encoding(ty, w, state))?;
            state.field("endianity", |w, state| print_endianity(ty, w, state))
        },
    )?;
    state.line_break()?;
    Ok(())
}

pub(crate) fn diff(state: &mut DiffState, id: usize, a: &BaseType, b: &BaseType) -> Result<()> {
    // The names should be the same, but we can't be sure.
    state.collapsed(
        |state| state.id(id, a, b, |w, _state, x| print_name(x, w)),
        |state| {
            state.field("size", a, b, |w, state, x| print_byte_size(x, w, state))?;
            state.field("encoding", a, b, |w, state, x| print_encoding(x, w, state))?;
            state.field("endianity", a, b, |w, state, x| {
                print_endianity(x, w, state)
            })
        },
    )?;
    state.line_break()?;
    Ok(())
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
