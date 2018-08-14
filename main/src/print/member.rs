use std::borrow::Cow;
use std::cmp;
use std::ops::Deref;

use parser::{FileHash, Member, Type, Unit};
use print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use Result;

fn print_name(
    member: &Member,
    w: &mut ValuePrinter,
    hash: &FileHash,
    bit_size: Option<u64>,
) -> Result<()> {
    write!(w, "{}", format_bit(member.bit_offset))?;
    match bit_size {
        Some(bit_size) => {
            write!(w, "[{}]", format_bit(bit_size))?;
        }
        None => {
            // TODO: show element size for unsized arrays.
            debug!("no size for {:?}", member);
            write!(w, "[??]")?;
        }
    }
    write!(w, "\t{}: ", member.name().unwrap_or("<anon>"))?;
    print::types::print_ref_from_offset(w, hash, member.ty)?;
    Ok(())
}

fn print_padding(
    member: &Member,
    w: &mut ValuePrinter,
    _hash: &FileHash,
    bit_size: Option<u64>,
) -> Result<()> {
    if let Some(padding) = member.padding(bit_size) {
        write!(
            w,
            "{}[{}]\t<padding>",
            format_bit(padding.bit_offset),
            format_bit(padding.bit_size)
        )?;
    }
    Ok(())
}

impl<'input> Print for Member<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        let hash = state.hash();
        let bit_size = self.bit_size(hash);
        let ty = if self.is_inline(hash) {
            self.ty(hash)
        } else {
            None
        };
        let ty = ty.as_ref().map(Cow::deref);
        state.expanded(
            |state| state.line(|w, state| print_name(self, w, state, bit_size)),
            |state| print::types::print_members(state, unit, ty),
        )?;
        state.line(|w, state| print_padding(self, w, state, bit_size))
    }

    fn diff(state: &mut DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> Result<()> {
        let bit_size_a = a.bit_size(state.hash_a());
        let bit_size_b = b.bit_size(state.hash_b());
        let ty_a = if a.is_inline(state.hash_a()) {
            a.ty(state.hash_a())
        } else {
            None
        };
        let ty_a = ty_a.as_ref().map(Cow::deref);
        let ty_b = if b.is_inline(state.hash_b()) {
            b.ty(state.hash_b())
        } else {
            None
        };
        let ty_b = ty_b.as_ref().map(Cow::deref);
        state.expanded(
            |state| {
                state.line(
                    (a, bit_size_a),
                    (b, bit_size_b),
                    |w, state, (x, bit_size)| print_name(x, w, state, bit_size),
                )
            },
            |state| print::types::diff_members(state, unit_a, ty_a, unit_b, ty_b),
        )?;

        state.line(
            (a, bit_size_a),
            (b, bit_size_b),
            |w, state, (x, bit_size)| print_padding(x, w, state, bit_size),
        )
    }
}

impl<'input> DiffList for Member<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 1;
        }
        match (a.ty(state.hash_a()), b.ty(state.hash_b())) {
            (Some(ref ty_a), Some(ref ty_b)) => {
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

fn format_bit(val: u64) -> String {
    let byte = val / 8;
    let bit = val % 8;
    if bit == 0 {
        format!("{}", byte)
    } else {
        format!("{}.{}", byte, bit)
    }
}
