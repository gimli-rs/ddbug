use std::borrow::Cow;
use std::cmp;
use std::ops::Deref;

use parser::{FileHash, Inherit, Layout, LayoutItem, Member, Type, Unit, Variant, VariantPart};

use crate::print::{self, DiffList, DiffState, Print, PrintState, ValuePrinter};
use crate::Result;

fn print_member(member: &Member, w: &mut dyn ValuePrinter, hash: &FileHash) -> Result<()> {
    write!(w, "{}", format_bit(member.bit_offset()))?;
    match member.bit_size(hash) {
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
    print::types::print_ref(member.ty(hash), w, hash)?;
    Ok(())
}

fn print_variant_part(
    layout: &Layout,
    _variant_part: &VariantPart,
    w: &mut dyn ValuePrinter,
) -> Result<()> {
    // TODO: indicate which discriminant
    write!(
        w,
        "{}[{}]\t<variant part>",
        format_bit(layout.bit_offset),
        format_bit(layout.bit_size.get().unwrap_or(0)),
    )?;
    Ok(())
}

fn print_variant(variant: &Variant, w: &mut dyn ValuePrinter) -> Result<()> {
    if let Some(name) = variant.name() {
        write!(w, "{}: ", name)?;
    }
    // TODO: use discriminant type to display value
    write!(w, "<{}>", variant.discriminant_value().unwrap_or(0))?;
    Ok(())
}

fn print_inherit(
    layout: &Layout,
    inherit: &Inherit,
    w: &mut dyn ValuePrinter,
    hash: &FileHash,
) -> Result<()> {
    write!(
        w,
        "{}[{}]\t<inherit>: ",
        format_bit(layout.bit_offset),
        format_bit(layout.bit_size.get().unwrap_or(0))
    )?;
    print::types::print_ref(inherit.ty(hash), w, hash)?;
    Ok(())
}

fn print_padding(layout: &Layout, w: &mut dyn ValuePrinter) -> Result<()> {
    write!(
        w,
        "{}[{}]\t<padding>",
        format_bit(layout.bit_offset),
        format_bit(layout.bit_size.get().unwrap_or(0))
    )?;
    Ok(())
}

impl<'input> Print for Member<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        let hash = state.hash();
        let ty = if self.is_inline(hash) {
            self.ty(hash)
        } else {
            None
        };
        let ty = ty.as_ref().map(Cow::deref);
        state.expanded(
            |state| state.line(|w, hash| print_member(self, w, hash)),
            |state| print::types::print_members(state, unit, ty),
        )
    }

    fn diff(state: &mut DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> Result<()> {
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
            |state| state.line(a, b, |w, hash, x| print_member(x, w, hash)),
            |state| print::types::diff_members(state, unit_a, ty_a, unit_b, ty_b),
        )
    }
}

impl<'input> DiffList for Member<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name().cmp(&b.name()) != cmp::Ordering::Equal {
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

impl<'input> Print for Variant<'input> {
    type Arg = (&'input Unit<'input>, u64, Option<u64>);

    fn print(
        &self,
        state: &mut PrintState,
        (unit, bit_offset, bit_size): &Self::Arg,
    ) -> Result<()> {
        state.expanded(
            |state| state.line(|w, _hash| print_variant(self, w)),
            |state| {
                let layout = self.layout(*bit_offset, *bit_size, state.hash());
                state.list(*unit, &layout)
            },
        )
    }

    fn diff(
        state: &mut DiffState,
        (unit_a, bit_offset_a, bit_size_a): &Self::Arg,
        a: &Self,
        (unit_b, bit_offset_b, bit_size_b): &Self::Arg,
        b: &Self,
    ) -> Result<()> {
        state.expanded(
            |state| state.line(a, b, |w, _hash, variant| print_variant(variant, w)),
            |state| {
                let layout_a = a.layout(*bit_offset_a, *bit_size_a, state.hash_a());
                let layout_b = b.layout(*bit_offset_b, *bit_size_b, state.hash_b());
                state.list(*unit_a, &layout_a, *unit_b, &layout_b)
            },
        )
    }
}

impl<'input> DiffList for Variant<'input> {
    fn step_cost(&self, _state: &DiffState, _arg: &Self::Arg) -> usize {
        1
    }

    fn diff_cost(
        _state: &DiffState,
        _arg_a: &Self::Arg,
        a: &Self,
        _arg_b: &Self::Arg,
        b: &Self,
    ) -> usize {
        let mut cost = 0;
        if a.name().cmp(&b.name()) != cmp::Ordering::Equal {
            cost += 1;
        }
        if a.discriminant_value() != b.discriminant_value() {
            cost += 1;
        }
        cost
    }
}

impl<'input, 'member> Print for Layout<'input, 'member> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        match self.item {
            LayoutItem::Padding => state.line(|w, _hash| print_padding(self, w)),
            LayoutItem::Member(member) => member.print(state, unit),
            LayoutItem::VariantPart(variant_part) => state.expanded(
                |state| state.line(|w, _hash| print_variant_part(self, variant_part, w)),
                |state| {
                    state.list(
                        &(unit, self.bit_offset, self.bit_size.get()),
                        variant_part.variants(),
                    )
                },
            ),
            LayoutItem::Inherit(inherit) => {
                state.line(|w, hash| print_inherit(self, inherit, w, hash))
            }
        }
    }

    fn diff(state: &mut DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> Result<()> {
        match (&a.item, &b.item) {
            (&LayoutItem::Padding, &LayoutItem::Padding) => {
                state.line(a, b, |w, _hash, x| print_padding(x, w))
            }
            (&LayoutItem::Member(ref member_a), &LayoutItem::Member(ref member_b)) => {
                Member::diff(state, unit_a, member_a, unit_b, member_b)
            }
            (
                &LayoutItem::VariantPart(ref variant_part_a),
                &LayoutItem::VariantPart(ref variant_part_b),
            ) => state.expanded(
                |state| {
                    state.line(
                        (a, variant_part_a),
                        (b, variant_part_b),
                        |w, _hash, (x, v)| print_variant_part(x, v, w),
                    )
                },
                |state| {
                    let variants_a = variant_part_a.variants();
                    let variants_b = variant_part_b.variants();
                    state.list(
                        &(unit_a, a.bit_offset, a.bit_size.get()),
                        variants_a,
                        &(unit_b, b.bit_offset, b.bit_size.get()),
                        variants_b,
                    )
                },
            ),
            (&LayoutItem::Inherit(ref inherit_a), &LayoutItem::Inherit(ref inherit_b)) => state
                .line((a, inherit_a), (b, inherit_b), |w, hash, (x, inherit)| {
                    print_inherit(x, inherit, w, hash)
                }),
            _ => state.block((unit_a, a), (unit_b, b), |state, (unit, x)| {
                Layout::print(x, state, unit)
            }),
        }
    }
}

impl<'input, 'member> DiffList for Layout<'input, 'member> {
    fn step_cost(&self, _state: &DiffState, _arg: &Unit) -> usize {
        // Must be same as diff cost for each layout item
        1
    }

    fn diff_cost(state: &DiffState, unit_a: &Unit, a: &Self, unit_b: &Unit, b: &Self) -> usize {
        match (&a.item, &b.item) {
            (&LayoutItem::Padding, &LayoutItem::Padding) => 0,
            (&LayoutItem::Member(ref a), &LayoutItem::Member(ref b)) => {
                Member::diff_cost(state, unit_a, a, unit_b, b)
            }
            (&LayoutItem::VariantPart(ref _a), &LayoutItem::VariantPart(ref _b)) => {
                // TODO: for now we assume there is only one variant part
                // Later we should compare `VariantPart::discr`
                0
            }
            (&LayoutItem::Inherit(ref a), &LayoutItem::Inherit(ref b)) => {
                Inherit::diff_cost(state, &(), a, &(), b)
            }
            _ => 2,
        }
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
