use std::cmp;
use std::collections::HashSet;

use parser::{
    BaseType, EnumerationType, File, FileHash, Function, StructType, Type, TypeDef, TypeKind,
    TypeOffset, UnionType, Unit, UnspecifiedType, Variable,
};

use crate::Options;

pub(crate) fn filter_units<'input, 'file>(
    file: &'file File<'input>,
    options: &Options,
) -> Vec<&'file Unit<'input>> {
    file.units()
        .iter()
        .filter(|a| filter_unit(a, options))
        .collect()
}

pub(crate) fn enumerate_and_filter_units<'input, 'file>(
    file: &'file File<'input>,
    options: &Options,
) -> Vec<(usize, &'file Unit<'input>)> {
    file.units()
        .iter()
        .enumerate()
        .filter(|a| filter_unit(a.1, options))
        .collect()
}

/// Return true if this unit matches the filter options.
fn filter_unit(unit: &Unit, options: &Options) -> bool {
    if let Some(filter) = options.filter_unit.as_ref() {
        let (prefix, suffix) = options.prefix_map(unit.name().unwrap_or(""));
        let iter = prefix.bytes().chain(suffix.bytes());
        iter.cmp(filter.bytes()) == cmp::Ordering::Equal
    } else {
        true
    }
}

/// The offsets of types that should be printed inline.
fn inline_types(unit: &Unit, hash: &FileHash) -> HashSet<TypeOffset> {
    let mut inline_types = HashSet::new();
    for ty in unit.types() {
        // Assume all anonymous types are inline. We don't actually check
        // that they will be inline, but in future we could (eg for TypeDefs).
        // TODO: is this a valid assumption?
        if ty.is_anon() && ty.offset().is_some() {
            inline_types.insert(ty.offset());
        }

        // Find all inline members.
        for t in ty.members() {
            if t.is_inline(hash) && t.type_offset().is_some() {
                inline_types.insert(t.type_offset());
            }
        }
    }
    inline_types
}

/// Filter and the list of types using the options.
/// Perform additional filtering when diffing.
pub(crate) fn filter_types<'input, 'unit>(
    unit: &'unit Unit<'input>,
    hash: &FileHash,
    options: &Options,
    diff: bool,
) -> Vec<&'unit Type<'input>> {
    let inline_types = inline_types(unit, hash);
    unit.types()
        .iter()
        .filter(|a| filter_type(a, options, diff, &inline_types))
        .collect()
}

pub(crate) fn enumerate_and_filter_types<'input, 'unit>(
    unit: &'unit Unit<'input>,
    hash: &FileHash,
    options: &Options,
    diff: bool,
) -> Vec<(usize, &'unit Type<'input>)> {
    let inline_types = inline_types(unit, hash);
    unit.types()
        .iter()
        .enumerate()
        .filter(|a| filter_type(a.1, options, diff, &inline_types))
        .collect()
}

pub(crate) fn filter_functions<'input, 'unit>(
    unit: &'unit Unit<'input>,
    options: &Options,
) -> Vec<&'unit Function<'input>> {
    unit.functions()
        .iter()
        .filter(|a| filter_function(a, options))
        .collect()
}

pub(crate) fn enumerate_and_filter_functions<'input, 'unit>(
    unit: &'unit Unit<'input>,
    options: &Options,
) -> Vec<(usize, &'unit Function<'input>)> {
    unit.functions()
        .iter()
        .enumerate()
        .filter(|a| filter_function(a.1, options))
        .collect()
}

pub(crate) fn filter_variables<'input, 'unit>(
    unit: &'unit Unit<'input>,
    options: &Options,
) -> Vec<&'unit Variable<'input>> {
    unit.variables()
        .iter()
        .filter(|a| filter_variable(a, options))
        .collect()
}

pub(crate) fn enumerate_and_filter_variables<'input, 'unit>(
    unit: &'unit Unit<'input>,
    options: &Options,
) -> Vec<(usize, &'unit Variable<'input>)> {
    unit.variables()
        .iter()
        .enumerate()
        .filter(|a| filter_variable(a.1, options))
        .collect()
}

fn filter_function(f: &Function, options: &Options) -> bool {
    if !f.is_inline() && (f.address().is_none() || f.size().is_none()) {
        // This is either a declaration or a dead function that was removed
        // from the code, but wasn't removed from the debuginfo.
        // TODO: make this configurable?
        return false;
    }
    options.filter_name(f.name())
        && options.filter_namespace(f.namespace())
        && options.filter_function_inline(f.is_inline())
}

fn filter_variable(v: &Variable, options: &Options) -> bool {
    if !v.is_declaration() && v.address().is_none() {
        // TODO: make this configurable?
        return false;
    }
    options.filter_name(v.name()) && options.filter_namespace(v.namespace())
}

fn filter_type(
    ty: &Type,
    options: &Options,
    diff: bool,
    inline_types: &HashSet<TypeOffset>,
) -> bool {
    // Filter by user options.
    if !match ty.kind() {
        TypeKind::Base(val) => filter_base(val, options),
        TypeKind::Def(val) => filter_type_def(val, options),
        TypeKind::Struct(val) => filter_struct(val, options),
        TypeKind::Union(val) => filter_union(val, options),
        TypeKind::Enumeration(val) => filter_enumeration(val, options),
        TypeKind::Unspecified(val) => filter_unspecified(val, options),
        TypeKind::Void
        | TypeKind::Array(..)
        | TypeKind::Function(..)
        | TypeKind::PointerToMember(..)
        | TypeKind::Modifier(..)
        | TypeKind::Subrange(..) => options.filter_name.is_none(),
    } {
        return false;
    }
    match ty.kind() {
        TypeKind::Struct(val) => {
            // Hack for rust closures
            // TODO: is there better way of identifying these, or a
            // a way to match pairs for diffing?
            if diff && val.name() == Some("closure") {
                return false;
            }
        }
        TypeKind::Base(..)
        | TypeKind::Def(..)
        | TypeKind::Union(..)
        | TypeKind::Enumeration(..) => {}
        TypeKind::Void
        | TypeKind::Array(..)
        | TypeKind::Function(..)
        | TypeKind::Unspecified(..)
        | TypeKind::PointerToMember(..)
        | TypeKind::Modifier(..)
        | TypeKind::Subrange(..) => return false,
    }
    // Filter out inline types.
    ty.offset().is_some() && !inline_types.contains(&ty.offset())
}

fn filter_base(ty: &BaseType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(None)
}

fn filter_type_def(ty: &TypeDef, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(ty.namespace())
}

fn filter_struct(ty: &StructType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(ty.namespace())
}

fn filter_union(ty: &UnionType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(ty.namespace())
}

fn filter_enumeration(ty: &EnumerationType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(ty.namespace())
}

fn filter_unspecified(ty: &UnspecifiedType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(ty.namespace())
}
