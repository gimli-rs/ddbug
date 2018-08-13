use function::Function;
use types::{EnumerationType, StructType, Type, TypeDef, TypeKind, UnionType, UnspecifiedType};
use Options;

pub(crate) fn filter_function(f: &Function, options: &Options) -> bool {
    if !f.inline && (f.address.is_none() || f.size.is_none()) {
        // This is either a declaration or a dead function that was removed
        // from the code, but wasn't removed from the debuginfo.
        // TODO: make this configurable?
        return false;
    }
    options.filter_name(f.name())
        && options.filter_namespace(&f.namespace)
        && options.filter_function_inline(f.inline)
}

pub(crate) fn filter_type(ty: &Type, options: &Options) -> bool {
    match ty.kind {
        TypeKind::Def(ref val) => filter_type_def(val, options),
        TypeKind::Struct(ref val) => filter_struct(val, options),
        TypeKind::Union(ref val) => filter_union(val, options),
        TypeKind::Enumeration(ref val) => filter_enumeration(val, options),
        TypeKind::Unspecified(ref val) => filter_unspecified(val, options),
        TypeKind::Base(..)
        | TypeKind::Array(..)
        | TypeKind::Function(..)
        | TypeKind::PointerToMember(..)
        | TypeKind::Modifier(..) => options.filter_name.is_none(),
    }
}

fn filter_type_def(ty: &TypeDef, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(&ty.namespace)
}

fn filter_struct(ty: &StructType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(&ty.namespace)
}

fn filter_union(ty: &UnionType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(&ty.namespace)
}

fn filter_enumeration(ty: &EnumerationType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(&ty.namespace)
}

fn filter_unspecified(ty: &UnspecifiedType, options: &Options) -> bool {
    options.filter_name(ty.name()) && options.filter_namespace(&ty.namespace)
}
