use std::borrow::Cow;
use std::cmp;
use std::marker;
use std::sync::Arc;
use std::usize;

use crate::file::FileHash;
use crate::function::ParameterOffset;
use crate::namespace::Namespace;
use crate::source::Source;
use crate::{Id, Size};

/// The kind of a type.
#[derive(Debug, Clone)]
pub enum TypeKind<'input> {
    /// The void type.
    Void,
    /// A base type.
    Base(BaseType<'input>),
    /// A type alias definition.
    Def(TypeDef<'input>),
    /// A struct type.
    Struct(StructType<'input>),
    /// A union type.
    Union(UnionType<'input>),
    /// An enumeration type.
    Enumeration(EnumerationType<'input>),
    /// A type for an array of elements.
    Array(ArrayType<'input>),
    /// A function type.
    Function(FunctionType<'input>),
    /// An unspecified type.
    Unspecified(UnspecifiedType<'input>),
    /// The type of a pointer to a member.
    PointerToMember(PointerToMemberType),
    /// A type that is obtained by adding a modifier to another type.
    Modifier(TypeModifier<'input>),
    /// A subrange of another type.
    Subrange(SubrangeType<'input>),
}

impl<'input> TypeKind<'input> {
    fn discriminant_value(&self) -> u8 {
        match *self {
            TypeKind::Void => 1,
            TypeKind::Base(..) => 2,
            TypeKind::Def(..) => 3,
            TypeKind::Struct(..) => 4,
            TypeKind::Union(..) => 5,
            TypeKind::Enumeration(..) => 6,
            TypeKind::Array(..) => 7,
            TypeKind::Function(..) => 8,
            TypeKind::Unspecified(..) => 9,
            TypeKind::PointerToMember(..) => 10,
            TypeKind::Modifier(..) => 11,
            TypeKind::Subrange(..) => 12,
        }
    }
}

/// The debuginfo offset of a type.
///
/// This is unique for all types in a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeOffset(usize);

impl TypeOffset {
    #[inline]
    pub(crate) fn new(offset: usize) -> TypeOffset {
        debug_assert!(TypeOffset(offset) != TypeOffset::none());
        TypeOffset(offset)
    }

    #[inline]
    pub(crate) fn none() -> TypeOffset {
        TypeOffset(usize::MAX)
    }

    /// Return true if the type is unknown or `void`.
    #[inline]
    pub fn is_none(self) -> bool {
        self == Self::none()
    }

    /// Return true if the type is known and not `void`.
    #[inline]
    pub fn is_some(self) -> bool {
        self != Self::none()
    }

    #[inline]
    pub(crate) fn get(self) -> Option<usize> {
        if self.is_none() {
            None
        } else {
            Some(self.0)
        }
    }
}

impl Default for TypeOffset {
    #[inline]
    fn default() -> Self {
        TypeOffset::none()
    }
}

/// A type.
#[derive(Debug, Clone)]
pub struct Type<'input> {
    pub(crate) id: Id,
    pub(crate) offset: TypeOffset,
    pub(crate) kind: TypeKind<'input>,
}

impl<'input> Default for Type<'input> {
    fn default() -> Self {
        Type {
            id: Id::new(0),
            offset: TypeOffset::none(),
            kind: TypeKind::Base(BaseType::default()),
        }
    }
}

impl<'input> Type<'input> {
    /// Lookup a type given its offset.
    ///
    /// Returns `None` if the type offset is invalid.
    pub fn from_offset<'a>(
        hash: &'a FileHash<'input>,
        offset: TypeOffset,
    ) -> Option<Cow<'a, Type<'input>>> {
        if offset.is_none() {
            return Some(Cow::Borrowed(&hash.void));
        }
        hash.types
            .get(&offset)
            .map(|ty| Cow::Borrowed(*ty))
            .or_else(|| hash.file.get_type(offset).map(Cow::Owned))
    }

    pub(crate) fn void() -> Type<'static> {
        Type {
            id: Id::new(usize::MAX),
            offset: TypeOffset(usize::MAX),
            kind: TypeKind::Void,
        }
    }

    /// Return true if the type is the void type.
    #[inline]
    pub fn is_void(&self) -> bool {
        match self.kind {
            TypeKind::Void => true,
            _ => false,
        }
    }

    /// The user defined id for this type.
    #[inline]
    pub fn id(&self) -> usize {
        self.id.get()
    }

    /// Set a user defined id for this type.
    #[inline]
    pub fn set_id(&self, id: usize) {
        self.id.set(id)
    }

    /// The debuginfo offset of this type.
    #[inline]
    pub fn offset(&self) -> TypeOffset {
        self.offset
    }

    /// The kind of this type.
    #[inline]
    pub fn kind(&self) -> &TypeKind<'input> {
        &self.kind
    }

    /// The size in bytes of an instance of this type.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        match self.kind {
            TypeKind::Void => Some(0),
            TypeKind::Base(ref val) => val.byte_size(),
            TypeKind::Def(ref val) => val.byte_size(hash),
            TypeKind::Struct(ref val) => val.byte_size(),
            TypeKind::Union(ref val) => val.byte_size(),
            TypeKind::Enumeration(ref val) => val.byte_size(hash),
            TypeKind::Array(ref val) => val.byte_size(hash),
            TypeKind::Function(ref val) => val.byte_size(),
            TypeKind::Unspecified(..) => None,
            TypeKind::PointerToMember(ref val) => val.byte_size(hash),
            TypeKind::Modifier(ref val) => val.byte_size(hash),
            TypeKind::Subrange(ref val) => val.byte_size(hash),
        }
    }

    /// Return true if this is an anonymous type, or defined within an anonymous type.
    pub fn is_anon(&self) -> bool {
        match self.kind {
            TypeKind::Struct(ref val) => val.is_anon(),
            TypeKind::Union(ref val) => val.is_anon(),
            TypeKind::Void
            | TypeKind::Base(..)
            | TypeKind::Def(..)
            | TypeKind::Enumeration(..)
            | TypeKind::Array(..)
            | TypeKind::Function(..)
            | TypeKind::Unspecified(..)
            | TypeKind::PointerToMember(..)
            | TypeKind::Modifier(..)
            | TypeKind::Subrange(..) => false,
        }
    }

    /// Return true if this is the type of a function (including aliases and modifiers).
    fn is_function(&self, hash: &FileHash) -> bool {
        match self.kind {
            TypeKind::Function(..) => true,
            TypeKind::Def(ref val) => match val.ty(hash) {
                Some(ty) => ty.is_function(hash),
                None => false,
            },
            TypeKind::Modifier(ref val) => match val.ty(hash) {
                Some(ty) => ty.is_function(hash),
                None => false,
            },
            TypeKind::Void
            | TypeKind::Struct(..)
            | TypeKind::Union(..)
            | TypeKind::Base(..)
            | TypeKind::Enumeration(..)
            | TypeKind::Array(..)
            | TypeKind::Unspecified(..)
            | TypeKind::PointerToMember(..)
            | TypeKind::Subrange(..) => false,
        }
    }

    /// The members of this type.
    pub fn members(&self) -> &[Member<'input>] {
        match self.kind {
            TypeKind::Struct(ref val) => val.members(),
            TypeKind::Union(ref val) => val.members(),
            TypeKind::Void
            | TypeKind::Enumeration(..)
            | TypeKind::Def(..)
            | TypeKind::Base(..)
            | TypeKind::Array(..)
            | TypeKind::Function(..)
            | TypeKind::Unspecified(..)
            | TypeKind::PointerToMember(..)
            | TypeKind::Modifier(..)
            | TypeKind::Subrange(..) => &[],
        }
    }

    /// Compare the identifying information of two types.
    ///
    /// Equal types must have the same type kind. Further requirements for equality
    /// depend on the specific type kind.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        type_a: &Type,
        hash_b: &FileHash,
        type_b: &Type,
    ) -> cmp::Ordering {
        use self::TypeKind::*;
        match (&type_a.kind, &type_b.kind) {
            (&Base(ref a), &Base(ref b)) => BaseType::cmp_id(a, b),
            (&Def(ref a), &Def(ref b)) => TypeDef::cmp_id(a, b),
            (&Struct(ref a), &Struct(ref b)) => StructType::cmp_id(a, b),
            (&Union(ref a), &Union(ref b)) => UnionType::cmp_id(a, b),
            (&Enumeration(ref a), &Enumeration(ref b)) => EnumerationType::cmp_id(a, b),
            (&Array(ref a), &Array(ref b)) => ArrayType::cmp_id(hash_a, a, hash_b, b),
            (&Function(ref a), &Function(ref b)) => FunctionType::cmp_id(hash_a, a, hash_b, b),
            (&Unspecified(ref a), &Unspecified(ref b)) => UnspecifiedType::cmp_id(a, b),
            (&PointerToMember(ref a), &PointerToMember(ref b)) => {
                PointerToMemberType::cmp_id(hash_a, a, hash_b, b)
            }
            (&Modifier(ref a), &Modifier(ref b)) => TypeModifier::cmp_id(hash_a, a, hash_b, b),
            (&Subrange(ref a), &Subrange(ref b)) => SubrangeType::cmp_id(hash_a, a, hash_b, b),
            _ => {
                let discr_a = type_a.kind.discriminant_value();
                let discr_b = type_b.kind.discriminant_value();
                debug_assert_ne!(discr_a, discr_b);
                discr_a.cmp(&discr_b)
            }
        }
    }
}

/// A type that is obtained by adding a modifier to another type.
#[derive(Debug, Clone)]
pub struct TypeModifier<'input> {
    pub(crate) kind: TypeModifierKind,
    pub(crate) ty: TypeOffset,
    pub(crate) name: Option<&'input str>,
    pub(crate) byte_size: Size,
    // TODO: hack
    pub(crate) address_size: Option<u64>,
}

/// The kind of a type modifier.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TypeModifierKind {
    /// The resulting type is a pointer to the type being modified.
    Pointer,
    /// The resulting type is a reference to the type being modified.
    Reference,
    /// The resulting type is a constant.
    Const,
    /// The resulting type is packed.
    Packed,
    /// The resulting type is volatile.
    Volatile,
    /// The resulting type has restricted aliasing.
    Restrict,
    /// The resulting type is shared (for example, in UPC).
    Shared,
    /// The resulting type is a rvalue reference to the type being modified.
    RvalueReference,
    /// The resulting type is atomic.
    Atomic,
    // TODO:
    // Immutable,
    /// Any other type modifier.
    // PDB is disabled
    #[allow(dead_code)]
    Other,
}

impl TypeModifierKind {
    fn discriminant_value(self) -> u8 {
        match self {
            TypeModifierKind::Pointer => 1,
            TypeModifierKind::Reference => 2,
            TypeModifierKind::Const => 3,
            TypeModifierKind::Packed => 4,
            TypeModifierKind::Volatile => 5,
            TypeModifierKind::Restrict => 6,
            TypeModifierKind::Shared => 7,
            TypeModifierKind::RvalueReference => 8,
            TypeModifierKind::Atomic => 9,
            TypeModifierKind::Other => 10,
        }
    }
}

impl<'input> TypeModifier<'input> {
    /// The name of the type.
    ///
    /// If this is `None` then the name should be derived from the type that is being modified.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The kind of this type modifier.
    #[inline]
    pub fn kind(&self) -> TypeModifierKind {
        self.kind
    }

    /// The type that is being modified.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    fn is_pointer_like(&self) -> bool {
        match self.kind {
            TypeModifierKind::Const
            | TypeModifierKind::Packed
            | TypeModifierKind::Volatile
            | TypeModifierKind::Restrict
            | TypeModifierKind::Shared
            | TypeModifierKind::Atomic
            | TypeModifierKind::Other => false,
            TypeModifierKind::Pointer
            | TypeModifierKind::Reference
            | TypeModifierKind::RvalueReference => true,
        }
    }

    /// The size in bytes of an instance of this type.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            return self.byte_size.get();
        }
        if self.is_pointer_like() {
            self.address_size
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash))
        }
    }

    /// Compare the identifying information of two types.
    ///
    /// Type modifiers are equal if the modifiers are the same and the types being modified
    /// are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &TypeModifier,
        hash_b: &FileHash,
        b: &TypeModifier,
    ) -> cmp::Ordering {
        match (a.ty(hash_a), b.ty(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => {
                let ord = Type::cmp_id(hash_a, ty_a, hash_b, ty_b);
                if ord != cmp::Ordering::Equal {
                    return ord;
                }
            }
            (Some(_), None) => {
                return cmp::Ordering::Less;
            }
            (None, Some(_)) => {
                return cmp::Ordering::Greater;
            }
            (None, None) => {}
        }
        let discr_a = a.kind.discriminant_value();
        let discr_b = b.kind.discriminant_value();
        discr_a.cmp(&discr_b)
    }
}

/// The endianity of an object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endianity {
    /// Default endianity encoding.
    Default,
    /// Big-endian encoding.
    Big,
    /// Little-endian encoding.
    Little,
}

impl Default for Endianity {
    fn default() -> Self {
        Self::Default
    }
}

/// The encoding of a base type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseTypeEncoding {
    /// Unsupported or unspecified encoding.
    Other,
    /// True or false.
    Boolean,
    /// Linear machine address.
    Address,
    /// Signed binary integer.
    Signed,
    /// Signed character.
    SignedChar,
    /// Unsigned binary integer.
    Unsigned,
    /// Unsigned character.
    UnsignedChar,
    /// Binary floating-point number.
    Float,
}

impl Default for BaseTypeEncoding {
    fn default() -> Self {
        Self::Other
    }
}

/// A base type.
#[derive(Debug, Default, Clone)]
pub struct BaseType<'input> {
    pub(crate) name: Option<&'input str>,
    pub(crate) byte_size: Size,
    pub(crate) encoding: BaseTypeEncoding,
    pub(crate) endianity: Endianity,
}

impl<'input> BaseType<'input> {
    /// The name of the type.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The size in bytes of an instance of this type.
    #[inline]
    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    /// How the base type is encoded an interpreted.
    #[inline]
    pub fn encoding(&self) -> BaseTypeEncoding {
        self.encoding
    }

    /// The endianity of the value, if applicable.
    #[inline]
    pub fn endianity(&self) -> Endianity {
        self.endianity
    }

    /// Compare the identifying information of two types.
    ///
    /// Base types are considered equal if their names are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &BaseType, b: &BaseType) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}

/// A type alias definition.
#[derive(Debug, Default, Clone)]
pub struct TypeDef<'input> {
    pub(crate) namespace: Option<Arc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
    pub(crate) ty: TypeOffset,
    pub(crate) source: Source<'input>,
}

impl<'input> TypeDef<'input> {
    /// The namespace of the type.
    pub fn namespace(&self) -> Option<&Namespace> {
        self.namespace.as_ref().map(|x| &**x)
    }

    /// The name of the type definition.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The type that the alias is being defined for.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The source information for the type definition.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.source
    }

    /// The size in bytes of an instance of this type.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash))
    }

    /// Compare the identifying information of two types.
    ///
    /// Type definitions are considered equal if their names are equal, even if the type being
    /// aliased is different.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &TypeDef, b: &TypeDef) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(a.namespace(), a.name(), b.namespace(), b.name())
    }
}

/// A struct type.
#[derive(Debug, Default, Clone)]
pub struct StructType<'input> {
    pub(crate) namespace: Option<Arc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
    pub(crate) source: Source<'input>,
    pub(crate) byte_size: Size,
    pub(crate) declaration: bool,
    pub(crate) members: Vec<Member<'input>>,
    pub(crate) variant_parts: Vec<VariantPart<'input>>,
    pub(crate) inherits: Vec<Inherit>,
}

impl<'input> StructType<'input> {
    /// The namespace of the type.
    pub fn namespace(&self) -> Option<&Namespace> {
        self.namespace.as_ref().map(|x| &**x)
    }

    /// The name of the type.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The source information for the type.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.source
    }

    /// The size in bytes of an instance of this type.
    #[inline]
    pub fn bit_size(&self) -> Option<u64> {
        self.byte_size.get().map(|v| v * 8)
    }

    /// The size in bytes of an instance of this type.
    #[inline]
    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    /// Return true if this is a declaration.
    #[inline]
    pub fn is_declaration(&self) -> bool {
        self.declaration
    }

    /// Return true if this is an anonymous type, or defined within an anonymous type.
    pub fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    /// The members of this type.
    #[inline]
    pub fn members(&self) -> &[Member<'input>] {
        &self.members
    }

    /// The variant parts of this type.
    #[inline]
    pub fn variant_parts(&self) -> &[VariantPart<'input>] {
        &self.variant_parts
    }

    /// The inherited types.
    #[inline]
    pub fn inherits(&self) -> &[Inherit] {
        &self.inherits
    }

    /// The layout of members of this type.
    pub fn layout<'me>(&'me self, hash: &FileHash) -> Vec<Layout<'input, 'me>> {
        layout(
            &*self.members,
            &*self.inherits,
            &*self.variant_parts,
            0,
            self.bit_size(),
            hash,
        )
    }

    /// Compare the identifying information of two types.
    ///
    /// Structs are considered equal if their names are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &StructType, b: &StructType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(a.namespace(), a.name(), b.namespace(), b.name())
    }
}

/// A union type.
#[derive(Debug, Default, Clone)]
pub struct UnionType<'input> {
    pub(crate) namespace: Option<Arc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
    pub(crate) source: Source<'input>,
    pub(crate) byte_size: Size,
    pub(crate) declaration: bool,
    pub(crate) members: Vec<Member<'input>>,
}

impl<'input> UnionType<'input> {
    /// The namespace of the type.
    pub fn namespace(&self) -> Option<&Namespace> {
        self.namespace.as_ref().map(|x| &**x)
    }

    /// The name of the type.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The source information for the type.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.source
    }

    /// The size in bytes of an instance of this type.
    #[inline]
    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    /// Return true if this is a declaration.
    #[inline]
    pub fn is_declaration(&self) -> bool {
        self.declaration
    }

    /// Return true if this is an anonymous type, or defined within an anonymous type.
    pub fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    /// The members of this type.
    #[inline]
    pub fn members(&self) -> &[Member<'input>] {
        &self.members
    }

    /// Compare the identifying information of two types.
    ///
    /// Unions are considered equal if their names are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &UnionType, b: &UnionType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(a.namespace(), a.name(), b.namespace(), b.name())
    }
}

/// A variant part.
///
/// A variant part is a discriminant member and list of variants that are
/// selected based on the value of the discriminant member.
#[derive(Debug, Default, Clone)]
pub struct VariantPart<'input> {
    pub(crate) discr: MemberOffset,
    pub(crate) variants: Vec<Variant<'input>>,
}

impl<'input> VariantPart<'input> {
    /// The discriminant member for this variant part.
    ///
    /// The given members should be from the type containing this variant part.
    #[inline]
    pub fn discriminant<'a>(&self, members: &'a [Member<'input>]) -> Option<&'a Member<'input>> {
        for member in members {
            if member.offset == self.discr {
                return Some(member);
            }
        }
        None
    }

    /// The variants for this variant part.
    #[inline]
    pub fn variants(&self) -> &[Variant<'input>] {
        &self.variants
    }

    /// The smallest offset in bits for a variant of this variant part.
    pub fn bit_offset(&self) -> u64 {
        let mut bit_offset = u64::max_value();
        for variant in &self.variants {
            let o = variant.bit_offset();
            if bit_offset > o {
                bit_offset = o;
            }
        }
        if bit_offset < u64::max_value() {
            bit_offset
        } else {
            0
        }
    }

    /// The largest size in bits for the variants of this variant part,
    /// excluding leading and trailing padding.
    pub fn bit_size(&self, hash: &FileHash) -> Option<u64> {
        let start = self.bit_offset();
        let mut end = start;
        for variant in &self.variants {
            let o = variant.bit_offset();
            if let Some(size) = variant.bit_size(hash) {
                if end < o + size {
                    end = o + size;
                }
            } else {
                return None;
            }
        }
        Some(end - start)
    }
}

/// A variant.
///
/// A variant consists of a discriminant value that selects the variant,
/// and a list of members that are valid when the variant is selected.
#[derive(Debug, Default, Clone)]
pub struct Variant<'input> {
    pub(crate) discr_value: Option<u64>,
    pub(crate) name: Option<&'input str>,
    pub(crate) members: Vec<Member<'input>>,
}

impl<'input> Variant<'input> {
    /// The discriminant value which selects this variant.
    ///
    /// The sign of this value depends on the type of the discriminant member.
    #[inline]
    pub fn discriminant_value(&self) -> Option<u64> {
        self.discr_value
    }

    /// The name of the variant.
    ///
    /// Currently this is only set for Rust enums.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The members for this variant.
    #[inline]
    pub fn members(&self) -> &[Member<'input>] {
        &self.members
    }

    /// The smallest offset in bits for a member of this variant.
    pub fn bit_offset(&self) -> u64 {
        let mut bit_offset = u64::max_value();
        for member in &self.members {
            let o = member.bit_offset();
            if bit_offset > o {
                bit_offset = o;
            }
        }
        if bit_offset < u64::max_value() {
            bit_offset
        } else {
            0
        }
    }

    /// The size in bits for the members of this variant, excluding leading and trailing padding.
    pub fn bit_size(&self, hash: &FileHash) -> Option<u64> {
        let start = self.bit_offset();
        let mut end = start;
        for member in &self.members {
            let o = member.bit_offset();
            if let Some(size) = member.bit_size(hash) {
                if end < o + size {
                    end = o + size;
                }
            } else {
                return None;
            }
        }
        Some(end - start)
    }

    /// The layout of members of this variant within a variant part.
    ///
    /// The given bit_offset and bit_size should be for the variant part.
    pub fn layout<'me>(
        &'me self,
        bit_offset: u64,
        bit_size: Option<u64>,
        hash: &FileHash<'input>,
    ) -> Vec<Layout<'input, 'me>> {
        layout(&*self.members, &[], &[], bit_offset, bit_size, hash)
    }

    /// Compare the identifying information of two types.
    ///
    /// Variants are considered equal if the discriminant values are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    // TODO: compare discriminant member too
    pub fn cmp_id(
        _hash_a: &FileHash,
        a: &Variant,
        _hash_b: &FileHash,
        b: &Variant,
    ) -> cmp::Ordering {
        a.discr_value.cmp(&b.discr_value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct MemberOffset(usize);

impl MemberOffset {
    #[inline]
    pub(crate) fn new(offset: usize) -> MemberOffset {
        debug_assert!(MemberOffset(offset) != MemberOffset::none());
        MemberOffset(offset)
    }

    #[inline]
    pub(crate) fn none() -> MemberOffset {
        MemberOffset(usize::MAX)
    }
}

impl Default for MemberOffset {
    #[inline]
    fn default() -> Self {
        MemberOffset::none()
    }
}

/// A member of a struct or union.
#[derive(Debug, Default, Clone)]
pub struct Member<'input> {
    pub(crate) offset: MemberOffset,
    pub(crate) name: Option<&'input str>,
    pub(crate) ty: TypeOffset,
    // Defaults to 0, so always present.
    pub(crate) bit_offset: u64,
    pub(crate) bit_size: Size,
}

impl<'input> Member<'input> {
    /// The name of the member.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The debuginfo offset of the type of this member.
    #[inline]
    pub fn type_offset(&self) -> TypeOffset {
        self.ty
    }

    /// The type of this member.
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The offset in bits of this member.
    #[inline]
    pub fn bit_offset(&self) -> u64 {
        self.bit_offset
    }

    /// The size in bits of this member.
    pub fn bit_size(&self, hash: &FileHash) -> Option<u64> {
        if self.bit_size.is_some() {
            self.bit_size.get()
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash).map(|v| v * 8))
        }
    }

    /// Return true if this member defines an inline type.
    pub fn is_inline(&self, hash: &FileHash) -> bool {
        match self.name() {
            Some(s) => {
                if s.starts_with("RUST$ENCODED$ENUM$") {
                    return true;
                }
            }
            None => return true,
        };
        if let Some(ty) = self.ty(hash) {
            ty.is_anon()
        } else {
            false
        }
    }
}

/// An inherited type of a struct or union.
#[derive(Debug, Default, Clone)]
pub struct Inherit {
    pub(crate) ty: TypeOffset,
    // Defaults to 0, so always present.
    pub(crate) bit_offset: u64,
}

impl Inherit {
    /// The debuginfo offset of the inherited type.
    #[inline]
    pub fn type_offset(&self) -> TypeOffset {
        self.ty
    }

    /// The inherited type.
    pub fn ty<'a, 'input>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The offset in bits of the inherited type within the struct.
    #[inline]
    pub fn bit_offset(&self) -> u64 {
        self.bit_offset
    }

    /// The size in bits of the inherited type.
    pub fn bit_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash).map(|v| v * 8))
    }
}

/// The layout of an item (member or padding) within a struct.
#[derive(Debug, Clone)]
pub struct Layout<'input, 'item>
where
    'input: 'item,
{
    /// The offset in bits of the item within the struct.
    pub bit_offset: u64,
    /// The size in bits of the item.
    pub bit_size: Size,
    /// The member or padding.
    pub item: LayoutItem<'input, 'item>,
}

/// The item in a `Layout`.
#[derive(Debug, Clone)]
pub enum LayoutItem<'input, 'item> {
    /// Padding.
    Padding,
    /// A member.
    Member(&'item Member<'input>),
    /// A variant part.
    VariantPart(&'item VariantPart<'input>),
    /// An inherited type.
    Inherit(&'item Inherit),
}

fn layout<'input, 'item>(
    members: &'item [Member<'input>],
    inherits: &'item [Inherit],
    variant_parts: &'item [VariantPart<'input>],
    base_bit_offset: u64,
    bit_size: Option<u64>,
    hash: &FileHash,
) -> Vec<Layout<'input, 'item>> {
    let mut members: Vec<_> = members
        .iter()
        .map(|member| Layout {
            bit_offset: member.bit_offset() - base_bit_offset,
            bit_size: member.bit_size(hash).into(),
            item: LayoutItem::Member(member),
        })
        .collect();
    members.extend(inherits.iter().map(|inherit| Layout {
        bit_offset: inherit.bit_offset() - base_bit_offset,
        bit_size: inherit.bit_size(hash).into(),
        item: LayoutItem::Inherit(inherit),
    }));
    members.extend(variant_parts.iter().map(|variant_part| Layout {
        bit_offset: variant_part.bit_offset() - base_bit_offset,
        bit_size: variant_part.bit_size(hash).into(),
        item: LayoutItem::VariantPart(variant_part),
    }));
    members.sort_by(|a, b| {
        a.bit_offset
            .cmp(&b.bit_offset)
            .then_with(|| a.bit_size.cmp(&b.bit_size))
    });

    let mut next_bit_offset = bit_size;
    let mut layout = Vec::new();
    for member in members.into_iter().rev() {
        if let (Some(bit_size), Some(next_bit_offset)) = (member.bit_size.get(), next_bit_offset) {
            let bit_offset = member.bit_offset + bit_size;
            if next_bit_offset > bit_offset {
                let bit_size = next_bit_offset - bit_offset;
                layout.push(Layout {
                    bit_offset,
                    bit_size: Size::new(bit_size),
                    item: LayoutItem::Padding,
                });
            }
        }
        next_bit_offset = Some(member.bit_offset);
        layout.push(member);
    }
    if let Some(first_bit_offset) = layout.last().map(|x| x.bit_offset) {
        if first_bit_offset > 0 {
            layout.push(Layout {
                bit_offset: 0,
                bit_size: Size::new(first_bit_offset),
                item: LayoutItem::Padding,
            });
        }
    }
    layout.reverse();
    layout
}

/// An enumeration type.
#[derive(Debug, Default, Clone)]
pub struct EnumerationType<'input> {
    pub(crate) offset: TypeOffset,
    pub(crate) namespace: Option<Arc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
    pub(crate) source: Source<'input>,
    pub(crate) declaration: bool,
    pub(crate) ty: TypeOffset,
    pub(crate) byte_size: Size,
}

impl<'input> EnumerationType<'input> {
    /// The namespace of the type.
    pub fn namespace(&self) -> Option<&Namespace> {
        self.namespace.as_ref().map(|x| &**x)
    }

    /// The name of the type.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The source information for the type.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.source
    }

    /// Return true if this is a declaration.
    #[inline]
    pub fn is_declaration(&self) -> bool {
        self.declaration
    }

    /// The underlying type of the enumeration.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The size in bytes of an instance of this type.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size.get()
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash))
        }
    }

    /// The enumerators of this type.
    pub fn enumerators(&self, hash: &FileHash<'input>) -> Vec<Enumerator<'input>> {
        hash.file.get_enumerators(self.offset)
    }

    /// Compare the identifying information of two types.
    ///
    /// Enumerations are considered equal if their names are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &EnumerationType, b: &EnumerationType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(a.namespace(), a.name(), b.namespace(), b.name())
    }
}

/// A member of an enumeration.
#[derive(Debug, Default, Clone)]
pub struct Enumerator<'input> {
    pub(crate) name: Option<&'input str>,
    pub(crate) value: Option<i64>,
}

impl<'input> Enumerator<'input> {
    /// The name of the enumerator.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The value of the enumerator.
    #[inline]
    pub fn value(&self) -> Option<i64> {
        self.value
    }
}

/// A type for an array of elements.
#[derive(Debug, Default, Clone)]
pub struct ArrayType<'input> {
    pub(crate) ty: TypeOffset,
    pub(crate) count: Size,
    pub(crate) byte_size: Size,
    pub(crate) phantom: marker::PhantomData<&'input str>,
}

impl<'input> ArrayType<'input> {
    /// The type of the elements in the array.
    pub fn element_type<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The size in bytes of an instance of this type.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size.get()
        } else if let (Some(ty), Some(count)) = (self.element_type(hash), self.count.get()) {
            ty.byte_size(hash).map(|v| v * count)
        } else {
            None
        }
    }

    /// The number of elements in the array.
    pub fn count(&self, hash: &FileHash) -> Option<u64> {
        if self.count.is_some() {
            self.count.get()
        } else if let (Some(ty), Some(byte_size)) = (self.element_type(hash), self.byte_size.get())
        {
            ty.byte_size(hash).map(|v| byte_size / v)
        } else {
            None
        }
    }

    /// Compare the identifying information of two types.
    ///
    /// Array types are considered equal if the element identifiers and counts are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &ArrayType,
        hash_b: &FileHash,
        b: &ArrayType,
    ) -> cmp::Ordering {
        match (a.element_type(hash_a), b.element_type(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => {
                let ord = Type::cmp_id(hash_a, ty_a, hash_b, ty_b);
                if ord != cmp::Ordering::Equal {
                    return ord;
                }
            }
            (Some(_), None) => {
                return cmp::Ordering::Less;
            }
            (None, Some(_)) => {
                return cmp::Ordering::Greater;
            }
            (None, None) => {}
        }
        a.count.cmp(&b.count)
    }
}

/// A subrange of another type.
#[derive(Debug, Default, Clone)]
pub struct SubrangeType<'input> {
    pub(crate) name: Option<&'input str>,
    pub(crate) ty: TypeOffset,
    pub(crate) lower: Option<u64>,
    pub(crate) upper: Option<u64>,
    pub(crate) byte_size: Size,
}

impl<'input> SubrangeType<'input> {
    /// The name of the subrange.
    #[inline]
    pub fn name(&self) -> Option<&'input str> {
        self.name
    }

    /// The underlying type of the subrange.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The lower bound of the subrange (inclusive).
    #[inline]
    pub fn lower(&self) -> Option<u64> {
        self.lower
    }

    /// The upper bound of the subrange (inclusive).
    #[inline]
    pub fn upper(&self) -> Option<u64> {
        self.upper
    }

    /// The size in bytes of an instance of this type.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size.get()
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash))
        }
    }

    /// Compare the identifying information of two types.
    ///
    /// Subrange types are considered equal if the underlying type and bounds are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &SubrangeType,
        hash_b: &FileHash,
        b: &SubrangeType,
    ) -> cmp::Ordering {
        match (a.ty(hash_a), b.ty(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => {
                let ord = Type::cmp_id(hash_a, ty_a, hash_b, ty_b);
                if ord != cmp::Ordering::Equal {
                    return ord;
                }
            }
            (Some(_), None) => {
                return cmp::Ordering::Less;
            }
            (None, Some(_)) => {
                return cmp::Ordering::Greater;
            }
            (None, None) => {}
        }
        a.lower.cmp(&b.lower).then_with(|| a.upper.cmp(&b.upper))
    }
}

/// A function type.
#[derive(Debug, Default, Clone)]
pub struct FunctionType<'input> {
    pub(crate) parameters: Vec<ParameterType<'input>>,
    pub(crate) return_type: TypeOffset,
    pub(crate) byte_size: Size,
}

impl<'input> FunctionType<'input> {
    /// The parameters of the function.
    #[inline]
    pub fn parameters(&self) -> &[ParameterType<'input>] {
        &self.parameters
    }

    /// The return type of the function.
    #[inline]
    pub fn return_type<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.return_type)
    }

    /// The size in bytes of an instance of this type.
    #[inline]
    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    /// Compare the identifying information of two types.
    ///
    /// Function types are considered equal if they have the same parameter types and
    /// return types. Parameter names are ignored.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &FunctionType,
        hash_b: &FileHash,
        b: &FunctionType,
    ) -> cmp::Ordering {
        for (parameter_a, parameter_b) in a.parameters.iter().zip(b.parameters.iter()) {
            let ord = ParameterType::cmp_id(hash_a, parameter_a, hash_b, parameter_b);
            if ord != cmp::Ordering::Equal {
                return ord;
            }
        }

        let ord = a.parameters.len().cmp(&b.parameters.len());
        if ord != cmp::Ordering::Equal {
            return ord;
        }

        match (a.return_type(hash_a), b.return_type(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => {
                let ord = Type::cmp_id(hash_a, ty_a, hash_b, ty_b);
                if ord != cmp::Ordering::Equal {
                    return ord;
                }
            }
            (Some(_), None) => {
                return cmp::Ordering::Less;
            }
            (None, Some(_)) => {
                return cmp::Ordering::Greater;
            }
            (None, None) => {}
        }

        cmp::Ordering::Equal
    }
}

/// The type of a function parameter.
#[derive(Debug, Default, Clone)]
pub struct ParameterType<'input> {
    pub(crate) offset: ParameterOffset,
    pub(crate) name: Option<&'input str>,
    pub(crate) ty: TypeOffset,
}

impl<'input> ParameterType<'input> {
    /// The name of the parameter.
    #[inline]
    pub fn name(&self) -> Option<&'input str> {
        self.name
    }

    /// The type of the parameter.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// Compare the identifying information of two types.
    ///
    /// Parameters are considered equal if they have the same types.
    /// Parameter names are ignored.
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &ParameterType,
        hash_b: &FileHash,
        b: &ParameterType,
    ) -> cmp::Ordering {
        match (a.ty(hash_a), b.ty(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => Type::cmp_id(hash_a, ty_a, hash_b, ty_b),
            (Some(_), None) => cmp::Ordering::Less,
            (None, Some(_)) => cmp::Ordering::Greater,
            (None, None) => cmp::Ordering::Equal,
        }
    }
}

/// An unspecified type.
#[derive(Debug, Default, Clone)]
pub struct UnspecifiedType<'input> {
    pub(crate) namespace: Option<Arc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
}

impl<'input> UnspecifiedType<'input> {
    /// The namespace of the type.
    pub fn namespace(&self) -> Option<&Namespace> {
        self.namespace.as_ref().map(|x| &**x)
    }

    /// The name of the type.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// Compare the identifying information of two types.
    ///
    /// Unspecified types are considered equal if they have the same name.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &UnspecifiedType, b: &UnspecifiedType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(a.namespace(), a.name(), b.namespace(), b.name())
    }
}

/// A type for a pointer to a member of a containing type.
#[derive(Debug, Default, Clone)]
pub struct PointerToMemberType {
    pub(crate) ty: TypeOffset,
    pub(crate) containing_ty: TypeOffset,
    pub(crate) byte_size: Size,
    // TODO: hack
    pub(crate) address_size: Option<u64>,
}

impl PointerToMemberType {
    /// The type of the member.
    #[inline]
    pub fn member_type<'a, 'input>(
        &self,
        hash: &'a FileHash<'input>,
    ) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The containing type.
    #[inline]
    pub fn containing_type<'a, 'input>(
        &self,
        hash: &'a FileHash<'input>,
    ) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.containing_ty)
    }

    /// The size in bytes of an instance of this type.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            return self.byte_size.get();
        }
        // TODO: this probably depends on the ABI
        self.member_type(hash).and_then(|ty| {
            if ty.is_function(hash) {
                self.address_size.map(|v| v * 2)
            } else {
                self.address_size
            }
        })
    }

    /// Compare the identifying information of two types.
    ///
    /// Pointer to member types are considered equal if both the member type and containing
    /// type are equal.
    ///
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &PointerToMemberType,
        hash_b: &FileHash,
        b: &PointerToMemberType,
    ) -> cmp::Ordering {
        match (a.containing_type(hash_a), b.containing_type(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => {
                let ord = Type::cmp_id(hash_a, ty_a, hash_b, ty_b);
                if ord != cmp::Ordering::Equal {
                    return ord;
                }
            }
            (Some(_), None) => {
                return cmp::Ordering::Less;
            }
            (None, Some(_)) => {
                return cmp::Ordering::Greater;
            }
            (None, None) => {}
        }
        match (a.member_type(hash_a), b.member_type(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => {
                let ord = Type::cmp_id(hash_a, ty_a, hash_b, ty_b);
                if ord != cmp::Ordering::Equal {
                    return ord;
                }
            }
            (Some(_), None) => {
                return cmp::Ordering::Less;
            }
            (None, Some(_)) => {
                return cmp::Ordering::Greater;
            }
            (None, None) => {}
        }
        cmp::Ordering::Equal
    }
}
