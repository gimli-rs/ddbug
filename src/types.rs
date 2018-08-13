use std::borrow::Cow;
use std::cell::Cell;
use std::cmp;
use std::marker;
use std::rc::Rc;
use std::usize;

use file::FileHash;
use function::Parameter;
use namespace::Namespace;
use source::Source;
use Size;

#[derive(Debug, Clone)]
pub(crate) enum TypeKind<'input> {
    Base(BaseType<'input>),
    Def(TypeDef<'input>),
    Struct(StructType<'input>),
    Union(UnionType<'input>),
    Enumeration(EnumerationType<'input>),
    Array(ArrayType<'input>),
    Function(FunctionType<'input>),
    Unspecified(UnspecifiedType<'input>),
    PointerToMember(PointerToMemberType),
    Modifier(TypeModifier<'input>),
}

impl<'input> TypeKind<'input> {
    fn discriminant_value(&self) -> u8 {
        match *self {
            TypeKind::Base(..) => 0,
            TypeKind::Def(..) => 1,
            TypeKind::Struct(..) => 2,
            TypeKind::Union(..) => 3,
            TypeKind::Enumeration(..) => 4,
            TypeKind::Array(..) => 5,
            TypeKind::Function(..) => 6,
            TypeKind::Unspecified(..) => 7,
            TypeKind::PointerToMember(..) => 8,
            TypeKind::Modifier(..) => 9,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TypeOffset(usize);

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

    #[inline]
    pub(crate) fn is_none(self) -> bool {
        self == Self::none()
    }

    #[inline]
    pub(crate) fn is_some(self) -> bool {
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

#[derive(Debug, Clone)]
pub(crate) struct Type<'input> {
    pub id: Cell<usize>,
    pub offset: TypeOffset,
    pub kind: TypeKind<'input>,
}

impl<'input> Default for Type<'input> {
    fn default() -> Self {
        Type {
            id: Cell::new(0),
            offset: TypeOffset::none(),
            kind: TypeKind::Base(BaseType::default()),
        }
    }
}

impl<'input> Type<'input> {
    pub fn from_offset<'a>(
        hash: &'a FileHash<'input>,
        offset: TypeOffset,
    ) -> Option<Cow<'a, Type<'input>>> {
        if offset.is_none() {
            return None;
        }
        hash.types
            .get(&offset)
            .map(|ty| Cow::Borrowed(*ty))
            .or_else(|| hash.file.get_type(offset).map(Cow::Owned))
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        match self.kind {
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
        }
    }

    pub fn is_anon(&self) -> bool {
        match self.kind {
            TypeKind::Struct(ref val) => val.is_anon(),
            TypeKind::Union(ref val) => val.is_anon(),
            TypeKind::Base(..)
            | TypeKind::Def(..)
            | TypeKind::Enumeration(..)
            | TypeKind::Array(..)
            | TypeKind::Function(..)
            | TypeKind::Unspecified(..)
            | TypeKind::PointerToMember(..)
            | TypeKind::Modifier(..) => false,
        }
    }

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
            TypeKind::Struct(..)
            | TypeKind::Union(..)
            | TypeKind::Base(..)
            | TypeKind::Enumeration(..)
            | TypeKind::Array(..)
            | TypeKind::Unspecified(..)
            | TypeKind::PointerToMember(..) => false,
        }
    }

    pub fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        match self.kind {
            TypeKind::Struct(ref val) => val.visit_members(f),
            TypeKind::Union(ref val) => val.visit_members(f),
            TypeKind::Enumeration(..)
            | TypeKind::Def(..)
            | TypeKind::Base(..)
            | TypeKind::Array(..)
            | TypeKind::Function(..)
            | TypeKind::Unspecified(..)
            | TypeKind::PointerToMember(..)
            | TypeKind::Modifier(..) => {}
        }
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    /// This must only be called for types that have identifiers.
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
            _ => {
                let discr_a = type_a.kind.discriminant_value();
                let discr_b = type_b.kind.discriminant_value();
                debug_assert_ne!(discr_a, discr_b);
                discr_a.cmp(&discr_b)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct TypeModifier<'input> {
    pub kind: TypeModifierKind,
    pub ty: TypeOffset,
    pub name: Option<&'input str>,
    pub byte_size: Size,
    // TODO: hack
    pub address_size: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum TypeModifierKind {
    Pointer,
    Reference,
    Const,
    Packed,
    Volatile,
    Restrict,
    Shared,
    RvalueReference,
    Atomic,
    // TODO:
    // Immutable,
    // PDB is disabled
    #[allow(dead_code)]
    Other,
}

impl TypeModifierKind {
    fn discriminant_value(&self) -> u8 {
        match *self {
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
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            return self.byte_size.get();
        }
        match self.kind {
            TypeModifierKind::Const
            | TypeModifierKind::Packed
            | TypeModifierKind::Volatile
            | TypeModifierKind::Restrict
            | TypeModifierKind::Shared
            | TypeModifierKind::Atomic
            | TypeModifierKind::Other => self.ty(hash).and_then(|v| v.byte_size(hash)),
            TypeModifierKind::Pointer
            | TypeModifierKind::Reference
            | TypeModifierKind::RvalueReference => self.address_size,
        }
    }

    /// Compare the identifying information of two types.
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

#[derive(Debug, Default, Clone)]
pub(crate) struct BaseType<'input> {
    pub name: Option<&'input str>,
    pub byte_size: Size,
}

impl<'input> BaseType<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &BaseType, b: &BaseType) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct TypeDef<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
    pub ty: TypeOffset,
    pub source: Source<'input>,
}

impl<'input> TypeDef<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash))
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &TypeDef, b: &TypeDef) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name(), &b.namespace, b.name())
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct StructType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
    pub source: Source<'input>,
    pub byte_size: Size,
    pub declaration: bool,
    pub members: Vec<Member<'input>>,
}

impl<'input> StructType<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    pub fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    pub fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &StructType, b: &StructType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name(), &b.namespace, b.name())
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct UnionType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
    pub source: Source<'input>,
    pub byte_size: Size,
    pub declaration: bool,
    pub members: Vec<Member<'input>>,
}

impl<'input> UnionType<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    pub fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    pub fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &UnionType, b: &UnionType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name(), &b.namespace, b.name())
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct Member<'input> {
    pub name: Option<&'input str>,
    pub ty: TypeOffset,
    // Defaults to 0, so always present.
    pub bit_offset: u64,
    pub bit_size: Size,
    // Redundant, but simplifies code.
    pub next_bit_offset: Size,
}

impl<'input> Member<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    pub fn bit_size(&self, hash: &FileHash) -> Option<u64> {
        if self.bit_size.is_some() {
            self.bit_size.get()
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash).map(|v| v * 8))
        }
    }

    pub fn is_inline(&self, hash: &FileHash) -> bool {
        match self.name() {
            Some(s) => if s.starts_with("RUST$ENCODED$ENUM$") {
                return true;
            },
            None => return true,
        };
        if let Some(ty) = self.ty(hash) {
            ty.is_anon()
        } else {
            false
        }
    }

    pub fn padding(&self, bit_size: Option<u64>) -> Option<Padding> {
        if let (Some(bit_size), Some(next_bit_offset)) = (bit_size, self.next_bit_offset.get()) {
            let bit_offset = self.bit_offset + bit_size;
            if next_bit_offset > bit_offset {
                let bit_size = next_bit_offset - bit_offset;
                return Some(Padding {
                    bit_offset,
                    bit_size,
                });
            }
        }
        None
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Padding {
    pub bit_offset: u64,
    pub bit_size: u64,
}

#[derive(Debug, Default, Clone)]
pub(crate) struct EnumerationType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
    pub source: Source<'input>,
    pub declaration: bool,
    pub ty: TypeOffset,
    pub byte_size: Size,
}

impl<'input> EnumerationType<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size.get()
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash))
        }
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &EnumerationType, b: &EnumerationType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name(), &b.namespace, b.name())
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct Enumerator<'input> {
    pub name: Option<&'input str>,
    pub value: Option<i64>,
}

impl<'input> Enumerator<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct ArrayType<'input> {
    pub ty: TypeOffset,
    pub count: Size,
    pub byte_size: Size,
    pub phantom: marker::PhantomData<&'input str>,
}

impl<'input> ArrayType<'input> {
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size.get()
        } else if let (Some(ty), Some(count)) = (self.ty(hash), self.count.get()) {
            ty.byte_size(hash).map(|v| v * count)
        } else {
            None
        }
    }

    pub fn count(&self, hash: &FileHash) -> Option<u64> {
        if self.count.is_some() {
            self.count.get()
        } else if let (Some(ty), Some(byte_size)) = (self.ty(hash), self.byte_size.get()) {
            ty.byte_size(hash).map(|v| byte_size / v)
        } else {
            None
        }
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &ArrayType,
        hash_b: &FileHash,
        b: &ArrayType,
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
        a.count.cmp(&b.count)
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct FunctionType<'input> {
    pub parameters: Vec<Parameter<'input>>,
    pub return_type: TypeOffset,
    pub byte_size: Size,
}

impl<'input> FunctionType<'input> {
    pub fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    pub fn return_type<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.return_type)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &FunctionType,
        hash_b: &FileHash,
        b: &FunctionType,
    ) -> cmp::Ordering {
        for (parameter_a, parameter_b) in a.parameters.iter().zip(b.parameters.iter()) {
            let ord = Parameter::cmp_type(hash_a, parameter_a, hash_b, parameter_b);
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

#[derive(Debug, Default, Clone)]
pub(crate) struct UnspecifiedType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
}

impl<'input> UnspecifiedType<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(a: &UnspecifiedType, b: &UnspecifiedType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name(), &b.namespace, b.name())
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct PointerToMemberType {
    pub ty: TypeOffset,
    pub containing_ty: TypeOffset,
    pub byte_size: Size,
    // TODO: hack
    pub address_size: Option<u64>,
}

impl PointerToMemberType {
    pub fn ty<'a, 'input>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    pub fn containing_ty<'a, 'input>(
        &self,
        hash: &'a FileHash<'input>,
    ) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.containing_ty)
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            return self.byte_size.get();
        }
        // TODO: this probably depends on the ABI
        self.ty(hash).and_then(|ty| {
            if ty.is_function(hash) {
                self.address_size.map(|v| v * 2)
            } else {
                self.address_size
            }
        })
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        hash_a: &FileHash,
        a: &PointerToMemberType,
        hash_b: &FileHash,
        b: &PointerToMemberType,
    ) -> cmp::Ordering {
        match (a.containing_ty(hash_a), b.containing_ty(hash_b)) {
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
        cmp::Ordering::Equal
    }
}
