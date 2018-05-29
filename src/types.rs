use std::borrow::Cow;
use std::cell::Cell;
use std::cmp;
use std::marker;
use std::ops::Deref;
use std::rc::Rc;
use std::usize;

use file::FileHash;
use function::Parameter;
use namespace::Namespace;
use print::{DiffList, DiffState, Print, PrintState, SortList, ValuePrinter};
use source::Source;
use unit::Unit;
use {Options, Result, Size, Sort};

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
            .or_else(|| hash.file.type_from_offset(offset).map(Cow::Owned))
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

    pub fn print(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        let id = self.id.get();
        match self.kind {
            TypeKind::Def(ref val) => val.print(state, unit, id),
            TypeKind::Struct(ref val) => val.print(state, unit, id),
            TypeKind::Union(ref val) => val.print(state, unit, id),
            TypeKind::Enumeration(ref val) => val.print(state, unit, id),
            TypeKind::Base(..)
            | TypeKind::Array(..)
            | TypeKind::Function(..)
            | TypeKind::Unspecified(..)
            | TypeKind::PointerToMember(..)
            | TypeKind::Modifier(..) => Err(format!("can't print {:?}", self).into()),
        }
    }

    pub fn print_ref(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        let id = self.id.get();
        match self.kind {
            TypeKind::Base(ref val) => val.print_ref(w),
            TypeKind::Def(ref val) => val.print_ref(w, id),
            TypeKind::Struct(ref val) => val.print_ref(w, id),
            TypeKind::Union(ref val) => val.print_ref(w, id),
            TypeKind::Enumeration(ref val) => val.print_ref(w, id),
            TypeKind::Array(ref val) => val.print_ref(w, hash),
            TypeKind::Function(ref val) => val.print_ref(w, hash),
            TypeKind::Unspecified(ref val) => val.print_ref(w),
            TypeKind::PointerToMember(ref val) => val.print_ref(w, hash),
            TypeKind::Modifier(ref val) => val.print_ref(w, hash),
        }
    }

    pub fn print_ref_from_offset(
        w: &mut ValuePrinter,
        hash: &FileHash,
        offset: TypeOffset,
    ) -> Result<()> {
        if offset.is_none() {
            write!(w, "void")?;
        } else {
            match Type::from_offset(hash, offset) {
                Some(ty) => ty.print_ref(w, hash)?,
                None => write!(w, "<invalid-type {}>", offset.0)?,
            }
        }
        Ok(())
    }

    pub fn diff(
        state: &mut DiffState,
        unit_a: &Unit,
        type_a: &Type,
        unit_b: &Unit,
        type_b: &Type,
    ) -> Result<()> {
        use self::TypeKind::*;
        let id = type_a.id.get();
        match (&type_a.kind, &type_b.kind) {
            (&Def(ref a), &Def(ref b)) => TypeDef::diff(state, id, unit_a, a, unit_b, b),
            (&Struct(ref a), &Struct(ref b)) => StructType::diff(state, id, unit_a, a, unit_b, b),
            (&Union(ref a), &Union(ref b)) => UnionType::diff(state, id, unit_a, a, unit_b, b),
            (&Enumeration(ref a), &Enumeration(ref b)) => {
                EnumerationType::diff(state, id, unit_a, a, unit_b, b)
            }
            _ => Err(format!("can't diff {:?}, {:?}", type_a, type_b).into()),
        }?;
        Ok(())
    }

    fn print_members(state: &mut PrintState, unit: &Unit, ty: Option<&Type>) -> Result<()> {
        if let Some(ty) = ty {
            match ty.kind {
                TypeKind::Struct(ref t) => return t.print_members(state, unit),
                TypeKind::Union(ref t) => return t.print_members(state, unit),
                _ => return Err(format!("can't print members {:?}", ty).into()),
            }
        }
        Ok(())
    }

    fn diff_members(
        state: &mut DiffState,
        unit_a: &Unit,
        type_a: Option<&Type>,
        unit_b: &Unit,
        type_b: Option<&Type>,
    ) -> Result<()> {
        if let (Some(type_a), Some(type_b)) = (type_a, type_b) {
            match (&type_a.kind, &type_b.kind) {
                (&TypeKind::Struct(ref a), &TypeKind::Struct(ref b)) => {
                    return StructType::diff_members(state, unit_a, a, unit_b, b);
                }
                (&TypeKind::Union(ref a), &TypeKind::Union(ref b)) => {
                    return UnionType::diff_members(state, unit_a, a, unit_b, b);
                }
                _ => {}
            }
        }

        // Different types, so don't try to diff the members.
        state.block((unit_a, type_a), (unit_b, type_b), |state, (unit, x)| {
            Type::print_members(state, unit, x)
        })
    }

    pub fn filter(&self, options: &Options) -> bool {
        match self.kind {
            TypeKind::Def(ref val) => val.filter(options),
            TypeKind::Struct(ref val) => val.filter(options),
            TypeKind::Union(ref val) => val.filter(options),
            TypeKind::Enumeration(ref val) => val.filter(options),
            TypeKind::Unspecified(ref val) => val.filter(options),
            TypeKind::Base(..)
            | TypeKind::Array(..)
            | TypeKind::Function(..)
            | TypeKind::PointerToMember(..)
            | TypeKind::Modifier(..) => options.filter_name.is_none(),
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

impl<'input> Print for Type<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, unit: &Self::Arg) -> Result<()> {
        self.print(state, unit)
    }

    fn diff(
        state: &mut DiffState,
        unit_a: &Self::Arg,
        a: &Self,
        unit_b: &Self::Arg,
        b: &Self,
    ) -> Result<()> {
        Self::diff(state, unit_a, a, unit_b, b)
    }
}

impl<'input> SortList for Type<'input> {
    /// This must only be called for types that have identifiers.
    fn cmp_id(
        hash_a: &FileHash,
        type_a: &Type,
        hash_b: &FileHash,
        type_b: &Type,
        _options: &Options,
    ) -> cmp::Ordering {
        Type::cmp_id(hash_a, type_a, hash_b, type_b)
    }

    fn cmp_by(
        hash_a: &FileHash,
        a: &Self,
        hash_b: &FileHash,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        match options.sort {
            Sort::None => a.offset.0.cmp(&b.offset.0),
            Sort::Name => Type::cmp_id(hash_a, a, hash_b, b),
            Sort::Size => a.byte_size(hash_a).cmp(&b.byte_size(hash_b)),
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
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
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

    fn print_ref(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        if let Some(name) = self.name() {
            write!(w, "{}", name)?;
        } else {
            match self.kind {
                TypeModifierKind::Pointer => write!(w, "* ")?,
                TypeModifierKind::Reference | TypeModifierKind::RvalueReference => write!(w, "& ")?,
                TypeModifierKind::Const => write!(w, "const ")?,
                TypeModifierKind::Volatile => write!(w, "volatile ")?,
                TypeModifierKind::Restrict => write!(w, "restrict ")?,
                TypeModifierKind::Packed
                | TypeModifierKind::Shared
                | TypeModifierKind::Atomic
                | TypeModifierKind::Other => {}
            }
            Type::print_ref_from_offset(w, hash, self.ty)?;
        }
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(
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
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    fn print_ref(&self, w: &mut ValuePrinter) -> Result<()> {
        write!(w, "{}", self.name().unwrap_or("<anon-base-type>"))?;
        Ok(())
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
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash))
    }

    fn print_name(&self, w: &mut ValuePrinter) -> Result<()> {
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        write!(w, "{}", self.name().unwrap_or("<anon-typedef>"))?;
        Ok(())
    }

    fn print_ref(&self, w: &mut ValuePrinter, id: usize) -> Result<()> {
        w.link(id, &mut |w| self.print_name(w))
    }

    fn print_def(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        write!(w, "type ")?;
        self.print_name(w)?;
        write!(w, " = ")?;
        Type::print_ref_from_offset(w, hash, self.ty)?;
        Ok(())
    }

    fn print_source(&self, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
        if self.source.is_some() {
            self.source.print(w, unit)?;
        }
        Ok(())
    }

    fn print_byte_size(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        if let Some(byte_size) = self.byte_size(hash) {
            write!(w, "{}", byte_size)?;
        }
        Ok(())
    }

    fn print(&self, state: &mut PrintState, unit: &Unit, id: usize) -> Result<()> {
        let ty = self.ty(state.hash());
        state.collapsed(
            |state| state.id(id, |w, state| self.print_def(w, state)),
            |state| {
                if state.options().print_source {
                    state.field("source", |w, _state| self.print_source(w, unit))?;
                }
                state.field("size", |w, state| self.print_byte_size(w, state))?;
                if let Some(ref ty) = ty {
                    if ty.is_anon() {
                        state.field_expanded("members", |state| {
                            Type::print_members(state, unit, Some(ty))
                        })?;
                    }
                }
                Ok(())
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn diff(
        state: &mut DiffState,
        id: usize,
        unit_a: &Unit,
        a: &TypeDef,
        unit_b: &Unit,
        b: &TypeDef,
    ) -> Result<()> {
        state.collapsed(
            |state| state.id(id, a, b, |w, state, x| x.print_def(w, state)),
            |state| {
                if state.options().print_source {
                    state.field(
                        "source",
                        (unit_a, a),
                        (unit_b, b),
                        |w, _state, (unit, x)| x.print_source(w, unit),
                    )?;
                }
                state.field("size", a, b, |w, state, x| x.print_byte_size(w, state))?;
                let ty_a = filter_option(a.ty(state.hash_a()), |ty| ty.is_anon());
                let ty_a = ty_a.as_ref().map(Cow::deref);
                let ty_b = filter_option(b.ty(state.hash_b()), |ty| ty.is_anon());
                let ty_b = ty_b.as_ref().map(Cow::deref);
                state.field_expanded("members", |state| {
                    Type::diff_members(state, unit_a, ty_a, unit_b, ty_b)
                })
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name()) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &TypeDef, b: &TypeDef) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name(), &b.namespace, b.name())
    }
}

fn filter_option<T, F>(o: Option<T>, f: F) -> Option<T>
where
    F: FnOnce(&T) -> bool,
{
    o.and_then(|v| if f(&v) { Some(v) } else { None })
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

    fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    fn print_name(&self, w: &mut ValuePrinter) -> Result<()> {
        write!(w, "struct ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        write!(w, "{}", self.name().unwrap_or("<anon>"))?;
        Ok(())
    }

    fn print_ref(&self, w: &mut ValuePrinter, id: usize) -> Result<()> {
        w.link(id, &mut |w| self.print_name(w))
    }

    fn print(&self, state: &mut PrintState, unit: &Unit, id: usize) -> Result<()> {
        state.collapsed(
            |state| state.id(id, |w, _state| self.print_name(w)),
            |state| {
                if state.options().print_source {
                    state.field("source", |w, _state| self.print_source(w, unit))?;
                }
                state.field("declaration", |w, state| self.print_declaration(w, state))?;
                state.field("size", |w, state| self.print_byte_size(w, state))?;
                state.field_expanded("members", |state| self.print_members(state, unit))
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn diff(
        state: &mut DiffState,
        id: usize,
        unit_a: &Unit,
        a: &StructType,
        unit_b: &Unit,
        b: &StructType,
    ) -> Result<()> {
        // The names should be the same, but we can't be sure.
        state.collapsed(
            |state| state.id(id, a, b, |w, _state, x| x.print_name(w)),
            |state| {
                if state.options().print_source {
                    state.field(
                        "source",
                        (unit_a, a),
                        (unit_b, b),
                        |w, _state, (unit, x)| x.print_source(w, unit),
                    )?;
                }
                state.field("declaration", a, b, |w, state, x| {
                    x.print_declaration(w, state)
                })?;
                state.field("size", a, b, |w, state, x| x.print_byte_size(w, state))?;
                state.field_expanded("members", |state| {
                    Self::diff_members(state, unit_a, a, unit_b, b)
                })
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn print_source(&self, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
        if self.source.is_some() {
            self.source.print(w, unit)?;
        }
        Ok(())
    }

    fn print_byte_size(&self, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
        if let Some(size) = self.byte_size() {
            write!(w, "{}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
        if self.declaration {
            write!(w, "yes")?;
        }
        Ok(())
    }

    fn print_members(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.list(unit, &self.members)
    }

    fn diff_members(
        state: &mut DiffState,
        unit_a: &Unit,
        a: &StructType,
        unit_b: &Unit,
        b: &StructType,
    ) -> Result<()> {
        state.list(unit_a, &a.members, unit_b, &b.members)
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name()) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &StructType, b: &StructType) -> cmp::Ordering {
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
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    fn print_name(&self, w: &mut ValuePrinter) -> Result<()> {
        write!(w, "union ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        write!(w, "{}", self.name().unwrap_or("<anon>"))?;
        Ok(())
    }

    fn print_ref(&self, w: &mut ValuePrinter, id: usize) -> Result<()> {
        w.link(id, &mut |w| self.print_name(w))
    }

    fn print(&self, state: &mut PrintState, unit: &Unit, id: usize) -> Result<()> {
        state.collapsed(
            |state| state.id(id, |w, _state| self.print_name(w)),
            |state| {
                if state.options().print_source {
                    state.field("source", |w, _state| self.print_source(w, unit))?;
                }
                state.field("declaration", |w, state| self.print_declaration(w, state))?;
                state.field("size", |w, state| self.print_byte_size(w, state))?;
                state.field_expanded("members", |state| self.print_members(state, unit))
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn diff(
        state: &mut DiffState,
        id: usize,
        unit_a: &Unit,
        a: &UnionType,
        unit_b: &Unit,
        b: &UnionType,
    ) -> Result<()> {
        // The names should be the same, but we can't be sure.
        state.collapsed(
            |state| state.id(id, a, b, |w, _state, x| x.print_name(w)),
            |state| {
                if state.options().print_source {
                    state.field(
                        "source",
                        (unit_a, a),
                        (unit_b, b),
                        |w, _state, (unit, x)| x.print_source(w, unit),
                    )?;
                }
                state.field("declaration", a, b, |w, state, x| {
                    x.print_declaration(w, state)
                })?;
                state.field("size", a, b, |w, state, x| x.print_byte_size(w, state))?;
                state.field_expanded("members", |state| {
                    Self::diff_members(state, unit_a, a, unit_b, b)
                })
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn print_source(&self, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
        if self.source.is_some() {
            self.source.print(w, unit)?;
        }
        Ok(())
    }

    fn print_byte_size(&self, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
        if let Some(size) = self.byte_size() {
            write!(w, "{}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
        if self.declaration {
            write!(w, "yes")?;
        }
        Ok(())
    }

    fn print_members(&self, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.list(unit, &self.members)
    }

    fn diff_members(
        state: &mut DiffState,
        unit_a: &Unit,
        a: &UnionType,
        unit_b: &Unit,
        b: &UnionType,
    ) -> Result<()> {
        // TODO: handle reordering better
        state.list(unit_a, &a.members, unit_b, &b.members)
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name()) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &UnionType, b: &UnionType) -> cmp::Ordering {
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
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    fn bit_size(&self, hash: &FileHash) -> Option<u64> {
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

    fn padding(&self, bit_size: Option<u64>) -> Option<Padding> {
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

    fn print_name(
        &self,
        w: &mut ValuePrinter,
        hash: &FileHash,
        bit_size: Option<u64>,
    ) -> Result<()> {
        write!(w, "{}", format_bit(self.bit_offset))?;
        match bit_size {
            Some(bit_size) => {
                write!(w, "[{}]", format_bit(bit_size))?;
            }
            None => {
                // TODO: show element size for unsized arrays.
                debug!("no size for {:?}", self);
                write!(w, "[??]")?;
            }
        }
        write!(w, "\t{}: ", self.name().unwrap_or("<anon>"))?;
        Type::print_ref_from_offset(w, hash, self.ty)?;
        Ok(())
    }

    fn print_padding(
        &self,
        w: &mut ValuePrinter,
        hash: &FileHash,
        bit_size: Option<u64>,
    ) -> Result<()> {
        if let Some(padding) = self.padding(bit_size) {
            padding.print(w, hash)?;
        }
        Ok(())
    }
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
            |state| state.line(|w, state| self.print_name(w, state, bit_size)),
            |state| Type::print_members(state, unit, ty),
        )?;
        state.line(|w, state| self.print_padding(w, state, bit_size))
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
                    |w, state, (x, bit_size)| x.print_name(w, state, bit_size),
                )
            },
            |state| Type::diff_members(state, unit_a, ty_a, unit_b, ty_b),
        )?;

        state.line(
            (a, bit_size_a),
            (b, bit_size_b),
            |w, state, (x, bit_size)| x.print_padding(w, state, bit_size),
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

#[derive(Debug, PartialEq, Eq)]
struct Padding {
    bit_offset: u64,
    bit_size: u64,
}

impl Padding {
    fn print(&self, w: &mut ValuePrinter, _hash: &FileHash) -> Result<()> {
        write!(
            w,
            "{}[{}]\t<padding>",
            format_bit(self.bit_offset),
            format_bit(self.bit_size)
        )?;
        Ok(())
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct EnumerationType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
    pub source: Source<'input>,
    pub declaration: bool,
    pub ty: TypeOffset,
    pub byte_size: Size,
    pub enumerators: Vec<Enumerator<'input>>,
}

impl<'input> EnumerationType<'input> {
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size.get()
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash))
        }
    }

    fn print_name(&self, w: &mut ValuePrinter) -> Result<()> {
        write!(w, "enum ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        write!(w, "{}", self.name().unwrap_or("<anon>"))?;
        Ok(())
    }

    fn print_ref(&self, w: &mut ValuePrinter, id: usize) -> Result<()> {
        w.link(id, &mut |w| self.print_name(w))
    }

    fn print(&self, state: &mut PrintState, unit: &Unit, id: usize) -> Result<()> {
        state.collapsed(
            |state| state.id(id, |w, _state| self.print_name(w)),
            |state| {
                if state.options().print_source {
                    state.field("source", |w, _state| self.print_source(w, unit))?;
                }
                state.field("declaration", |w, _state| self.print_declaration(w))?;
                state.field("size", |w, state| self.print_byte_size(w, state))?;
                state.field_expanded("enumerators", |state| state.list(unit, &self.enumerators))
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn diff(
        state: &mut DiffState,
        id: usize,
        unit_a: &Unit,
        a: &EnumerationType,
        unit_b: &Unit,
        b: &EnumerationType,
    ) -> Result<()> {
        // The names should be the same, but we can't be sure.
        state.collapsed(
            |state| state.id(id, a, b, |w, _state, x| x.print_name(w)),
            |state| {
                if state.options().print_source {
                    state.field(
                        "source",
                        (unit_a, a),
                        (unit_b, b),
                        |w, _state, (unit, x)| x.print_source(w, unit),
                    )?;
                }
                state.field("declaration", a, b, |w, _state, x| x.print_declaration(w))?;
                state.field("size", a, b, |w, state, x| x.print_byte_size(w, state))?;
                // TODO: handle reordering better
                state.field_expanded("enumerators", |state| {
                    state.list(unit_a, &a.enumerators, unit_b, &b.enumerators)
                })
            },
        )?;
        state.line_break()?;
        Ok(())
    }

    fn print_source(&self, w: &mut ValuePrinter, unit: &Unit) -> Result<()> {
        if self.source.is_some() {
            self.source.print(w, unit)?;
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut ValuePrinter) -> Result<()> {
        if self.declaration {
            write!(w, "yes")?;
        }
        Ok(())
    }

    fn print_byte_size(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        if let Some(size) = self.byte_size(hash) {
            write!(w, "{}", size)?;
        } else {
            debug!("enum with no size");
        }
        Ok(())
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name()) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &EnumerationType, b: &EnumerationType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name(), &b.namespace, b.name())
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct Enumerator<'input> {
    pub name: Option<&'input str>,
    pub value: Option<i64>,
}

impl<'input> Enumerator<'input> {
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn print_name_value(&self, w: &mut ValuePrinter) -> Result<()> {
        write!(w, "{}", self.name().unwrap_or("<anon>"))?;
        if let Some(value) = self.value {
            write!(w, "({})", value)?;
        }
        Ok(())
    }
}

impl<'input> Print for Enumerator<'input> {
    type Arg = Unit<'input>;

    fn print(&self, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(|w, _state| self.print_name_value(w))
    }

    fn diff(
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(a, b, |w, _state, x| x.print_name_value(w))
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
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 4;
        }
        if a.value.cmp(&b.value) != cmp::Ordering::Equal {
            cost += 2;
        }
        cost
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
    fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size.get()
        } else if let (Some(ty), Some(count)) = (self.ty(hash), self.count.get()) {
            ty.byte_size(hash).map(|v| v * count)
        } else {
            None
        }
    }

    fn count(&self, hash: &FileHash) -> Option<u64> {
        if self.count.is_some() {
            self.count.get()
        } else if let (Some(ty), Some(byte_size)) = (self.ty(hash), self.byte_size.get()) {
            ty.byte_size(hash).map(|v| byte_size / v)
        } else {
            None
        }
    }

    fn print_ref(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        write!(w, "[")?;
        Type::print_ref_from_offset(w, hash, self.ty)?;
        if let Some(count) = self.count(hash) {
            write!(w, "; {}", count)?;
        }
        write!(w, "]")?;
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(hash_a: &FileHash, a: &ArrayType, hash_b: &FileHash, b: &ArrayType) -> cmp::Ordering {
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
    fn byte_size(&self) -> Option<u64> {
        self.byte_size.get()
    }

    fn return_type<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.return_type)
    }

    fn print_ref(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        let mut first = true;
        write!(w, "(")?;
        for parameter in &self.parameters {
            if first {
                first = false;
            } else {
                write!(w, ", ")?;
            }
            parameter.print_decl(w, hash)?;
        }
        write!(w, ")")?;

        if let Some(return_type) = self.return_type(hash) {
            write!(w, " -> ")?;
            return_type.print_ref(w, hash)?;
        }
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(
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
    fn name(&self) -> Option<&str> {
        self.name
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name()) && options.filter_namespace(&self.namespace)
    }

    fn print_ref(&self, w: &mut ValuePrinter) -> Result<()> {
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        write!(w, "{}", self.name().unwrap_or("<void>"))?;
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &UnspecifiedType, b: &UnspecifiedType) -> cmp::Ordering {
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
    fn ty<'a, 'input>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    fn containing_ty<'a, 'input>(
        &self,
        hash: &'a FileHash<'input>,
    ) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.containing_ty)
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
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

    fn print_ref(&self, w: &mut ValuePrinter, hash: &FileHash) -> Result<()> {
        Type::print_ref_from_offset(w, hash, self.containing_ty)?;
        write!(w, "::* ")?;
        Type::print_ref_from_offset(w, hash, self.ty)?;
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(
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

fn format_bit(val: u64) -> String {
    let byte = val / 8;
    let bit = val % 8;
    if bit == 0 {
        format!("{}", byte)
    } else {
        format!("{}.{}", byte, bit)
    }
}
