use std::cmp;
use std::io::Write;
use std::rc::Rc;
use std::marker;

use {Options, Result, Sort};
use file::FileHash;
use function::Parameter;
use namespace::Namespace;
use print::{DiffList, DiffState, Print, PrintState, SortList};
use unit::Unit;

#[derive(Debug)]
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
pub(crate) struct TypeOffset(pub usize);

#[derive(Debug)]
pub(crate) struct Type<'input> {
    pub offset: TypeOffset,
    pub kind: TypeKind<'input>,
}

impl<'input> Default for Type<'input> {
    fn default() -> Self {
        Type {
            offset: TypeOffset(0),
            kind: TypeKind::Base(BaseType::default()),
        }
    }
}

impl<'input> Type<'input> {
    pub fn from_offset<'a>(
        hash: &'a FileHash<'a, 'input>,
        offset: TypeOffset,
    ) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        hash.types.get(&offset).map(|ty| *ty)
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
            TypeKind::Base(..) |
            TypeKind::Def(..) |
            TypeKind::Enumeration(..) |
            TypeKind::Array(..) |
            TypeKind::Function(..) |
            TypeKind::Unspecified(..) |
            TypeKind::PointerToMember(..) |
            TypeKind::Modifier(..) => false,
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
            TypeKind::Struct(..) |
            TypeKind::Union(..) |
            TypeKind::Base(..) |
            TypeKind::Enumeration(..) |
            TypeKind::Array(..) |
            TypeKind::Unspecified(..) |
            TypeKind::PointerToMember(..) => false,
        }
    }

    pub fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        match self.kind {
            TypeKind::Struct(ref val) => val.visit_members(f),
            TypeKind::Union(ref val) => val.visit_members(f),
            TypeKind::Enumeration(..) |
            TypeKind::Def(..) |
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Function(..) |
            TypeKind::Unspecified(..) |
            TypeKind::PointerToMember(..) |
            TypeKind::Modifier(..) => {}
        }
    }

    pub fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        match self.kind {
            TypeKind::Def(ref val) => val.print(w, state, unit),
            TypeKind::Struct(ref val) => val.print(w, state, unit),
            TypeKind::Union(ref val) => val.print(w, state, unit),
            TypeKind::Enumeration(ref val) => val.print(w, state, unit),
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Function(..) |
            TypeKind::Unspecified(..) |
            TypeKind::PointerToMember(..) |
            TypeKind::Modifier(..) => Err(format!("can't print {:?}", self).into()),
        }
    }

    pub fn print_ref(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        match self.kind {
            TypeKind::Base(ref val) => val.print_ref(w),
            TypeKind::Def(ref val) => val.print_ref(w),
            TypeKind::Struct(ref val) => val.print_ref(w),
            TypeKind::Union(ref val) => val.print_ref(w),
            TypeKind::Enumeration(ref val) => val.print_ref(w),
            TypeKind::Array(ref val) => val.print_ref(w, state),
            TypeKind::Function(ref val) => val.print_ref(w, state),
            TypeKind::Unspecified(ref val) => val.print_ref(w),
            TypeKind::PointerToMember(ref val) => val.print_ref(w, state),
            TypeKind::Modifier(ref val) => val.print_ref(w, state),
        }
    }

    pub fn print_ref_from_offset(
        w: &mut Write,
        state: &PrintState,
        offset: Option<TypeOffset>,
    ) -> Result<()> {
        match offset {
            Some(offset) => match Type::from_offset(state.hash, offset) {
                Some(ty) => ty.print_ref(w, state)?,
                None => write!(w, "<invalid-type {}>", offset.0)?,
            },
            None => write!(w, "void")?,
        }
        Ok(())
    }

    pub fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        type_a: &Type,
        unit_b: &Unit,
        type_b: &Type,
    ) -> Result<()> {
        use self::TypeKind::*;
        match (&type_a.kind, &type_b.kind) {
            (&Def(ref a), &Def(ref b)) => TypeDef::diff(w, state, unit_a, a, unit_b, b),
            (&Struct(ref a), &Struct(ref b)) => StructType::diff(w, state, unit_a, a, unit_b, b),
            (&Union(ref a), &Union(ref b)) => UnionType::diff(w, state, unit_a, a, unit_b, b),
            (&Enumeration(ref a), &Enumeration(ref b)) => {
                EnumerationType::diff(w, state, unit_a, a, unit_b, b)
            }
            _ => Err(format!("can't diff {:?}, {:?}", type_a, type_b).into()),
        }?;
        Ok(())
    }

    fn print_members(
        label: &str,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
        ty: Option<&Type>,
    ) -> Result<()> {
        if let Some(ty) = ty {
            match ty.kind {
                TypeKind::Struct(ref t) => return t.print_members(label, w, state, unit),
                TypeKind::Union(ref t) => return t.print_members(label, w, state, unit),
                _ => return Err(format!("can't print members {:?}", ty).into()),
            }
        }
        Ok(())
    }

    fn diff_members(
        label: &str,
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        type_a: Option<&Type>,
        unit_b: &Unit,
        type_b: Option<&Type>,
    ) -> Result<()> {
        if let (Some(type_a), Some(type_b)) = (type_a, type_b) {
            match (&type_a.kind, &type_b.kind) {
                (&TypeKind::Struct(ref a), &TypeKind::Struct(ref b)) => {
                    return StructType::diff_members(label, w, state, unit_a, a, unit_b, b);
                }
                (&TypeKind::Union(ref a), &TypeKind::Union(ref b)) => {
                    return UnionType::diff_members(label, w, state, unit_a, a, unit_b, b);
                }
                _ => {}
            }
        }

        // Different types, so don't try to diff the members.
        state.prefix_diff(|state| {
            Type::print_members(label, w, &mut state.a, unit_a, type_a)?;
            Type::print_members(label, w, &mut state.b, unit_b, type_b)
        })
    }

    pub fn filter(&self, options: &Options) -> bool {
        match self.kind {
            TypeKind::Def(ref val) => val.filter(options),
            TypeKind::Struct(ref val) => val.filter(options),
            TypeKind::Union(ref val) => val.filter(options),
            TypeKind::Enumeration(ref val) => val.filter(options),
            TypeKind::Unspecified(ref val) => val.filter(options),
            TypeKind::Base(..) |
            TypeKind::Array(..) |
            TypeKind::Function(..) |
            TypeKind::PointerToMember(..) |
            TypeKind::Modifier(..) => options.filter_name.is_none(),
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

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Self::Arg) -> Result<()> {
        self.print(w, state, unit)
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Self::Arg,
        a: &Self,
        unit_b: &Self::Arg,
        b: &Self,
    ) -> Result<()> {
        Self::diff(w, state, unit_a, a, unit_b, b)
    }
}

impl<'input> SortList for Type<'input> {
    /// This must only be called for types that have identifiers.
    fn cmp_id(
        state_a: &PrintState,
        type_a: &Type,
        state_b: &PrintState,
        type_b: &Type,
        _options: &Options,
    ) -> cmp::Ordering {
        Type::cmp_id(state_a.hash, type_a, state_b.hash, type_b)
    }

    fn cmp_by(
        state_a: &PrintState,
        a: &Self,
        state_b: &PrintState,
        b: &Self,
        options: &Options,
    ) -> cmp::Ordering {
        match options.sort {
            Sort::None => a.offset.0.cmp(&b.offset.0),
            Sort::Name => Type::cmp_id(state_a.hash, a, state_b.hash, b),
            Sort::Size => a.byte_size(state_a.hash).cmp(&b.byte_size(state_b.hash)),
        }
    }
}

#[derive(Debug)]
pub(crate) struct TypeModifier<'input> {
    pub kind: TypeModifierKind,
    pub ty: Option<TypeOffset>,
    pub name: Option<&'input [u8]>,
    pub byte_size: Option<u64>,
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
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            return self.byte_size;
        }
        match self.kind {
            TypeModifierKind::Const |
            TypeModifierKind::Packed |
            TypeModifierKind::Volatile |
            TypeModifierKind::Restrict |
            TypeModifierKind::Shared |
            TypeModifierKind::Atomic |
            TypeModifierKind::Other => self.ty(hash).and_then(|v| v.byte_size(hash)),
            TypeModifierKind::Pointer |
            TypeModifierKind::Reference |
            TypeModifierKind::RvalueReference => self.address_size,
        }
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        if let Some(name) = self.name {
            write!(w, "{}", String::from_utf8_lossy(name))?;
        } else {
            match self.kind {
                TypeModifierKind::Pointer => write!(w, "* ")?,
                TypeModifierKind::Reference | TypeModifierKind::RvalueReference => write!(w, "& ")?,
                TypeModifierKind::Const => write!(w, "const ")?,
                TypeModifierKind::Volatile => write!(w, "volatile ")?,
                TypeModifierKind::Restrict => write!(w, "restrict ")?,
                TypeModifierKind::Packed |
                TypeModifierKind::Shared |
                TypeModifierKind::Atomic |
                TypeModifierKind::Other => {}
            }
            Type::print_ref_from_offset(w, state, self.ty)?;
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
            (Some(ty_a), Some(ty_b)) => {
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

#[derive(Debug, Default)]
pub(crate) struct BaseType<'input> {
    pub name: Option<&'input [u8]>,
    pub byte_size: Option<u64>,
}

impl<'input> BaseType<'input> {
    fn byte_size(&self) -> Option<u64> {
        self.byte_size
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon-base-type>")?,
        }
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &BaseType, b: &BaseType) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}

#[derive(Debug, Default)]
pub(crate) struct TypeDef<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub ty: Option<TypeOffset>,
}

impl<'input> TypeDef<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|t| Type::from_offset(hash, t))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash))
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon-typedef>")?,
        }
        Ok(())
    }

    fn print_name(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        write!(w, "type ")?;
        self.print_ref(w)?;
        write!(w, " = ")?;
        Type::print_ref_from_offset(w, state, self.ty)?;
        Ok(())
    }

    fn print_byte_size(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if let Some(byte_size) = self.byte_size(state.hash) {
            write!(w, "size: {}", byte_size)?;
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        let ty = self.ty(state.hash);
        state.line(w, |w, state| self.print_name(w, state))?;
        state.indent(|state| {
            state.line(w, |w, state| self.print_byte_size(w, state))?;
            if let Some(ty) = ty {
                if ty.is_anon() {
                    Type::print_members("members", w, state, unit, Some(ty))?;
                }
            }
            Ok(())
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &TypeDef,
        unit_b: &Unit,
        b: &TypeDef,
    ) -> Result<()> {
        state.line(w, a, b, |w, state, x| x.print_name(w, state))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, state, x| x.print_byte_size(w, state))?;
            let ty_a = filter_option(a.ty(state.a.hash), Type::is_anon);
            let ty_b = filter_option(b.ty(state.b.hash), Type::is_anon);
            Type::diff_members("members", w, state, unit_a, ty_a, unit_b, ty_b)
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &TypeDef, b: &TypeDef) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }
}

fn filter_option<T, F>(o: Option<T>, f: F) -> Option<T>
where
    T: Copy,
    F: FnOnce(T) -> bool,
{
    o.and_then(|v| if f(v) { Some(v) } else { None })
}

#[derive(Debug, Default)]
pub(crate) struct StructType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub byte_size: Option<u64>,
    pub declaration: bool,
    pub members: Vec<Member<'input>>,
}

impl<'input> StructType<'input> {
    fn byte_size(&self) -> Option<u64> {
        self.byte_size
    }

    fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        write!(w, "struct ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line(w, |w, _state| self.print_ref(w))?;
        state.indent(|state| {
            state.line_option(w, |w, state| self.print_declaration(w, state))?;
            state.line_option(w, |w, state| self.print_byte_size(w, state))?;
            self.print_members("members", w, state, unit)
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &StructType,
        unit_b: &Unit,
        b: &StructType,
    ) -> Result<()> {
        // The names should be the same, but we can't be sure.
        state.line(w, a, b, |w, _state, x| x.print_ref(w))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, state, x| x.print_declaration(w, state))?;
            state.line_option(w, a, b, |w, state, x| x.print_byte_size(w, state))?;
            Self::diff_members("members", w, state, unit_a, a, unit_b, b)
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn print_byte_size(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size {
            write!(w, "size: {}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_members(
        &self,
        label: &str,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
    ) -> Result<()> {
        state.list(label, w, unit, &self.members)
    }

    fn diff_members(
        label: &str,
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &StructType,
        unit_b: &Unit,
        b: &StructType,
    ) -> Result<()> {
        state.list(label, w, unit_a, &a.members, unit_b, &b.members)
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &StructType, b: &StructType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }
}

#[derive(Debug, Default)]
pub(crate) struct UnionType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub byte_size: Option<u64>,
    pub declaration: bool,
    pub members: Vec<Member<'input>>,
}

impl<'input> UnionType<'input> {
    fn byte_size(&self) -> Option<u64> {
        self.byte_size
    }

    fn is_anon(&self) -> bool {
        self.name.is_none() || Namespace::is_anon_type(&self.namespace)
    }

    fn visit_members(&self, f: &mut FnMut(&Member) -> ()) {
        for member in &self.members {
            f(member);
        }
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        write!(w, "union ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line(w, |w, _state| self.print_ref(w))?;
        state.indent(|state| {
            state.line_option(w, |w, state| self.print_declaration(w, state))?;
            state.line_option(w, |w, state| self.print_byte_size(w, state))?;
            self.print_members("members", w, state, unit)
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &UnionType,
        unit_b: &Unit,
        b: &UnionType,
    ) -> Result<()> {
        // The names should be the same, but we can't be sure.
        state.line(w, a, b, |w, _state, x| x.print_ref(w))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, state, x| x.print_declaration(w, state))?;
            state.line_option(w, a, b, |w, state, x| x.print_byte_size(w, state))?;
            Self::diff_members("members", w, state, unit_a, a, unit_b, b)
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn print_byte_size(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size {
            write!(w, "size: {}", size)?;
        } else if !self.declaration {
            debug!("struct with no size");
        }
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_members(
        &self,
        label: &str,
        w: &mut Write,
        state: &mut PrintState,
        unit: &Unit,
    ) -> Result<()> {
        state.list(label, w, unit, &self.members)
    }

    fn diff_members(
        label: &str,
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &UnionType,
        unit_b: &Unit,
        b: &UnionType,
    ) -> Result<()> {
        // TODO: handle reordering better
        state.list(label, w, unit_a, &a.members, unit_b, &b.members)
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &UnionType, b: &UnionType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct Member<'input> {
    pub name: Option<&'input [u8]>,
    pub ty: Option<TypeOffset>,
    // Defaults to 0, so always present.
    pub bit_offset: u64,
    pub bit_size: Option<u64>,
    // Redundant, but simplifies code.
    pub next_bit_offset: Option<u64>,
}

impl<'input> Member<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|t| Type::from_offset(hash, t))
    }

    fn bit_size(&self, hash: &FileHash) -> Option<u64> {
        if self.bit_size.is_some() {
            self.bit_size
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash).map(|v| v * 8))
        }
    }

    pub fn is_inline(&self, hash: &FileHash) -> bool {
        match self.name {
            Some(s) => if s.starts_with(b"RUST$ENCODED$ENUM$") {
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
        if let (Some(bit_size), Some(next_bit_offset)) = (bit_size, self.next_bit_offset) {
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
        w: &mut Write,
        state: &mut PrintState,
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
        match self.name {
            Some(name) => write!(w, "\t{}", String::from_utf8_lossy(name))?,
            None => write!(w, "\t<anon>")?,
        }
        write!(w, ": ")?;
        Type::print_ref_from_offset(w, state, self.ty)?;
        Ok(())
    }

    fn print_padding(
        &self,
        w: &mut Write,
        state: &mut PrintState,
        bit_size: Option<u64>,
    ) -> Result<()> {
        if let Some(padding) = self.padding(bit_size) {
            padding.print(w, state)?;
        }
        Ok(())
    }
}

impl<'input> Print for Member<'input> {
    type Arg = Unit<'input>;

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        let bit_size = self.bit_size(state.hash);
        state.line(w, |w, state| self.print_name(w, state, bit_size))?;
        state.indent(|state| {
            let ty = if self.is_inline(state.hash) {
                self.ty(state.hash)
            } else {
                None
            };
            Type::print_members("", w, state, unit, ty)
        })?;
        state.line_option(w, |w, state| self.print_padding(w, state, bit_size))
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &Self,
        unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        let bit_size_a = a.bit_size(state.a.hash);
        let bit_size_b = b.bit_size(state.b.hash);
        state
            .line(w, (a, bit_size_a), (b, bit_size_b), |w, state, (x, bit_size)| {
                x.print_name(w, state, bit_size)
            })?;

        let ty_a = if a.is_inline(state.a.hash) {
            a.ty(state.a.hash)
        } else {
            None
        };
        let ty_b = if b.is_inline(state.b.hash) {
            b.ty(state.b.hash)
        } else {
            None
        };
        Type::diff_members("", w, state, unit_a, ty_a, unit_b, ty_b)?;

        state.line_option(w, (a, bit_size_a), (b, bit_size_b), |w, state, (x, bit_size)| {
            x.print_padding(w, state, bit_size)
        })
    }
}

impl<'input> DiffList for Member<'input> {
    fn step_cost() -> usize {
        1
    }

    fn diff_cost(state: &DiffState, _unit_a: &Unit, a: &Self, _unit_b: &Unit, b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 1;
        }
        match (a.ty(state.a.hash), b.ty(state.b.hash)) {
            (Some(ty_a), Some(ty_b)) => {
                if Type::cmp_id(state.a.hash, ty_a, state.b.hash, ty_b) != cmp::Ordering::Equal {
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
    fn print(&self, w: &mut Write, _state: &mut PrintState) -> Result<()> {
        write!(w, "{}[{}]\t<padding>", format_bit(self.bit_offset), format_bit(self.bit_size))?;
        Ok(())
    }
}

#[derive(Debug, Default)]
pub(crate) struct EnumerationType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub declaration: bool,
    pub ty: Option<TypeOffset>,
    pub byte_size: Option<u64>,
    pub enumerators: Vec<Enumerator<'input>>,
}

impl<'input> EnumerationType<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|t| Type::from_offset(hash, t))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size
        } else {
            self.ty(hash).and_then(|v| v.byte_size(hash))
        }
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        write!(w, "enum ")?;
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print(&self, w: &mut Write, state: &mut PrintState, unit: &Unit) -> Result<()> {
        state.line(w, |w, _state| self.print_ref(w))?;
        state.indent(|state| {
            state.line_option(w, |w, _state| self.print_declaration(w))?;
            state.line_option(w, |w, state| self.print_byte_size(w, state))?;
            state.list("enumerators", w, unit, &self.enumerators)
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        unit_a: &Unit,
        a: &EnumerationType,
        unit_b: &Unit,
        b: &EnumerationType,
    ) -> Result<()> {
        // The names should be the same, but we can't be sure.
        state.line(w, a, b, |w, _state, x| x.print_ref(w))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, _state, x| x.print_declaration(w))?;
            state.line_option(w, a, b, |w, state, x| x.print_byte_size(w, state))?;
            // TODO: handle reordering better
            state.list("enumerators", w, unit_a, &a.enumerators, unit_b, &b.enumerators)
        })?;
        writeln!(w, "")?;
        Ok(())
    }

    fn print_declaration(&self, w: &mut Write) -> Result<()> {
        if self.declaration {
            write!(w, "declaration: yes")?;
        }
        Ok(())
    }

    fn print_byte_size(&self, w: &mut Write, state: &mut PrintState) -> Result<()> {
        if let Some(size) = self.byte_size(state.hash) {
            write!(w, "size: {}", size)?;
        } else {
            debug!("enum with no size");
        }
        Ok(())
    }

    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &EnumerationType, b: &EnumerationType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct Enumerator<'input> {
    pub name: Option<&'input [u8]>,
    pub value: Option<i64>,
}

impl<'input> Enumerator<'input> {
    fn print_ref(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        Ok(())
    }

    fn print_name_value(&self, w: &mut Write) -> Result<()> {
        self.print_ref(w)?;
        if let Some(value) = self.value {
            write!(w, "({})", value)?;
        }
        Ok(())
    }
}

impl<'input> Print for Enumerator<'input> {
    type Arg = Unit<'input>;

    fn print(&self, w: &mut Write, state: &mut PrintState, _unit: &Unit) -> Result<()> {
        state.line(w, |w, _state| self.print_name_value(w))
    }

    fn diff(
        w: &mut Write,
        state: &mut DiffState,
        _unit_a: &Unit,
        a: &Self,
        _unit_b: &Unit,
        b: &Self,
    ) -> Result<()> {
        state.line(w, a, b, |w, _state, x| x.print_name_value(w))
    }
}

impl<'input> DiffList for Enumerator<'input> {
    fn step_cost() -> usize {
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

#[derive(Debug, Default)]
pub(crate) struct ArrayType<'input> {
    pub ty: Option<TypeOffset>,
    pub count: Option<u64>,
    pub byte_size: Option<u64>,
    pub phantom: marker::PhantomData<&'input [u8]>,
}

impl<'input> ArrayType<'input> {
    fn ty<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            self.byte_size
        } else if let (Some(ty), Some(count)) = (self.ty(hash), self.count) {
            ty.byte_size(hash).map(|v| v * count)
        } else {
            None
        }
    }

    fn count(&self, hash: &FileHash) -> Option<u64> {
        if self.count.is_some() {
            self.count
        } else if let (Some(ty), Some(byte_size)) = (self.ty(hash), self.byte_size) {
            ty.byte_size(hash).map(|v| byte_size / v)
        } else {
            None
        }
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        write!(w, "[")?;
        Type::print_ref_from_offset(w, state, self.ty)?;
        if let Some(count) = self.count(state.hash) {
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
            (Some(ty_a), Some(ty_b)) => {
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

#[derive(Debug, Default)]
pub(crate) struct FunctionType<'input> {
    pub parameters: Vec<Parameter<'input>>,
    pub return_type: Option<TypeOffset>,
    pub byte_size: Option<u64>,
}

impl<'input> FunctionType<'input> {
    fn byte_size(&self) -> Option<u64> {
        self.byte_size
    }

    fn return_type<'a>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.return_type.and_then(|v| Type::from_offset(hash, v))
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        let mut first = true;
        write!(w, "(")?;
        for parameter in &self.parameters {
            if first {
                first = false;
            } else {
                write!(w, ", ")?;
            }
            parameter.print_decl(w, state)?;
        }
        write!(w, ")")?;

        if let Some(return_type) = self.return_type(state.hash) {
            write!(w, " -> ")?;
            return_type.print_ref(w, state)?;
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
            (Some(ty_a), Some(ty_b)) => {
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

#[derive(Debug, Default)]
pub(crate) struct UnspecifiedType<'input> {
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
}

impl<'input> UnspecifiedType<'input> {
    fn filter(&self, options: &Options) -> bool {
        options.filter_name(self.name) && options.filter_namespace(&self.namespace)
    }

    fn print_ref(&self, w: &mut Write) -> Result<()> {
        if let Some(ref namespace) = self.namespace {
            namespace.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<void>")?,
        }
        Ok(())
    }

    /// Compare the identifying information of two types.
    /// This can be used to sort, and to determine if two types refer to the same definition
    /// (even if there are differences in the definitions).
    fn cmp_id(a: &UnspecifiedType, b: &UnspecifiedType) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(&a.namespace, a.name, &b.namespace, b.name)
    }
}

#[derive(Debug, Default)]
pub(crate) struct PointerToMemberType {
    pub ty: Option<TypeOffset>,
    pub containing_ty: Option<TypeOffset>,
    pub byte_size: Option<u64>,
    // TODO: hack
    pub address_size: Option<u64>,
}

impl PointerToMemberType {
    fn ty<'a, 'input>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.ty.and_then(|v| Type::from_offset(hash, v))
    }

    fn containing_ty<'a, 'input>(&self, hash: &'a FileHash<'a, 'input>) -> Option<&'a Type<'input>>
    where
        'input: 'a,
    {
        self.containing_ty.and_then(|v| Type::from_offset(hash, v))
    }

    fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.byte_size.is_some() {
            return self.byte_size;
        }
        // TODO: this probably depends on the ABI
        self.ty(hash).and_then(|ty| if ty.is_function(hash) {
            self.address_size.map(|v| v * 2)
        } else {
            self.address_size
        })
    }

    fn print_ref(&self, w: &mut Write, state: &PrintState) -> Result<()> {
        Type::print_ref_from_offset(w, state, self.containing_ty)?;
        write!(w, "::* ")?;
        Type::print_ref_from_offset(w, state, self.ty)?;
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
            (Some(ty_a), Some(ty_b)) => {
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
            (Some(ty_a), Some(ty_b)) => {
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
