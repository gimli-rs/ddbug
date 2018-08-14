use std::borrow::Cow;
use std::cell::Cell;
use std::cmp;
use std::rc::Rc;
use std::usize;

use file::FileHash;
use namespace::Namespace;
use range::Range;
use source::Source;
use types::{Type, TypeOffset};
use variable::LocalVariable;
use {Address, Size};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionOffset(usize);

impl FunctionOffset {
    #[inline]
    pub(crate) fn new(offset: usize) -> FunctionOffset {
        debug_assert!(FunctionOffset(offset) != FunctionOffset::none());
        FunctionOffset(offset)
    }

    #[inline]
    pub(crate) fn none() -> FunctionOffset {
        FunctionOffset(usize::MAX)
    }

    #[inline]
    pub(crate) fn is_none(self) -> bool {
        self == Self::none()
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

impl Default for FunctionOffset {
    #[inline]
    fn default() -> Self {
        FunctionOffset::none()
    }
}

#[derive(Debug, Default)]
pub struct Function<'input> {
    pub id: Cell<usize>,
    pub offset: FunctionOffset,
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
    pub linkage_name: Option<&'input str>,
    pub symbol_name: Option<&'input str>,
    pub source: Source<'input>,
    pub address: Address,
    pub size: Size,
    pub inline: bool,
    pub declaration: bool,
    pub parameters: Vec<Parameter<'input>>,
    pub return_type: TypeOffset,
}

#[derive(Debug, Default)]
pub struct FunctionDetails<'input> {
    pub variables: Vec<LocalVariable<'input>>,
    pub inlined_functions: Vec<InlinedFunction<'input>>,
}

impl<'input> Function<'input> {
    pub fn from_offset<'a>(
        hash: &'a FileHash<'input>,
        offset: FunctionOffset,
    ) -> Option<&'a Function<'input>> {
        if offset.is_none() {
            return None;
        }
        hash.functions_by_offset
            .get(&offset)
            .map(|function| *function)
    }

    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn linkage_name(&self) -> Option<&str> {
        self.linkage_name
    }

    pub fn symbol_name(&self) -> Option<&str> {
        self.symbol_name
    }

    pub fn address(&self) -> Option<u64> {
        self.address.get()
    }

    pub fn size(&self) -> Option<u64> {
        self.size.get()
    }

    pub fn range(&self) -> Option<Range> {
        if let (Some(address), Some(size)) = (self.address(), self.size()) {
            Some(Range {
                begin: address,
                end: address + size,
            })
        } else {
            None
        }
    }

    pub fn return_type<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.return_type)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ParameterOffset(usize);

impl ParameterOffset {
    #[inline]
    pub(crate) fn new(offset: usize) -> ParameterOffset {
        debug_assert!(ParameterOffset(offset) != ParameterOffset::none());
        ParameterOffset(offset)
    }

    #[inline]
    pub(crate) fn none() -> ParameterOffset {
        ParameterOffset(usize::MAX)
    }
}

impl Default for ParameterOffset {
    #[inline]
    fn default() -> Self {
        ParameterOffset::none()
    }
}

#[derive(Debug, Default, Clone)]
pub struct Parameter<'input> {
    pub offset: ParameterOffset,
    pub name: Option<&'input str>,
    pub ty: TypeOffset,
}

impl<'input> Parameter<'input> {
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
    #[allow(dead_code)]
    fn cmp_id(hash_a: &FileHash, a: &Parameter, hash_b: &FileHash, b: &Parameter) -> cmp::Ordering {
        let ord = Self::cmp_type(hash_a, a, hash_b, b);
        if ord != cmp::Ordering::Equal {
            return ord;
        }
        a.name.cmp(&b.name)
    }

    pub fn cmp_type(
        hash_a: &FileHash,
        a: &Parameter,
        hash_b: &FileHash,
        b: &Parameter,
    ) -> cmp::Ordering {
        match (a.ty(hash_a), b.ty(hash_b)) {
            (Some(ref ty_a), Some(ref ty_b)) => Type::cmp_id(hash_a, ty_a, hash_b, ty_b),
            (Some(_), None) => cmp::Ordering::Less,
            (None, Some(_)) => cmp::Ordering::Greater,
            (None, None) => cmp::Ordering::Equal,
        }
    }
}

#[derive(Debug, Default)]
pub struct InlinedFunction<'input> {
    pub abstract_origin: FunctionOffset,
    pub size: Size,
    pub parameters: Vec<Parameter<'input>>,
    pub variables: Vec<LocalVariable<'input>>,
    pub inlined_functions: Vec<InlinedFunction<'input>>,
    pub call_source: Source<'input>,
}

impl<'input> InlinedFunction<'input> {
    pub fn size(&self) -> Option<u64> {
        self.size.get()
    }
}
