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
use {Address, Size};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableOffset(usize);

impl VariableOffset {
    #[inline]
    pub(crate) fn new(offset: usize) -> VariableOffset {
        debug_assert!(VariableOffset(offset) != VariableOffset::none());
        VariableOffset(offset)
    }

    #[inline]
    pub(crate) fn none() -> VariableOffset {
        VariableOffset(usize::MAX)
    }
}

impl Default for VariableOffset {
    #[inline]
    fn default() -> Self {
        VariableOffset::none()
    }
}

#[derive(Debug, Default)]
pub struct Variable<'input> {
    pub id: Cell<usize>,
    pub offset: VariableOffset,
    pub namespace: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input str>,
    pub linkage_name: Option<&'input str>,
    pub symbol_name: Option<&'input str>,
    pub ty: TypeOffset,
    pub source: Source<'input>,
    pub address: Address,
    pub size: Size,
    pub declaration: bool,
}

impl<'input> Variable<'input> {
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
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

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.size.is_some() {
            self.size.get()
        } else {
            self.ty(hash).and_then(|t| t.byte_size(hash))
        }
    }

    pub fn range(&self, hash: &FileHash) -> Option<Range> {
        match (self.address(), self.byte_size(hash)) {
            (Some(begin), Some(size)) => Some(Range {
                begin,
                end: begin + size,
            }),
            _ => None,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct LocalVariable<'input> {
    pub offset: VariableOffset,
    pub name: Option<&'input str>,
    pub ty: TypeOffset,
    pub source: Source<'input>,
    pub address: Address,
    pub size: Size,
}

impl<'input> LocalVariable<'input> {
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.size.is_some() {
            self.size.get()
        } else {
            self.ty(hash).and_then(|t| t.byte_size(hash))
        }
    }

    pub fn cmp_id(_hash_a: &FileHash, a: &Self, _hash_b: &FileHash, b: &Self) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}
