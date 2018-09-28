use std::borrow::Cow;
use std::cell::Cell;
use std::cmp;
use std::rc::Rc;
use std::usize;

use file::FileHash;
use location::{FrameLocation, Location, Piece, Register};
use namespace::Namespace;
use range::Range;
use source::Source;
use types::{Type, TypeOffset};
use {Address, Size};

/// The debuginfo offset of a variable.
///
/// This is unique for all variables in a file.
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

/// A global variable.
#[derive(Debug, Default)]
pub struct Variable<'input> {
    pub(crate) id: Cell<usize>,
    pub(crate) offset: VariableOffset,
    pub(crate) namespace: Option<Rc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
    pub(crate) linkage_name: Option<&'input str>,
    pub(crate) symbol_name: Option<&'input str>,
    pub(crate) ty: TypeOffset,
    pub(crate) source: Source<'input>,
    pub(crate) address: Address,
    pub(crate) size: Size,
    pub(crate) declaration: bool,
}

impl<'input> Variable<'input> {
    /// The user defined id for this variable.
    #[inline]
    pub fn id(&self) -> usize {
        self.id.get()
    }

    /// Set a user defined id for this variable.
    #[inline]
    pub fn set_id(&self, id: usize) {
        self.id.set(id)
    }

    /// The namespace of the variable.
    pub fn namespace(&self) -> Option<&Namespace> {
        self.namespace.as_ref().map(|x| &**x)
    }

    /// The name of the variable.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The linkage name of the variable.
    #[inline]
    pub fn linkage_name(&self) -> Option<&str> {
        self.linkage_name
    }

    /// The symbol name of the variable.
    ///
    /// This is determined from a symbol table entry with a matching address.
    #[inline]
    pub fn symbol_name(&self) -> Option<&str> {
        self.symbol_name
    }

    /// The type of the variable.
    ///
    /// Returns `None` if the type is invalid.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The source information for the variable.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.source
    }

    /// The address of the variable.
    #[inline]
    pub fn address(&self) -> Option<u64> {
        self.address.get()
    }

    /// The size in bytes of the variable.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.size.is_some() {
            self.size.get()
        } else {
            self.ty(hash).and_then(|t| t.byte_size(hash))
        }
    }

    /// The address range of the variable.
    pub fn range(&self, hash: &FileHash) -> Option<Range> {
        match (self.address(), self.byte_size(hash)) {
            (Some(begin), Some(size)) => Some(Range {
                begin,
                end: begin + size,
            }),
            _ => None,
        }
    }

    /// Return true if this is a declaration.
    #[inline]
    pub fn is_declaration(&self) -> bool {
        self.declaration
    }

    /// Compare the identifying information of two variables.
    ///
    /// Variables are equal if they have the same namespace and name.
    ///
    /// This can be used to sort, and to determine if two variables refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        _hash_a: &FileHash,
        a: &Variable,
        _hash_b: &FileHash,
        b: &Variable,
    ) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(a.namespace(), a.name(), b.namespace(), b.name())
    }
}

/// A local variable.
#[derive(Debug, Default, Clone)]
pub struct LocalVariable<'input> {
    pub(crate) offset: VariableOffset,
    pub(crate) name: Option<&'input str>,
    pub(crate) ty: TypeOffset,
    pub(crate) source: Source<'input>,
    pub(crate) address: Address,
    pub(crate) size: Size,
    pub(crate) locations: Vec<Piece>,
}

impl<'input> LocalVariable<'input> {
    /// The name of the variable.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// The type of the variable.
    ///
    /// Returns `None` if the type is invalid.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The source information for the variable.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.source
    }

    /// The address of the variable.
    ///
    /// This will only be known for static variables.
    #[inline]
    pub fn address(&self) -> Option<u64> {
        self.address.get()
    }

    /// The size in bytes of the variable.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        if self.size.is_some() {
            self.size.get()
        } else {
            self.ty(hash).and_then(|t| t.byte_size(hash))
        }
    }

    /// The registers in which this variable is stored.
    pub fn registers<'a>(&'a self) -> impl Iterator<Item = Register> + 'a {
        self.locations.iter().filter_map(|piece| {
            if piece.is_value {
                return None;
            }
            match piece.location {
                Location::Register { register } => Some(register),
                _ => None,
            }
        })
    }

    /// The stack frame locations at which this variable is stored.
    pub fn frame_locations<'a>(&'a self) -> impl Iterator<Item = FrameLocation> + 'a {
        self.locations.iter().filter_map(|piece| {
            if piece.is_value {
                return None;
            }
            match piece.location {
                // TODO: do we need to distinguish between these?
                Location::FrameOffset { offset } | Location::CfaOffset { offset } => {
                    Some(FrameLocation {
                        offset,
                        bit_size: piece.bit_size,
                    })
                }
                _ => None,
            }
        })
    }

    /// Compare the identifying information of two variables.
    ///
    /// Variables are considered equal if their names are equal.
    ///
    /// This can be used to sort, and to determine if two variables refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(_hash_a: &FileHash, a: &Self, _hash_b: &FileHash, b: &Self) -> cmp::Ordering {
        a.name.cmp(&b.name)
    }
}
