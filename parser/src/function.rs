use std::borrow::Cow;
use std::cmp;
use std::sync::Arc;

use fnv::FnvHashMap as HashMap;

use crate::file::FileHash;
use crate::location::{self, FrameLocation, Piece, Register};
use crate::namespace::Namespace;
use crate::range::Range;
use crate::source::Source;
use crate::types::{MemberOffset, ParameterType, Type, TypeOffset};
use crate::variable::{LocalVariable, Variable, VariableOffset};
use crate::{Address, Id, Size};

/// The debuginfo offset of a function.
///
/// This is unique for all functions in a file.
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
    pub(crate) fn is_some(self) -> bool {
        self != Self::none()
    }

    #[inline]
    pub(crate) fn get(self) -> Option<usize> {
        if self.is_none() { None } else { Some(self.0) }
    }
}

impl Default for FunctionOffset {
    #[inline]
    fn default() -> Self {
        FunctionOffset::none()
    }
}

/// A function.
#[derive(Debug, Default)]
pub struct Function<'input> {
    pub(crate) id: Id,
    pub(crate) offset: FunctionOffset,
    pub(crate) namespace: Option<Arc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
    pub(crate) linkage_name: Option<&'input str>,
    pub(crate) symbol_name: Option<&'input str>,
    pub(crate) source: Source<'input>,
    pub(crate) address: Address,
    pub(crate) size: Size,
    pub(crate) ranges: Vec<Range>,
    pub(crate) inline: bool,
    pub(crate) declaration: bool,
    pub(crate) parameters: Vec<ParameterType<'input>>,
    pub(crate) return_type: TypeOffset,
}

/// Extra function details.
///
/// These are kept separate from `Function` so that they can be loaded only when needed.
#[derive(Debug, Default)]
pub struct FunctionDetails<'input> {
    pub(crate) parameters: Vec<Parameter<'input>>,
    pub(crate) variables: Vec<LocalVariable<'input>>,
    pub(crate) inlined_functions: Vec<InlinedFunction<'input>>,
    pub(crate) calls: Vec<FunctionCall<'input>>,
}

impl<'input> Function<'input> {
    pub(crate) fn from_offset<'a>(
        hash: &'a FileHash<'input>,
        offset: FunctionOffset,
    ) -> Option<&'input Function<'input>> {
        if offset.is_none() {
            return None;
        }
        hash.functions_by_offset.get(&offset).cloned()
    }

    /// The user defined id for this function.
    #[inline]
    pub fn id(&self) -> usize {
        self.id.get()
    }

    /// Set a user defined id for this function.
    #[inline]
    pub fn set_id(&self, id: usize) {
        self.id.set(id)
    }

    /// The namespace of the function.
    pub fn namespace(&self) -> Option<&Namespace<'input>> {
        self.namespace.as_deref()
    }

    /// The name of the function.
    #[inline]
    pub fn name(&self) -> Option<&'input str> {
        self.name
    }

    /// The linkage name of the variable.
    #[inline]
    pub fn linkage_name(&self) -> Option<&'input str> {
        self.linkage_name
    }

    /// The symbol name of the function.
    ///
    /// This is determined from a symbol table entry with a matching address.
    #[inline]
    pub fn symbol_name(&self) -> Option<&'input str> {
        self.symbol_name
    }

    /// The source information for the function.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.source
    }

    /// The address of the function.
    #[inline]
    pub fn address(&self) -> Option<u64> {
        self.address.get()
    }

    /// The size in bytes of the function.
    ///
    /// This may exclude padding, and may be non-contiguous.
    #[inline]
    pub fn size(&self) -> Option<u64> {
        self.size.get()
    }

    /// The address ranges of the function.
    pub fn ranges(&self) -> &[Range] {
        &self.ranges
    }

    /// Return true if this is an inlined function.
    #[inline]
    pub fn is_inline(&self) -> bool {
        self.inline
    }

    /// Return true if this is a declaration.
    #[inline]
    pub fn is_declaration(&self) -> bool {
        self.declaration
    }

    /// The function parameter types.
    #[inline]
    pub fn parameters(&self) -> &[ParameterType<'input>] {
        &self.parameters
    }

    /// The return type.
    ///
    /// Returns `None` if the return type is invalid.
    #[inline]
    pub fn return_type<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.return_type)
    }

    /// Extra function details.
    pub fn details(&self, hash: &FileHash<'input>) -> FunctionDetails<'input> {
        hash.file.get_function_details(self.offset, hash)
    }

    /// Compare the identifying information of two functions.
    ///
    /// Functions are equal if they have the same namespace and name.
    ///
    /// This can be used to sort, and to determine if two functions refer to the same definition
    /// (even if there are differences in the definitions).
    pub fn cmp_id(
        _hash_a: &FileHash,
        a: &Function,
        _hash_b: &FileHash,
        b: &Function,
    ) -> cmp::Ordering {
        Namespace::cmp_ns_and_name(a.namespace(), a.name(), b.namespace(), b.name())
    }
}

impl<'input> FunctionDetails<'input> {
    /// The function parameters.
    #[inline]
    pub fn parameters(&self) -> &[Parameter<'input>] {
        &self.parameters
    }

    /// The local variables.
    #[inline]
    pub fn variables(&self) -> &[LocalVariable<'input>] {
        &self.variables
    }

    /// The inlined functions.
    #[inline]
    pub fn inlined_functions(&self) -> &[InlinedFunction<'input>] {
        &self.inlined_functions
    }

    /// The calls to non-inlined functions.
    #[inline]
    pub fn calls(&self) -> &[FunctionCall<'input>] {
        &self.calls
    }
}

/// The debuginfo offset of a parameter formal specification/definition.
///
/// This is unique for all parameter specifications/definitions in a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

/// A function parameter definition.
#[derive(Debug, Default, Clone)]
pub struct Parameter<'input> {
    pub(crate) offset: ParameterOffset,
    pub(crate) name: Option<&'input str>,
    pub(crate) ty: TypeOffset,
    // TODO: move this to ParameterDetails
    pub(crate) locations: Vec<(Range, Piece)>,
}

impl<'input> Parameter<'input> {
    /// The name of the parameter.
    #[inline]
    pub fn name(&self) -> Option<&'input str> {
        self.name
    }

    /// The debuginfo offset of this parameter.
    #[inline]
    pub fn offset(&self) -> ParameterOffset {
        self.offset
    }

    /// The type offset of the parameter.
    ///
    /// A type offset is unique for all types in a file.
    #[inline]
    pub fn type_offset(&self) -> TypeOffset {
        self.ty
    }

    /// The type of the parameter.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        Type::from_offset(hash, self.ty)
    }

    /// The size in bytes of the parameter.
    pub fn byte_size(&self, hash: &FileHash) -> Option<u64> {
        self.ty(hash).and_then(|v| v.byte_size(hash))
    }

    /// A list of all locations where this parameter is stored.
    pub fn locations(&self) -> &[(Range, Piece)] {
        &self.locations
    }

    /// The registers in which this parameter is stored.
    pub fn registers(&self) -> impl Iterator<Item = (Range, Register)> + '_ {
        location::registers(&self.locations)
    }

    /// The registers pointing to where this variable is stored.
    pub fn register_offsets(&self) -> impl Iterator<Item = (Range, Register, i64)> + '_ {
        location::register_offsets(&self.locations)
    }

    /// The stack frame locations at which this parameter is stored.
    pub fn frame_locations(&self) -> impl Iterator<Item = (Range, FrameLocation)> + '_ {
        location::frame_locations(&self.locations)
    }

    /// Compare the identifying information of two parameters.
    ///
    /// Parameters are considered equal if their name and type are equal.
    ///
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

    /// Compare the types of two parameters.
    pub fn cmp_type(
        hash_a: &FileHash,
        a: &Parameter,
        hash_b: &FileHash,
        b: &Parameter,
    ) -> cmp::Ordering {
        match (&a.ty(hash_a), &b.ty(hash_b)) {
            (Some(ty_a), Some(ty_b)) => Type::cmp_id(hash_a, ty_a, hash_b, ty_b),
            (Some(_), None) => cmp::Ordering::Less,
            (None, Some(_)) => cmp::Ordering::Greater,
            (None, None) => cmp::Ordering::Equal,
        }
    }
}

/// An inlined instance of a function.
#[derive(Debug, Default)]
pub struct InlinedFunction<'input> {
    pub(crate) abstract_origin: FunctionOffset,
    pub(crate) size: Size,
    pub(crate) ranges: Vec<Range>,
    pub(crate) parameters: Vec<Parameter<'input>>,
    pub(crate) variables: Vec<LocalVariable<'input>>,
    pub(crate) inlined_functions: Vec<InlinedFunction<'input>>,
    pub(crate) calls: Vec<FunctionCall<'input>>,
    pub(crate) call_source: Source<'input>,
}

impl<'input> InlinedFunction<'input> {
    /// The function that this is an inlined instance of.
    #[inline]
    pub fn abstract_origin<'a>(&self, hash: &'a FileHash<'input>) -> Option<&'a Function<'input>> {
        Function::from_offset(hash, self.abstract_origin)
    }

    /// The address ranges of the inlined function instance.
    #[inline]
    pub fn ranges(&self) -> &[Range] {
        &self.ranges
    }

    /// The size of the inlined function instance.
    #[inline]
    pub fn size(&self) -> Option<u64> {
        self.size.get()
    }

    /// The source information for call location.
    #[inline]
    pub fn call_source(&self) -> &Source<'input> {
        &self.call_source
    }

    /// The function parameters.
    #[inline]
    pub fn parameters(&self) -> &[Parameter<'input>] {
        &self.parameters
    }

    /// The local variables.
    #[inline]
    pub fn variables(&self) -> &[LocalVariable<'input>] {
        &self.variables
    }

    /// The inlined functions within this inlined functions.
    #[inline]
    pub fn inlined_functions(&self) -> &[InlinedFunction<'input>] {
        &self.inlined_functions
    }

    /// The calls to non-inlined functions.
    #[inline]
    pub fn calls(&self) -> &[FunctionCall<'input>] {
        &self.calls
    }
}

/// A call to another (non-inlined) function.
#[derive(Debug, Default)]
pub struct FunctionCall<'input> {
    pub(crate) kind: FunctionCallKind,
    pub(crate) return_address: Option<u64>,
    pub(crate) call_address: Option<u64>,
    pub(crate) origin: Option<FunctionCallOrigin<'input>>,
    pub(crate) target: Vec<Piece>,
    pub(crate) target_is_clobbered: bool,
    pub(crate) ty: Option<TypeOffset>,
    pub(crate) called_from_source: Source<'input>,
    pub(crate) parameters: Vec<FunctionCallParameter<'input>>,
}

impl<'input> FunctionCall<'input> {
    /// The kind of function call (normal or tail call).
    #[inline]
    pub fn kind(&self) -> FunctionCallKind {
        self.kind
    }

    /// The return address after the call.
    #[inline]
    pub fn return_address(&self) -> Option<u64> {
        self.return_address
    }

    /// The address of the call instruction.
    ///
    /// This the call-like instruction for a normal call or the jump-like instruction
    /// for a tail call.
    #[inline]
    pub fn call_address(&self) -> Option<u64> {
        self.call_address
    }

    /// The origin of the target of the call.
    ///
    /// This determines whether the call is direct or indirect,
    /// and if it is indirect, where the function pointer comes from.
    #[inline]
    pub fn origin(&self) -> Option<&FunctionCallOrigin<'input>> {
        self.origin.as_ref()
    }

    /// The computed value of the target of the call.
    ///
    /// This is only used if the target is indirect.
    #[inline]
    pub fn target(&self) -> &[Piece] {
        &self.target
    }

    /// Whether the expression for the value of `target` is only valid before the call.
    #[inline]
    pub fn target_is_clobbered(&self) -> bool {
        self.target_is_clobbered
    }

    /// The type of the target of the call.
    ///
    /// This is usually omitted if `origin` is specified.
    ///
    /// Returns `None` if the type is invalid or unknown.
    // TODO: add a convenient way to get the type from either `origin` or `ty`.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        if let Some(ty) = self.ty {
            Type::from_offset(hash, ty)
        } else {
            None
        }
    }

    /// The source location of the call.
    #[inline]
    pub fn source(&self) -> &Source<'input> {
        &self.called_from_source
    }

    /// The function parameters for this call.
    #[inline]
    pub fn parameters(&self) -> &[FunctionCallParameter<'input>] {
        &self.parameters
    }
}

/// The kind of function call being made.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub enum FunctionCallKind {
    /// This is a normal function call made via a call-like instruction.
    #[default]
    Normal,
    /// This is a tail call made via a jump-like instruction.
    Tail,
}

/// The origin of the target of a function call.
#[derive(Debug)]
pub enum FunctionCallOrigin<'input> {
    /// The definition of the function for a direct call.
    Direct(&'input Function<'input>),
    /// The origin of the function pointer for an indirect call.
    Indirect(FunctionCallIndirectOrigin<'input>),
}

/// The origin of the function pointer for an indirect function call.
#[derive(Debug)]
pub enum FunctionCallIndirectOrigin<'input> {
    /// The function pointer is stored in this variable at the time of the call.
    Variable(&'input Variable<'input>),
    /// The function pointer is stored in one of the caller function's local variables at the time of the call.
    LocalVariable(VariableOffset),
    /// The function origin is stored in one of the caller function's parameters at the time of the call.
    Parameter(ParameterOffset),
    /// The function origin is stored in this member at the time of the call.
    ///
    /// We store this as the unique member offset. This allows for later traversal down the types
    /// in order to locate this exact member if the caller is interested.
    Member(MemberOffset),
}

/// Represents one of the parameters for a function call.
#[derive(Debug, Default)]
pub struct FunctionCallParameter<'input> {
    pub(crate) name: Option<&'input str>,
    pub(crate) ty: Option<TypeOffset>,
    pub(crate) location: Vec<Piece>,
    pub(crate) value: Vec<Piece>,
    pub(crate) data_location: Vec<Piece>,
    pub(crate) data_value: Vec<Piece>,
}

impl<'input> FunctionCallParameter<'input> {
    /// The name of the parameter.
    #[inline]
    pub fn name(&self) -> Option<&'input str> {
        self.name
    }

    /// The type of the parameter.
    ///
    /// Returns `None` if the type is invalid or unknown.
    #[inline]
    pub fn ty<'a>(&self, hash: &'a FileHash<'input>) -> Option<Cow<'a, Type<'input>>> {
        if let Some(ty) = self.ty {
            Type::from_offset(hash, ty)
        } else {
            None
        }
    }

    /// The location where the parameter is passed for the call.
    pub fn location(&self) -> &[Piece] {
        &self.location
    }

    /// The value of the parameter at the time of the call.
    pub fn value(&self) -> &[Piece] {
        &self.value
    }

    /// If the parameter is a reference, the location where the referenced data is stored.
    pub fn data_location(&self) -> &[Piece] {
        &self.data_location
    }

    /// If the parameter is a reference, the value of the referenced data at the time of the call.
    pub fn data_value(&self) -> &[Piece] {
        &self.data_value
    }
}

/// Abstracts over functions vs inlined functions at the details level
#[derive(Debug, Clone, Copy)]
pub enum FunctionInstance<'input> {
    /// This is a non-inlined function
    Normal(&'input FunctionDetails<'input>),
    /// This is an inlined function
    Inlined(&'input InlinedFunction<'input>),
}

impl<'input> FunctionInstance<'input> {
    #[inline]
    fn parameters(&self) -> &'input [Parameter<'input>] {
        match self {
            Self::Normal(f) => f.parameters(),
            Self::Inlined(f) => f.parameters(),
        }
    }

    #[inline]
    fn variables(&self) -> &'input [LocalVariable<'input>] {
        match self {
            Self::Normal(f) => f.variables(),
            Self::Inlined(f) => f.variables(),
        }
    }
}

/// An index of parameters and local variables within a function.
///
/// This requires the function details to be loaded.
pub struct FunctionHash<'input> {
    /// The function being indexed.
    pub function: FunctionInstance<'input>,
    /// All parameters by offset.
    pub parameters_by_offset: HashMap<ParameterOffset, &'input Parameter<'input>>,
    /// All local variables by offset.
    pub local_variables_by_offset: HashMap<VariableOffset, &'input LocalVariable<'input>>,
}

impl<'input> FunctionHash<'input> {
    /// Create a new `FunctionHash` for the given function.
    pub fn new(function: FunctionInstance<'input>) -> Self {
        Self {
            function,
            parameters_by_offset: Self::parameters_by_offset(&function),
            local_variables_by_offset: Self::local_variables_by_offset(&function),
        }
    }

    fn parameters_by_offset(
        function: &FunctionInstance<'input>,
    ) -> HashMap<ParameterOffset, &'input Parameter<'input>> {
        let mut parameters = HashMap::default();
        for parameter in function.parameters() {
            parameters.insert(parameter.offset, parameter);
        }
        parameters
    }

    fn local_variables_by_offset(
        function: &FunctionInstance<'input>,
    ) -> HashMap<VariableOffset, &'input LocalVariable<'input>> {
        let mut local_variables = HashMap::default();
        for local_variable in function.variables() {
            local_variables.insert(local_variable.offset, local_variable);
        }
        local_variables
    }
}
