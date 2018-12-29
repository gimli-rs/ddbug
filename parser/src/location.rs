use crate::file::FileHash;
use crate::{Address, Size};

/// A register number.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Register(pub u16);

impl Register {
    /// The name of the register, if known.
    pub fn name(self, hash: &FileHash) -> Option<&'static str> {
        hash.file.get_register_name(self)
    }
}

/// A location within the stack frame.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FrameLocation {
    /// The offset from the frame pointer.
    pub offset: i64,
    /// The size of the value in bits.
    pub bit_size: Size,
}

/// A piece of a value.
// TODO: include the address ranges for which this piece is valid
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Piece {
    /// The offset of the piece within the containing object.
    pub bit_offset: u64,
    /// The size of the piece. If none, then the piece is the complete value.
    pub bit_size: Size,
    /// The location of the piece.
    pub location: Location,
    /// The offset of the piece within the location.
    pub location_offset: u64,
    /// If `true`, then the piece does not have a location.
    /// Instead, `location` is the value of the piece.
    pub is_value: bool,
}

/// A value location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Location {
    /// The value has been optimized away.
    Empty,
    /// A literal address or value.
    Literal {
        /// The literal address or value.
        value: u64,
    },
    /// The value is stored in a register.
    Register {
        /// The register number.
        register: Register,
    },
    /// The value is stored in memory at an offset from an address stored in a register.
    RegisterOffset {
        /// The register number.
        register: Register,
        /// The offset.
        offset: i64,
    },
    /// The value is stored in memory at an offset from the frame base.
    FrameOffset {
        /// The offset.
        offset: i64,
    },
    /// The value is stored in memory at an offset from the CFA.
    CfaOffset {
        /// The offset.
        offset: i64,
    },
    /// The value is stored in memory at an address. This address may need relocation.
    Address {
        /// The offset.
        address: Address,
    },
    /// The value is stored in memory at an offset within TLS.
    TlsOffset {
        /// The offset.
        offset: u64,
    },
    /// The value is more complex than any of the above variants.
    Other,
}

pub(crate) fn registers<'a>(locations: &'a [Piece]) -> impl Iterator<Item = Register> + 'a {
    locations.iter().filter_map(|piece| {
        if piece.is_value {
            return None;
        }
        match piece.location {
            Location::Register { register } => Some(register),
            _ => None,
        }
    })
}

pub(crate) fn frame_locations<'a>(
    locations: &'a [Piece],
) -> impl Iterator<Item = FrameLocation> + 'a {
    locations.iter().filter_map(|piece| {
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
