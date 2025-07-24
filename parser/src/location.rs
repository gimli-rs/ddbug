use crate::file::FileHash;
use crate::{Address, Range, Size};

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
///
/// The value of an object may be split into multiple pieces, each with a different location.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Piece {
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
pub enum Location {
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

pub(crate) fn registers(
    locations: &[(Range, Piece)],
) -> impl Iterator<Item = (Range, Register)> + '_ {
    locations.iter().filter_map(|(range, piece)| {
        if piece.is_value {
            return None;
        }
        match piece.location {
            Location::Register { register } => Some((*range, register)),
            _ => None,
        }
    })
}

pub(crate) fn frame_locations(
    locations: &[(Range, Piece)],
) -> impl Iterator<Item = (Range, FrameLocation)> + '_ {
    locations.iter().filter_map(|(range, piece)| {
        if piece.is_value {
            return None;
        }
        match piece.location {
            // TODO: do we need to distinguish between these?
            Location::FrameOffset { offset } | Location::CfaOffset { offset } => Some((
                *range,
                FrameLocation {
                    offset,
                    bit_size: piece.bit_size,
                },
            )),
            _ => None,
        }
    })
}

pub(crate) fn register_offsets(
    locations: &[(Range, Piece)],
) -> impl Iterator<Item = (Range, Register, i64)> + '_ {
    locations.iter().filter_map(|(range, piece)| {
        if piece.is_value {
            return None;
        }
        match piece.location {
            Location::RegisterOffset { register, offset } => Some((*range, register, offset)),
            _ => None,
        }
    })
}
