use file::FileHash;
use {Address, Size};

/// A register number.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Register(pub u16);

impl Register {
    /// The name of the register, if known.
    pub fn name(self, hash: &FileHash) -> Option<&'static str> {
        hash.file.get_register_name(self)
    }
}

/// A value location.
// TODO: include the address ranges for which this location is valid
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Location {
    /// The value is a constant.
    Constant {
        /// The constant value.
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
        offset: usize,
        /// The size.
        size: Size,
    },
    /// The value is stored in memory at an offset from the CFA.
    CfaOffset {
        /// The offset.
        offset: usize,
        /// The size.
        size: Size,
    },
    /// The value is stored in memory at a fixed address.
    Address {
        /// The address.
        address: Address,
        /// The size.
        size: Size,
    },
}
