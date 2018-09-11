//! A library for parsing debuginfo.
//!
//! ## Example usage
//!
//! ```rust,no_run
//! extern crate ddbug_parser;
//!
//! # let a_file_path = "";
//! ddbug_parser::File::parse(a_file_path, |file| {
//!     for unit in file.units() {
//!         for function in unit.functions() {
//!             if let Some(name) = function.name() {
//!                 println!("{}", name);
//!             }
//!         }
//!     }
//!     Ok(())
//! });
//! ```
#![deny(missing_docs)]

extern crate fnv;
extern crate gimli;
#[macro_use]
extern crate log;
extern crate memmap;
extern crate moria;
extern crate object;
extern crate typed_arena;

mod file;
mod function;
mod namespace;
mod range;
mod source;
mod types;
mod unit;
mod variable;

pub use file::*;
pub use function::*;
pub use namespace::*;
pub use range::*;
pub use source::*;
pub use types::*;
pub use unit::*;
pub use variable::*;

use std::borrow::{Borrow, Cow};
use std::error;
use std::fmt;
use std::io;
use std::result;

/// A parsing error.
#[derive(Debug)]
pub struct Error(pub Cow<'static, str>);

impl error::Error for Error {
    fn description(&self) -> &str {
        self.0.borrow()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&'static str> for Error {
    fn from(s: &'static str) -> Error {
        Error(Cow::Borrowed(s))
    }
}

impl From<String> for Error {
    fn from(s: String) -> Error {
        Error(Cow::Owned(s))
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error(Cow::Owned(format!("IO error: {}", e)))
    }
}

impl From<gimli::Error> for Error {
    fn from(e: gimli::Error) -> Error {
        Error(Cow::Owned(format!("DWARF error: {}", e)))
    }
}

/*
impl From<crate_pdb::Error> for Error {
    fn from(e: crate_pdb::Error) -> Error {
        Error(Cow::Owned(format!("PDB error: {}", e)))
    }
}
*/

/// A parsing result.
pub type Result<T> = result::Result<T, Error>;

mod address {
    use std::u64;

    /// An optional address.
    ///
    /// This is similar to `Option<u64>`, but uses `0` to encode the `None` case.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Address(u64);

    impl Address {
        /// Create a known address value.
        #[inline]
        pub fn new(address: u64) -> Address {
            debug_assert!(Address(address) != Address::none());
            Address(address)
        }

        /// Create an unknown or absent address value.
        #[inline]
        pub fn none() -> Address {
            Address(0)
        }

        /// Return true if the address is unknown or absent.
        #[inline]
        pub fn is_none(self) -> bool {
            self == Self::none()
        }

        /// Return true if the address is known.
        #[inline]
        pub fn is_some(self) -> bool {
            self != Self::none()
        }

        /// Return the address.
        #[inline]
        pub fn get(self) -> Option<u64> {
            if self.is_none() {
                None
            } else {
                Some(self.0)
            }
        }
    }

    impl Default for Address {
        #[inline]
        fn default() -> Self {
            Address::none()
        }
    }
}

pub use address::Address;

mod size {
    use std::u64;

    /// An optional size.
    ///
    /// This is similar to `Option<u64>`, but uses `u64::MAX` to encode the `None` case.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Size(u64);

    impl Size {
        /// Create a known size value.
        #[inline]
        pub fn new(size: u64) -> Size {
            debug_assert!(Size(size) != Size::none());
            Size(size)
        }

        /// Create an unknown or absent size value.
        #[inline]
        pub fn none() -> Size {
            Size(u64::MAX)
        }

        /// Return true if the size is unknown or absent.
        #[inline]
        pub fn is_none(self) -> bool {
            self == Self::none()
        }

        /// Return true if the size is known.
        #[inline]
        pub fn is_some(self) -> bool {
            self != Self::none()
        }

        /// Return the size.
        #[inline]
        pub fn get(self) -> Option<u64> {
            if self.is_none() {
                None
            } else {
                Some(self.0)
            }
        }
    }

    impl Default for Size {
        #[inline]
        fn default() -> Self {
            Size::none()
        }
    }
}

pub use size::Size;
