extern crate fnv;
extern crate gimli;
#[macro_use]
extern crate log;
extern crate marksman_escape;
extern crate memmap;
extern crate object;
extern crate panopticon_amd64 as amd64;
extern crate panopticon_core as panopticon;
extern crate typed_arena;

mod code;
mod file;
mod filter;
mod function;
mod namespace;
mod print;
mod range;
mod source;
mod types;
mod unit;
mod variable;

use std::borrow::Borrow;
use std::borrow::Cow;
use std::error;
use std::fmt;
use std::io;
use std::rc::Rc;
use std::result;

use namespace::Namespace;

pub use file::File;
pub use print::file::{diff, print};
pub use print::{DiffPrefix, HtmlPrinter, Printer, TextPrinter};

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

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort {
    None,
    Name,
    Size,
}

impl Default for Sort {
    fn default() -> Self {
        Sort::None
    }
}

#[derive(Debug, Default, Clone)]
pub struct Options<'a> {
    pub print_source: bool,
    pub print_file_address: bool,
    pub print_unit_address: bool,
    pub print_function_calls: bool,
    pub print_function_variables: bool,
    pub inline_depth: usize,
    pub html: bool,

    pub category_file: bool,
    pub category_unit: bool,
    pub category_type: bool,
    pub category_function: bool,
    pub category_variable: bool,

    pub filter_function_inline: Option<bool>,
    pub filter_name: Option<&'a str>,
    pub filter_namespace: Vec<&'a str>,
    pub filter_unit: Option<&'a str>,

    pub sort: Sort,

    pub ignore_added: bool,
    pub ignore_deleted: bool,
    pub ignore_function_address: bool,
    pub ignore_function_size: bool,
    pub ignore_function_inline: bool,
    pub ignore_function_symbol_name: bool,
    pub ignore_variable_address: bool,
    pub ignore_variable_symbol_name: bool,
    pub prefix_map: Vec<(&'a str, &'a str)>,
}

impl<'a> Options<'a> {
    pub fn unit(&mut self, unit: &'a str) -> &mut Self {
        self.filter_unit = Some(unit);
        self
    }

    pub fn name(&mut self, name: &'a str) -> &mut Self {
        self.filter_name = Some(name);
        self
    }

    fn filter_function_inline(&self, inline: bool) -> bool {
        self.filter_function_inline.is_none() || self.filter_function_inline == Some(inline)
    }

    fn filter_name(&self, name: Option<&str>) -> bool {
        self.filter_name.is_none() || self.filter_name == name
    }

    fn filter_namespace(&self, namespace: &Option<Rc<Namespace>>) -> bool {
        self.filter_namespace.is_empty() || {
            match *namespace {
                Some(ref namespace) => namespace.filter(&self.filter_namespace),
                None => false,
            }
        }
    }

    fn prefix_map<'name>(&self, name: &'name str) -> (&'a str, &'name str) {
        for &(old, new) in &self.prefix_map {
            if name.starts_with(old) {
                return (new, &name[old.len()..]);
            }
        }
        ("", name)
    }
}

mod address {
    use std::u64;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub(crate) struct Address(u64);

    impl Address {
        #[inline]
        pub(crate) fn new(address: u64) -> Address {
            debug_assert!(Address(address) != Address::none());
            Address(address)
        }

        #[inline]
        pub(crate) fn none() -> Address {
            Address(0)
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
        pub(crate) fn get(self) -> Option<u64> {
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

pub(crate) use address::Address;

mod size {
    use std::u64;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub(crate) struct Size(u64);

    impl Size {
        #[inline]
        pub(crate) fn new(size: u64) -> Size {
            debug_assert!(Size(size) != Size::none());
            Size(size)
        }

        #[inline]
        pub(crate) fn none() -> Size {
            Size(u64::MAX)
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
        pub(crate) fn get(self) -> Option<u64> {
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

pub(crate) use size::Size;
