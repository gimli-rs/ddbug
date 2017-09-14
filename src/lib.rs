extern crate gimli;
extern crate goblin;
#[macro_use]
extern crate log;
extern crate memmap;
extern crate panopticon_amd64 as amd64;
extern crate panopticon_core as panopticon;
extern crate pdb as crate_pdb;

mod file;
mod function;
mod namespace;
mod print;
mod range;
mod types;
mod variable;
mod unit;

use std::borrow::Borrow;
use std::borrow::Cow;
use std::error;
use std::fmt;
use std::io;
use std::result;
use std::rc::Rc;

use namespace::Namespace;

pub use file::File;

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

impl From<crate_pdb::Error> for Error {
    fn from(e: crate_pdb::Error) -> Error {
        Error(Cow::Owned(format!("PDB error: {}", e)))
    }
}

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
    pub print_file_address: bool,
    pub print_unit_address: bool,
    pub print_function_calls: bool,
    pub print_function_variables: bool,
    pub inline_depth: usize,

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

    fn filter_name(&self, name: Option<&[u8]>) -> bool {
        self.filter_name.is_none() || self.filter_name.map(str::as_bytes) == name
    }

    fn filter_namespace(&self, namespace: &Option<Rc<Namespace>>) -> bool {
        self.filter_namespace.is_empty() || {
            match *namespace {
                Some(ref namespace) => namespace.filter(&self.filter_namespace),
                None => false,
            }
        }
    }
}
