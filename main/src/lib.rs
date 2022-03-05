// Enable some rust 2018 idioms.
#![warn(bare_trait_objects)]
#![warn(unused_extern_crates)]
// Calm down clippy.
#![allow(clippy::new_ret_no_self)]
#![allow(clippy::single_match)]
#![allow(clippy::type_complexity)]

#[macro_use]
extern crate log;

use parser::Namespace;

pub use parser::{Error, File, Result};

mod code;
mod filter;

mod print;
pub use self::print::file::{
    bloat, bloat_id, bloat_index, diff, diff_id, diff_index, print, print_id, print_index,
    print_parent, BloatIndex, DiffIndex, PrintIndex,
};
pub use self::print::{DiffPrefix, HtmlPrinter, Id, Printer, TextPrinter};

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
pub struct Options {
    pub print_source: bool,
    pub print_file_address: bool,
    pub print_unit_address: bool,
    pub print_function_calls: bool,
    pub print_function_instructions: bool,
    pub print_function_variables: bool,
    pub print_function_stack_frame: bool,
    pub print_inlined_function_parameters: bool,
    pub print_variable_locations: bool,
    pub inline_depth: usize,
    pub html: bool,
    pub http: bool,

    pub category_file: bool,
    pub category_unit: bool,
    pub category_type: bool,
    pub category_function: bool,
    pub category_variable: bool,

    pub filter_function_inline: Option<bool>,
    pub filter_name: Option<String>,
    pub filter_namespace: Vec<String>,
    pub filter_unit: Option<String>,

    pub sort: Sort,

    pub ignore_added: bool,
    pub ignore_deleted: bool,
    pub ignore_function_address: bool,
    pub ignore_function_size: bool,
    pub ignore_function_inline: bool,
    pub ignore_function_linkage_name: bool,
    pub ignore_function_symbol_name: bool,
    pub ignore_variable_address: bool,
    pub ignore_variable_linkage_name: bool,
    pub ignore_variable_symbol_name: bool,
    pub prefix_map: Vec<(String, String)>,
}

impl Options {
    pub fn unit(&mut self, unit: &str) -> &mut Self {
        self.filter_unit = Some(unit.into());
        self
    }

    pub fn name(&mut self, name: &str) -> &mut Self {
        self.filter_name = Some(name.into());
        self
    }

    fn filter_function_inline(&self, inline: bool) -> bool {
        self.filter_function_inline.is_none() || self.filter_function_inline == Some(inline)
    }

    fn filter_name(&self, name: Option<&str>) -> bool {
        self.filter_name.is_none() || self.filter_name.as_ref().map(String::as_ref) == name
    }

    fn filter_namespace(&self, namespace: Option<&Namespace>) -> bool {
        self.filter_namespace.is_empty() || {
            match namespace {
                Some(namespace) => namespace.is_within(&self.filter_namespace),
                None => false,
            }
        }
    }

    fn prefix_map<'name>(&self, name: &'name str) -> (&str, &'name str) {
        for (old, new) in &self.prefix_map {
            if name.starts_with(&*old) {
                return (&new, &name[old.len()..]);
            }
        }
        ("", name)
    }
}
