use std::cmp;
use std::collections::HashMap;
use std::fs;
use std::io::{self, Write};

mod dwarf;
mod elf;
mod mach;
mod pdb;

use goblin;
use memmap;
use panopticon;

use {Options, Result, Sort};
use function::Function;
use print::{DiffList, DiffState, PrintList, PrintState};
use range::{Range, RangeList};
use types::{Type, TypeOffset};
use unit::Unit;

#[derive(Debug)]
pub(crate) struct CodeRegion {
    pub machine: panopticon::Machine,
    pub region: panopticon::Region,
}

#[derive(Debug)]
pub struct File<'a, 'input> {
    path: &'a str,
    code: Option<CodeRegion>,
    sections: Vec<Section<'input>>,
    units: Vec<Unit<'input>>,
}

impl<'a, 'input> File<'a, 'input> {
    pub fn parse(path: &'a str, cb: &mut FnMut(&mut File) -> Result<()>) -> Result<()> {
        let file = match fs::File::open(path) {
            Ok(file) => file,
            Err(e) => {
                return Err(format!("open failed: {}", e).into());
            }
        };

        let file = match memmap::Mmap::open(&file, memmap::Protection::Read) {
            Ok(file) => file,
            Err(e) => {
                return Err(format!("memmap failed: {}", e).into());
            }
        };

        let input = unsafe { file.as_slice() };
        if input.starts_with(b"Microsoft C/C++ MSF 7.00\r\n\x1a\x44\x53\x00") {
            pdb::parse(input, path, cb)
        } else {
            let mut cursor = io::Cursor::new(input);
            match goblin::peek(&mut cursor) {
                Ok(goblin::Hint::Elf(_)) => elf::parse(input, path, cb),
                Ok(goblin::Hint::Mach(_)) => mach::parse(input, path, cb),
                Ok(_) => Err("unrecognized file format".into()),
                Err(e) => Err(format!("file identification failed: {}", e).into()),
            }
        }
    }

    pub(crate) fn code(&self) -> Option<&CodeRegion> {
        self.code.as_ref()
    }

    fn ranges(&self) -> RangeList {
        let mut ranges = RangeList::default();
        for section in &self.sections {
            // TODO: ignore BSS for size?
            if let Some(range) = section.address() {
                ranges.push(range);
            }
        }
        for unit in &self.units {
            for range in unit.ranges.list() {
                ranges.push(*range);
            }
        }
        ranges.sort();
        ranges
    }

    pub fn print(&self, w: &mut Write, options: &Options) -> Result<()> {
        let hash = FileHash::new(self);
        let mut state = PrintState::new(self, &hash, options);

        if options.category_file {
            state.line(w, |w, _state| {
                write!(w, "file {}", self.path)?;
                Ok(())
            })?;
            state.indent(|state| {
                // TODO: display ranges/size that aren't covered by debuginfo.
                let ranges = self.ranges();
                state.list("addresses", w, &(), ranges.list())?;
                state.line_option_u64(w, "size", ranges.size())?;
                state.list("sections", w, &(), &*self.sections)?;
                Ok(())
            })?;
            writeln!(w, "")?;
        }

        for unit in self.filter_units(options, false) {
            unit.print(w, &mut state, options)?;
        }
        Ok(())
    }

    pub fn diff(w: &mut Write, file_a: &File, file_b: &File, options: &Options) -> Result<()> {
        let hash_a = FileHash::new(file_a);
        let hash_b = FileHash::new(file_b);
        let mut state = DiffState::new(file_a, &hash_a, file_b, &hash_b, options);

        if options.category_file {
            state.line(w, file_a, file_b, |w, _state, x| {
                write!(w, "file {}", x.path)?;
                Ok(())
            })?;
            state.indent(|state| {
                let ranges_a = file_a.ranges();
                let ranges_b = file_b.ranges();
                state.list("addresses", w, &(), ranges_a.list(), &(), ranges_b.list())?;
                state.line_option_u64(w, "size", ranges_a.size(), ranges_b.size())?;
                // TODO: sort sections
                state.list("sections", w, &(), &*file_a.sections, &(), &*file_b.sections)?;
                Ok(())
            })?;
            writeln!(w, "")?;
        }

        state
            .merge(
                w,
                |_state| file_a.filter_units(options, true),
                |_state| file_b.filter_units(options, true),
                |_hash_a, a, _hash_b, b| Unit::cmp_id(a, b, options),
                |w, state, a, b| {
                    Unit::diff(a, b, w, state, options)
                },
                |w, state, a| {
                    if !options.ignore_deleted {
                        a.print(w, state, options)?;
                    }
                    Ok(())
                },
                |w, state, b| {
                    if !options.ignore_added {
                        b.print(w, state, options)?;
                    }
                    Ok(())
                },
            )?;
        Ok(())
    }

    fn filter_units(&self, options: &Options, diff: bool) -> Vec<&Unit> {
        let mut units: Vec<_> = self.units.iter().filter(|a| a.filter(options)).collect();
        match options.sort.with_diff(diff) {
            Sort::None => {}
            Sort::Name => units.sort_by(|a, b| Unit::cmp_id(a, b, options)),
            Sort::Size => units.sort_by(|a, b| Unit::cmp_size(a, b)),
        }
        units
    }
}

#[derive(Debug)]
pub(crate) struct FileHash<'a, 'input>
where
    'input: 'a,
{
    // All functions by address.
    pub functions: HashMap<u64, &'a Function<'input>>,
    // All types by offset.
    pub types: HashMap<TypeOffset, &'a Type<'input>>,
}

impl<'a, 'input> FileHash<'a, 'input> {
    fn new(file: &'a File<'a, 'input>) -> Self {
        FileHash {
            functions: Self::functions(file),
            types: Self::types(file),
        }
    }

    /// Returns a map from address to function for all functions in the file.
    fn functions(file: &'a File<'a, 'input>) -> HashMap<u64, &'a Function<'input>> {
        let mut functions = HashMap::new();
        // TODO: insert symbol table names too
        for unit in &file.units {
            for function in unit.functions.values() {
                if let Some(low_pc) = function.low_pc {
                    // TODO: handle duplicate addresses
                    functions.insert(low_pc, function);
                }
            }
        }
        functions
    }

    /// Returns a map from offset to type for all types in the file.
    fn types(file: &'a File<'a, 'input>) -> HashMap<TypeOffset, &'a Type<'input>> {
        let mut types = HashMap::new();
        for unit in &file.units {
            for (offset, ty) in unit.types.iter() {
                types.insert(*offset, ty);
            }
        }
        types
    }
}

#[derive(Debug)]
pub(crate) struct Section<'input> {
    name: Option<&'input [u8]>,
    address: Option<u64>,
    size: u64,
}

impl<'input> Section<'input> {
    fn address(&self) -> Option<Range> {
        self.address.map(|address| {
            Range {
                begin: address,
                end: address + self.size,
            }
        })
    }

    fn print_name(&self, w: &mut Write) -> Result<()> {
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon-section>")?,
        }
        Ok(())
    }

    fn print_address(&self, w: &mut Write) -> Result<()> {
        if let Some(address) = self.address() {
            write!(w, "address: ")?;
            address.print(w)?;
        }
        Ok(())
    }
}

impl<'input> PrintList for Section<'input> {
    type Arg = ();

    fn print_list(&self, w: &mut Write, state: &mut PrintState, _arg: &()) -> Result<()> {
        state.line(w, |w, _state| self.print_name(w))?;
        state.indent(|state| {
            state.line_option(w, |w, _state| self.print_address(w))?;
            state.line_option_u64(w, "size", Some(self.size))
        })
    }
}

impl<'input> DiffList for Section<'input> {
    fn step_cost() -> usize {
        1
    }

    fn diff_cost(_state: &DiffState, _arg_a: &(), a: &Self, _arg_b: &(), b: &Self) -> usize {
        let mut cost = 0;
        if a.name.cmp(&b.name) != cmp::Ordering::Equal {
            cost += 2;
        }
        cost
    }

    fn diff_list(
        w: &mut Write,
        state: &mut DiffState,
        _arg_a: &(),
        a: &Self,
        _arg_b: &(),
        b: &Self,
    ) -> Result<()> {
        state.line(w, a, b, |w, _state, x| x.print_name(w))?;
        state.indent(|state| {
            state.line_option(w, a, b, |w, _state, x| x.print_address(w))?;
            state.line_option_u64(w, "size", Some(a.size), Some(b.size))
        })
    }
}
