use gimli;
use goblin::mach;

use std::borrow;
use std::cmp;

use Result;
use file::{dwarf, File, Section, Symbol, SymbolType};

pub(crate) fn parse(
    input: &[u8],
    path: &str,
    cb: &mut FnMut(&mut File) -> Result<()>,
) -> Result<()> {
    let macho = match mach::MachO::parse(&input, 0) {
        Ok(macho) => macho,
        Err(e) => return Err(format!("Mach-O parse failed: {}", e).into()),
    };

    // Code based on 'object' crate
    let get_section = |section_name: &str| -> &[u8] {
        for segment in &macho.segments {
            if let Ok(name) = segment.name() {
                if name == "__DWARF" {
                    for section in segment {
                        if let Ok((section, data)) = section {
                            if let Ok(mut name) = section.name() {
                                while name.starts_with("_") {
                                    name = &name[1..];
                                }
                                if name == section_name {
                                    return data;
                                }
                            }
                        }
                    }
                }
            }
        }
        &[]
    };

    let units = if macho.header.is_little_endian() {
        dwarf::parse(gimli::LittleEndian, get_section)?
    } else {
        dwarf::parse(gimli::BigEndian, get_section)?
    };

    let mut sections = Vec::new();
    for segment in &macho.segments {
        let segment_name = segment.name().ok();
        for section in segment {
            if let Ok((section, _data)) = section {
                // TODO: avoid Cow::Owned
                let name = section.name().ok().map(|x| borrow::Cow::Owned(x.as_bytes().to_vec()));
                let segment_name = segment_name.map(|x| borrow::Cow::Owned(x.as_bytes().to_vec()));
                sections.push(Section {
                    name,
                    segment: segment_name,
                    address: Some(section.addr),
                    size: section.size,
                });
            } else {
                sections.push(Section {
                    name: None,
                    segment: None,
                    address: None,
                    size: 0,
                });
            }
        }
    }

    let mut symbols = Vec::new();
    for symbol in macho.symbols() {
        if let Ok((name, nlist)) = symbol {
            if name.len() == 0 {
                continue;
            }
            if (nlist.n_type & mach::symbols::NLIST_TYPE_MASK) != mach::symbols::N_SECT {
                // TODO: handle other types
                continue;
            }
            if nlist.n_sect == 0 || nlist.n_sect - 1 >= sections.len() {
                continue;
            }
            let section = &sections[nlist.n_sect - 1];
            let ty = if section.segment.as_ref().map(borrow::Cow::as_ref) == Some(b"__TEXT")
                && section.name.as_ref().map(borrow::Cow::as_ref) == Some(b"__text")
            {
                SymbolType::Function
            } else {
                SymbolType::Variable
            };
            symbols.push(Symbol {
                name: Some(name.as_bytes()),
                ty,
                section: nlist.n_sect,
                address: nlist.n_value,
                size: 0,
            });
        }
    }

    {
        // Calculate symbol sizes by sorting and finding the next symbol.
        let mut section_ends = Vec::new();
        for (i, section) in sections.iter().enumerate() {
            section_ends.push(Symbol {
                name: None,
                ty: SymbolType::Variable,
                section: i + 1,
                address: section.address.unwrap_or(0) + section.size,
                size: 0,
            });
        }

        let mut symbol_refs = Vec::with_capacity(symbols.len() + section_ends.len());
        symbol_refs.extend(symbols.iter_mut());
        symbol_refs.extend(section_ends.iter_mut());
        symbol_refs.sort_by(|a, b| {
            let ord = a.section.cmp(&b.section);
            if ord != cmp::Ordering::Equal {
                return ord;
            }
            let ord = a.address.cmp(&b.address);
            if ord != cmp::Ordering::Equal {
                return ord;
            }
            // Place the dummy end of section symbols last.
            (a.name == None).cmp(&(b.name == None))
        });

        for i in 0..symbol_refs.len() {
            let (before, after) = symbol_refs.split_at_mut(i + 1);
            let sym = &mut before[i];
            if sym.name != None {
                if let Some(next) =
                    after.iter().skip_while(|x| x.name != None && x.address == sym.address).next()
                {
                    sym.size = next.address - sym.address;
                }
            }
        }
    }

    let mut file = File {
        path,
        // TODO
        code: None,
        sections,
        symbols,
        units,
    };
    file.normalize();
    cb(&mut file)
}
