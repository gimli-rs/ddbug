use gimli;
use goblin::mach;

use std::borrow;

use Result;
use file::{dwarf, File, Section};

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
        let mut name = Vec::with_capacity(section_name.len() + 1);
        name.push(b'_');
        name.push(b'_');
        for ch in &section_name.as_bytes()[1..] {
            name.push(*ch);
        }
        let section_name = name;

        for segment in &macho.segments {
            if let Ok(name) = segment.name() {
                if name == "__DWARF" {
                    for section in segment {
                        if let Ok((section, data)) = section {
                            if let Ok(name) = section.name() {
                                if name.as_bytes() == &*section_name {
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
            }
        }
    }

    let symbols = Vec::new();
    /* FIXME: return these symbols once we can determine their type and size.
    for symbol in macho.symbols() {
        if let Ok((name, nlist)) = symbol {
            if name.len() == 0 {
                continue;
            }
            if (nlist.n_type & mach::symbols::NLIST_TYPE_MASK) != mach::symbols::N_SECT {
                // TODO: handle other types
                continue;
            }
            symbols.push(Symbol {
                name: Some(name.as_bytes()),
                // FIXME: determine from sections
                ty: SymbolType::Function,
                address: nlist.n_value,
                // FIXME:
                size: 0,
            });
        }
    }
    */

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
