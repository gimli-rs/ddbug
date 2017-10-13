use gimli;
use goblin;

use Result;
use file::{dwarf, File};

pub(crate) fn parse(
    input: &[u8],
    path: &str,
    cb: &mut FnMut(&mut File) -> Result<()>,
) -> Result<()> {
    let macho = match goblin::mach::MachO::parse(&input, 0) {
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

    let mut file = File {
        path,
        // TODO
        code: None,
        // TODO
        sections: Vec::new(),
        // TODO
        symbols: Vec::new(),
        units,
    };
    file.normalize();
    cb(&mut file)
}
