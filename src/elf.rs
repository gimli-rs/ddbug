use dwarf;
use gimli;
use goblin;
use panopticon;

use super::{CodeRegion, File, Result};

pub(crate) fn parse(
    input: &[u8],
    path: &str,
    cb: &mut FnMut(&mut File) -> Result<()>,
) -> Result<()> {
    let elf = match goblin::elf::Elf::parse(&input) {
        Ok(elf) => elf,
        Err(e) => return Err(format!("ELF parse failed: {}", e).into()),
    };

    let machine = elf.header.e_machine;
    let region = match machine {
        goblin::elf::header::EM_X86_64 => {
            Some(panopticon::Region::undefined("RAM".to_string(), 0xFFFF_FFFF_FFFF_FFFF))
        }
        _ => None,
    };

    let mut code = None;
    if let Some(mut region) = region {
        for ph in &elf.program_headers {
            if ph.p_type == goblin::elf::program_header::PT_LOAD {
                let offset = ph.p_offset;
                let size = ph.p_filesz;
                let addr = ph.p_vaddr;
                if offset as usize <= input.len() {
                    let input = &input[offset as usize..];
                    if size as usize <= input.len() {
                        let bound = panopticon::Bound::new(addr, addr + size);
                        let layer = panopticon::Layer::wrap(input[..size as usize].to_vec());
                        region.cover(bound, layer);
                        debug!("loaded program header addr {:#x} size {:#x}", addr, size);
                    } else {
                        debug!("invalid program header size {}", size);
                    }
                } else {
                    debug!("invalid program header offset {}", offset);
                }
            }
        }
        code = Some(CodeRegion { machine, region });
    }

    // Code based on 'object' crate
    let get_section = |section_name: &str| -> &[u8] {
        for header in &elf.section_headers {
            if let Ok(name) = elf.shdr_strtab.get(header.sh_name) {
                if name == section_name {
                    return &input[header.sh_offset as usize..][..header.sh_size as usize];
                }
            }
        }
        &[]
    };

    let units = match elf.header.e_ident[goblin::elf::header::EI_DATA] {
        goblin::elf::header::ELFDATA2LSB => dwarf::parse(gimli::LittleEndian, get_section)?,
        goblin::elf::header::ELFDATA2MSB => dwarf::parse(gimli::BigEndian, get_section)?,
        _ => return Err("unknown endianity".into()),
    };

    let mut file = File { path, code, units };
    cb(&mut file)
}
