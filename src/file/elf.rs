use gimli;
use goblin;
use panopticon;

use std::borrow;
use std::result;

use Result;
use file::{dwarf, CodeRegion, File, Section, Symbol, SymbolType};

pub(crate) fn parse(
    input: &[u8],
    path: &str,
    cb: &mut FnMut(&mut File) -> Result<()>,
) -> Result<()> {
    let elf = match goblin::elf::Elf::parse(&input) {
        Ok(elf) => elf,
        Err(e) => return Err(format!("ELF parse failed: {}", e).into()),
    };

    let machine = match elf.header.e_machine {
        goblin::elf::header::EM_X86_64 => {
            let region = panopticon::Region::undefined("RAM".to_string(), 0xFFFF_FFFF_FFFF_FFFF);
            Some((panopticon::Machine::Amd64, region))
        }
        _ => None,
    };

    let mut code = None;
    if let Some((machine, mut region)) = machine {
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

    let mut sections = Vec::new();
    for sh in &elf.section_headers {
        let name = elf.shdr_strtab
            .get(sh.sh_name)
            .and_then(result::Result::ok)
            .map(|x| borrow::Cow::Owned(x.as_bytes().to_vec()));
        let address = if sh.sh_addr != 0 {
            Some(sh.sh_addr)
        } else {
            None
        };
        let size = sh.sh_size;
        if size != 0 {
            sections.push(Section {
                name,
                segment: None,
                address,
                size,
            });
        }
    }

    let mut symbols = Vec::new();
    for sym in &elf.syms {
        // TODO: handle relocatable objects
        let address = sym.st_value;
        if address == 0 {
            continue;
        }

        let size = sym.st_size;
        if size == 0 {
            continue;
        }

        // TODO: handle STT_FILE
        let ty = match goblin::elf::sym::st_type(sym.st_info) {
            goblin::elf::sym::STT_OBJECT => SymbolType::Variable,
            goblin::elf::sym::STT_FUNC => SymbolType::Function,
            _ => continue,
        };

        let name = elf.strtab.get(sym.st_name).and_then(result::Result::ok).map(str::as_bytes);

        symbols.push(Symbol {
            name,
            ty,
            address,
            size,
        });
    }

    // Code based on 'object' crate
    let get_section = |section_name: &str| -> &[u8] {
        for sh in &elf.section_headers {
            if let Some(Ok(mut name)) = elf.shdr_strtab.get(sh.sh_name) {
                while name.starts_with(".") {
                    name = &name[1..];
                }
                if name == section_name {
                    return &input[sh.sh_offset as usize..][..sh.sh_size as usize];
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

    let mut file = File {
        path,
        code,
        sections,
        symbols,
        units,
    };
    file.normalize();
    cb(&mut file)
}
