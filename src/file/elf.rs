use goblin;
use object::{self, Object};
use panopticon;

use Result;
use file::{CodeRegion, File};

pub(crate) fn parse(
    input: &[u8],
    path: &str,
    cb: &mut FnMut(&mut File) -> Result<()>,
) -> Result<()> {
    let object = object::ElfFile::parse(input)?;

    let machine = match object.elf().header.e_machine {
        goblin::elf::header::EM_X86_64 => {
            let region = panopticon::Region::undefined("RAM".to_string(), 0xFFFF_FFFF_FFFF_FFFF);
            Some((panopticon::Machine::Amd64, region))
        }
        _ => None,
    };

    let mut code = None;
    if let Some((machine, mut region)) = machine {
        for ph in &object.elf().program_headers {
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

    let mut file = File {
        path,
        code,
        ..Default::default()
    };
    file.parse_object(&object)?;
    file.normalize();
    cb(&mut file)
}
