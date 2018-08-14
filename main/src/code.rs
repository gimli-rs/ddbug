use std::fmt::Debug;

use amd64;
use panopticon;

use parser::{File, Machine, Range};

#[derive(Debug)]
pub(crate) struct CodeRegion {
    machine: panopticon::Machine,
    region: panopticon::Region,
}

impl CodeRegion {
    pub(crate) fn new(file: &File) -> Option<Self> {
        let (machine, mut region) = match file.machine() {
            Machine::X86_64 => {
                let region =
                    panopticon::Region::undefined("RAM".to_string(), 0xFFFF_FFFF_FFFF_FFFF);
                (panopticon::Machine::Amd64, region)
            }
            _ => return None,
        };

        for segment in file.segments() {
            let data = segment.data;
            let address = segment.address;
            let bound = panopticon::Bound::new(address, address + data.len() as u64);
            // FIXME: avoid copy
            let layer = panopticon::Layer::wrap(data.to_vec());
            region.cover(bound, layer);
        }

        Some(CodeRegion { machine, region })
    }

    pub(crate) fn calls(&self, range: Range) -> Vec<Call> {
        match self.machine {
            panopticon::Machine::Amd64 => {
                disassemble_arch::<amd64::Amd64>(&self.region, range, amd64::Mode::Long)
            }
            _ => Vec::new(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct Call {
    pub from: u64,
    pub to: u64,
}

fn disassemble_arch<A>(
    region: &panopticon::Region,
    range: Range,
    cfg: A::Configuration,
) -> Vec<Call>
where
    A: panopticon::Architecture + Debug,
    A::Configuration: Debug,
{
    let mut calls = Vec::new();
    let mut addr = range.begin;
    while addr < range.end {
        let m = match A::decode(region, addr, &cfg) {
            Ok(m) => m,
            Err(e) => {
                error!("failed to disassemble: {}", e);
                return calls;
            }
        };

        for mnemonic in m.mnemonics {
            for instruction in &mnemonic.instructions {
                match *instruction {
                    panopticon::Statement {
                        op: panopticon::Operation::Call(ref call),
                        ..
                    } => match *call {
                        panopticon::Rvalue::Constant { ref value, .. } => {
                            calls.push(Call {
                                from: mnemonic.area.start,
                                to: *value,
                            });
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
            addr = mnemonic.area.end;
        }
    }
    calls
}
