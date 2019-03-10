use capstone::arch::x86::X86OperandType;
use capstone::arch::ArchOperand;
use capstone::{self, Arch, Capstone, Insn, InsnGroupType, Mode};
use parser::{File, Machine, Range};

#[derive(Debug)]
pub(crate) struct Code<'code> {
    arch: Arch,
    mode: Mode,
    regions: Vec<Region<'code>>,
}

#[derive(Debug)]
struct Region<'code> {
    address: u64,
    code: &'code [u8],
}

#[derive(Debug)]
pub(crate) struct Call {
    pub from: u64,
    pub to: u64,
}

impl<'code> Code<'code> {
    pub(crate) fn new(file: &File<'code>) -> Option<Self> {
        let (arch, mode) = match file.machine() {
            Machine::X86 => (Arch::X86, Mode::Mode32),
            Machine::X86_64 => (Arch::X86, Mode::Mode64),
            _ => return None,
        };
        let mut regions = Vec::new();
        for segment in file.segments() {
            regions.push(Region {
                address: segment.address,
                code: segment.bytes,
            });
        }
        Some(Code {
            arch,
            mode,
            regions,
        })
    }

    pub(crate) fn calls(&self, range: Range) -> Vec<Call> {
        for region in &*self.regions {
            if range.begin >= region.address
                && range.end <= region.address + region.code.len() as u64
            {
                let begin = (range.begin - region.address) as usize;
                let len = (range.end - range.begin) as usize;
                let code = &region.code[begin..][..len];
                return calls(self.arch, self.mode, code, range.begin).unwrap_or(Vec::new());
            }
        }
        Vec::new()
    }
}

fn calls(arch: Arch, mode: Mode, code: &[u8], addr: u64) -> Option<Vec<Call>> {
    let mut cs = Capstone::new_raw(arch, mode, capstone::NO_EXTRA_MODE, None).ok()?;
    cs.set_detail(true).ok()?;
    Some(
        cs.disasm_all(code, addr)
            .ok()?
            .iter()
            .filter_map(|x| call(arch, &cs, &x))
            .collect(),
    )
}

fn call(arch: Arch, cs: &Capstone, insn: &Insn) -> Option<Call> {
    match arch {
        Arch::X86 => call_x86(cs, insn),
        _ => None,
    }
}

fn call_x86(cs: &Capstone, insn: &Insn) -> Option<Call> {
    let detail = cs.insn_detail(insn).ok()?;
    if !detail
        .groups()
        .any(|group| group.0 as u32 == InsnGroupType::CS_GRP_CALL)
    {
        return None;
    }
    let arch_detail = detail.arch_detail();
    for op in arch_detail.operands() {
        if let ArchOperand::X86Operand(op) = op {
            if let X86OperandType::Imm(imm) = op.op_type {
                return Some(Call {
                    from: insn.address(),
                    to: imm as u64,
                });
            }
        }
    }
    None
}
