use capstone::arch::x86::X86OperandType;
use capstone::arch::ArchOperand;
use capstone::{self, Arch, Capstone, Insn, InsnDetail, InsnGroupType, Mode};

use crate::print::{self, PrintState, ValuePrinter};
use crate::Result;
use parser::{Error, File, Machine, Range};

// Newtype so that we can convert capstone errors.
struct CodeError(Error);

type CodeResult<T> = std::result::Result<T, CodeError>;

impl From<CodeError> for Error {
    fn from(e: CodeError) -> Error {
        e.0
    }
}

impl From<Error> for CodeError {
    fn from(e: Error) -> CodeError {
        CodeError(e)
    }
}

impl From<capstone::Error> for CodeError {
    fn from(e: capstone::Error) -> CodeError {
        CodeError(format!("Capstone error: {}", e).into())
    }
}

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
        self.range(range)
            .and_then(|code| calls(self.arch, self.mode, code, range.begin))
            .unwrap_or(Vec::new())
    }

    pub(crate) fn print_instructions(&self, state: &mut PrintState, range: Range) -> Result<()> {
        self.range(range)
            .map(|code| print_instructions(state, self.arch, self.mode, code, range))
            .unwrap_or(Ok(()))?;
        Ok(())
    }

    fn range(&self, range: Range) -> Option<&'code [u8]> {
        for region in &self.regions {
            if range.begin >= region.address
                && range.end <= region.address + region.code.len() as u64
            {
                let begin = (range.begin - region.address) as usize;
                let len = (range.end - range.begin) as usize;
                return Some(&region.code[begin..][..len]);
            }
        }
        None
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
    if !is_call(&detail) {
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

fn print_instructions(
    state: &mut PrintState,
    arch: Arch,
    mode: Mode,
    code: &[u8],
    range: Range,
) -> CodeResult<()> {
    let mut cs = Capstone::new_raw(arch, mode, capstone::NO_EXTRA_MODE, None)?;
    cs.set_detail(true)?;
    for insn in cs.disasm_all(code, range.begin)?.iter() {
        print_instruction(state, &cs, &insn, range)?;
    }
    Ok(())
}

fn print_instruction(
    state: &mut PrintState,
    cs: &Capstone,
    insn: &Insn,
    range: Range,
) -> CodeResult<()> {
    fn pad_address(w: &mut dyn ValuePrinter) -> Result<()> {
        write!(w, "{:3}   ", "")?;
        Ok(())
    }
    fn pad_mnemonic(w: &mut dyn ValuePrinter) -> Result<()> {
        write!(w, "{:6} ", "")?;
        Ok(())
    }

    let detail = cs.insn_detail(insn)?;
    let arch_detail = detail.arch_detail();

    state.line(|w, _hash| {
        write!(w, "{:3x}:  ", insn.address() - range.begin)?;
        if let Some(mnemonic) = insn.mnemonic() {
            write!(w, "{:6}", mnemonic)?;
            if let Some(op_str) = insn.op_str().filter(|s| !s.is_empty()) {
                let mut ops = arch_detail.operands().into_iter();
                let mut first = true;
                for op_str in op_str.split(", ") {
                    if first {
                        write!(w, " ")?;
                        first = false;
                    } else {
                        write!(w, ", ")?;
                    }
                    if let Some(op) = ops.next() {
                        if let Some(imm) = is_imm(&op) {
                            if is_jump(&detail) && range.contains(imm) {
                                write!(w, "+{:x}", imm - range.begin)?;
                                continue;
                            }
                        }
                    } else {
                        debug!("operand count mismatch {:x}", insn.address());
                    }
                    write!(w, "{}", op_str)?
                }
            }
        } else {
            for b in insn.bytes() {
                write!(w, "{:02x} ", b)?;
            }
        }
        Ok(())
    })?;

    for op in arch_detail.operands() {
        if let Some(imm) = is_imm(&op) {
            if is_jump(&detail) && range.contains(imm) {
                continue;
            }
            // TODO: lookup variables too
            if let Some(function) = state.hash().functions_by_address.get(&imm) {
                state.line(|w, _hash| {
                    pad_address(w)?;
                    pad_mnemonic(w)?;
                    write!(w, "{:x} = ", imm)?;
                    print::function::print_ref(function, w)
                })?;
            }
        }
        // TODO: find DWARF expressions for registers
    }

    Ok(())
}

fn is_call(detail: &InsnDetail) -> bool {
    detail
        .groups()
        .any(|group| group.0 as u32 == InsnGroupType::CS_GRP_CALL)
}

fn is_jump(detail: &InsnDetail) -> bool {
    detail
        .groups()
        .any(|group| group.0 as u32 == InsnGroupType::CS_GRP_JUMP)
}

fn is_imm(op: &ArchOperand) -> Option<u64> {
    if let ArchOperand::X86Operand(op) = op {
        if let X86OperandType::Imm(imm) = op.op_type {
            return Some(imm as u64);
        }
    }
    None
}
