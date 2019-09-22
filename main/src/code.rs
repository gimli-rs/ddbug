use capstone::arch::x86::X86OperandType;
use capstone::arch::ArchOperand;
use capstone::{self, Arch, Capstone, Insn, InsnDetail, InsnGroupType, Mode};

use crate::print::{self, PrintState, ValuePrinter};
use crate::Result;
use parser::{Address, Architecture, File, FunctionDetails, Range, Register};

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
            Architecture::I386 => (Arch::X86, Mode::Mode32),
            Architecture::X86_64 => (Arch::X86, Mode::Mode64),
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

    pub(crate) fn disassembler<'a>(&'a self) -> Option<Disassembler<'a>> {
        Disassembler::new(self, self.arch, self.mode)
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
    let insns = cs.disasm_all(code, addr).ok()?;
    Some(insns.iter().filter_map(|x| call(arch, &cs, &x)).collect())
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

pub(crate) struct Disassembler<'a> {
    code: &'a Code<'a>,
    cs: capstone::Capstone,
}

impl<'a> Disassembler<'a> {
    pub(crate) fn new(code: &'a Code<'a>, arch: Arch, mode: Mode) -> Option<Disassembler<'a>> {
        let mut cs = Capstone::new_raw(arch, mode, capstone::NO_EXTRA_MODE, None).ok()?;
        cs.set_detail(true).ok()?;
        Some(Disassembler { code, cs })
    }

    pub(crate) fn instructions(&'a self, range: Range) -> Option<Instructions<'a>> {
        self.code
            .range(range)
            .and_then(|code| self.cs.disasm_all(code, range.begin).ok())
            .map(|instructions| Instructions { instructions })
    }
}

pub(crate) struct Instructions<'a> {
    instructions: capstone::Instructions<'a>,
}

impl<'a> Instructions<'a> {
    pub(crate) fn iter(&'a self) -> InstructionIterator<'a> {
        let instructions = self.instructions.iter();
        InstructionIterator { instructions }
    }
}

pub(crate) struct InstructionIterator<'a> {
    instructions: capstone::InstructionIterator<'a>,
}

impl<'a> Iterator for InstructionIterator<'a> {
    type Item = Instruction<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.instructions.next().map(|insn| Instruction { insn })
    }
}

pub(crate) struct Instruction<'a> {
    insn: capstone::Insn<'a>,
}

impl<'a> Instruction<'a> {
    pub(crate) fn address(&self) -> Address {
        Address::new(self.insn.address())
    }

    pub(crate) fn print(
        &self,
        state: &mut PrintState,
        d: &Disassembler<'a>,
        f: &FunctionDetails,
        range: Range,
    ) -> Result<()> {
        fn pad_address(w: &mut dyn ValuePrinter) -> Result<()> {
            write!(w, "{:3}   ", "")?;
            Ok(())
        }
        fn pad_mnemonic(w: &mut dyn ValuePrinter) -> Result<()> {
            write!(w, "{:6} ", "")?;
            Ok(())
        }

        let detail = match d.cs.insn_detail(&self.insn) {
            Ok(detail) => detail,
            Err(_) => return Ok(()),
        };
        let arch_detail = detail.arch_detail();

        state.line(|w, _hash| {
            write!(w, "{:3x}:  ", self.insn.address() - range.begin)?;
            if let Some(mnemonic) = self.insn.mnemonic() {
                write!(w, "{:6}", mnemonic)?;
                if let Some(op_str) = self.insn.op_str().filter(|s| !s.is_empty()) {
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
                            debug!("operand count mismatch {:x}", self.insn.address());
                        }
                        write!(w, "{}", op_str)?
                    }
                }
            } else {
                for b in self.insn.bytes() {
                    write!(w, "{:02x} ", b)?;
                }
            }
            Ok(())
        })?;

        let mut first = true;
        for op in arch_detail.operands() {
            let address = if first {
                // HACK: assume only first operand is modified, so calculate it after the instruction
                first = false;
                self.insn.address() + self.insn.bytes().len() as u64
            } else {
                self.insn.address()
            };
            if let Some(imm) = is_imm(&op) {
                if is_jump(&detail) && range.contains(imm) {
                    continue;
                }
                // TODO: lookup variables too
                if let Some(function) = state.hash().functions_by_address.get(&imm) {
                    state.line(|w, _hash| {
                        pad_address(w)?;
                        pad_mnemonic(w)?;
                        write!(w, "0x{:x} = ", imm)?;
                        print::function::print_ref(function, w)
                    })?;
                }
            }
            if let Some(reg) = is_reg(&op) {
                for parameter in f.parameters() {
                    for (range, register) in parameter.registers() {
                        if reg == register && range.contains(address) {
                            state.line(|w, hash| {
                                pad_address(w)?;
                                pad_mnemonic(w)?;
                                print::register::print(register, w, hash)?;
                                write!(w, " = ")?;
                                print::parameter::print_decl(parameter, w, hash)
                            })?;
                        }
                    }
                }
                for variable in f.variables() {
                    for (range, register) in variable.registers() {
                        if reg == register && range.contains(address) {
                            state.line(|w, hash| {
                                pad_address(w)?;
                                pad_mnemonic(w)?;
                                print::register::print(register, w, hash)?;
                                write!(w, " = ")?;
                                print::local_variable::print_decl(variable, w, hash)
                            })?;
                        }
                    }
                }
            }
            if let Some((reg, ofs)) = is_reg_offset(&op) {
                for parameter in f.parameters() {
                    let size = parameter.byte_size(state.hash()).unwrap_or(0) as i64;
                    for (range, register, offset) in parameter.register_offsets() {
                        if reg == register
                            && ofs >= offset
                            && ofs < offset + size
                            && range.contains(address)
                        {
                            state.line(|w, hash| {
                                pad_address(w)?;
                                pad_mnemonic(w)?;
                                write!(w, "[")?;
                                print::register::print(register, w, hash)?;
                                if offset < 0 {
                                    write!(w, " - 0x{:x}", -offset)?;
                                } else if offset > 0 {
                                    write!(w, " + 0x{:x}", offset)?;
                                }
                                write!(w, "] = ")?;
                                // FIXME: print members if ofs != offset || reg.size() < size
                                print::parameter::print_decl(parameter, w, hash)
                            })?;
                        }
                    }
                }
                for variable in f.variables() {
                    let size = variable.byte_size(state.hash()).unwrap_or(0) as i64;
                    for (range, register, offset) in variable.register_offsets() {
                        if reg == register
                            && ofs >= offset
                            && ofs < offset + size
                            && range.contains(address)
                        {
                            state.line(|w, hash| {
                                pad_address(w)?;
                                pad_mnemonic(w)?;
                                write!(w, "[")?;
                                print::register::print(register, w, hash)?;
                                if offset < 0 {
                                    write!(w, " - 0x{:x}", -offset)?;
                                } else if offset > 0 {
                                    write!(w, " + 0x{:x}", offset)?;
                                }
                                write!(w, "] = ")?;
                                // FIXME: print members if ofs != offset || reg.size() < size
                                print::local_variable::print_decl(variable, w, hash)
                            })?;
                        }
                    }
                }
            }
            // TODO: keep track of pointer types, and lookup X86OperandType::Mem offsets
        }

        Ok(())
    }
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

fn is_reg(op: &ArchOperand) -> Option<Register> {
    if let ArchOperand::X86Operand(op) = op {
        if let X86OperandType::Reg(reg) = op.op_type {
            return convert_reg(reg);
        }
        if let X86OperandType::Mem(op) = op.op_type {
            return convert_reg(op.base());
            // TODO: op.index()?
        }
    }
    None
}

fn is_reg_offset(op: &ArchOperand) -> Option<(Register, i64)> {
    if let ArchOperand::X86Operand(op) = op {
        if let X86OperandType::Mem(op) = op.op_type {
            return convert_reg(op.base()).map(|reg| (reg, op.disp()));
        }
    }
    None
}

fn convert_reg(reg: capstone::RegId) -> Option<Register> {
    use capstone::arch::x86::X86Reg::*;
    // FIXME: mapping from capstone to dwarf registers should live elsewhere
    // FIXME: keep track of register width?
    return match reg.0 as u32 {
        X86_REG_RAX | X86_REG_EAX | X86_REG_AX | X86_REG_AH | X86_REG_AL => Some(Register(0)),
        X86_REG_RDX | X86_REG_EDX | X86_REG_DX | X86_REG_DH | X86_REG_DL => Some(Register(1)),
        X86_REG_RCX | X86_REG_ECX | X86_REG_CX | X86_REG_CH | X86_REG_CL => Some(Register(2)),
        X86_REG_RBX | X86_REG_EBX | X86_REG_BX | X86_REG_BH | X86_REG_BL => Some(Register(3)),
        X86_REG_RSI | X86_REG_ESI | X86_REG_SI | X86_REG_SIL => Some(Register(4)),
        X86_REG_RDI | X86_REG_EDI | X86_REG_DI | X86_REG_DIL => Some(Register(5)),
        X86_REG_RBP | X86_REG_EBP | X86_REG_BP | X86_REG_BPL => Some(Register(6)),
        X86_REG_RSP | X86_REG_ESP | X86_REG_SP | X86_REG_SPL => Some(Register(7)),

        X86_REG_R8 | X86_REG_R8D | X86_REG_R8W | X86_REG_R8B => Some(Register(8)),
        X86_REG_R9 | X86_REG_R9D | X86_REG_R9W | X86_REG_R9B => Some(Register(9)),
        X86_REG_R10 | X86_REG_R10D | X86_REG_R10W | X86_REG_R10B => Some(Register(10)),
        X86_REG_R11 | X86_REG_R11D | X86_REG_R11W | X86_REG_R11B => Some(Register(11)),
        X86_REG_R12 | X86_REG_R12D | X86_REG_R12W | X86_REG_R12B => Some(Register(12)),
        X86_REG_R13 | X86_REG_R13D | X86_REG_R13W | X86_REG_R13B => Some(Register(13)),
        X86_REG_R14 | X86_REG_R14D | X86_REG_R14W | X86_REG_R14B => Some(Register(14)),
        X86_REG_R15 | X86_REG_R15D | X86_REG_R15W | X86_REG_R15B => Some(Register(15)),

        X86_REG_XMM0 | X86_REG_YMM0 => Some(Register(17)),
        X86_REG_XMM1 | X86_REG_YMM1 => Some(Register(18)),
        X86_REG_XMM2 | X86_REG_YMM2 => Some(Register(19)),
        X86_REG_XMM3 | X86_REG_YMM3 => Some(Register(20)),
        X86_REG_XMM4 | X86_REG_YMM4 => Some(Register(21)),
        X86_REG_XMM5 | X86_REG_YMM5 => Some(Register(22)),
        X86_REG_XMM6 | X86_REG_YMM6 => Some(Register(23)),
        X86_REG_XMM7 | X86_REG_YMM7 => Some(Register(24)),

        X86_REG_XMM8 | X86_REG_YMM8 => Some(Register(25)),
        X86_REG_XMM9 | X86_REG_YMM9 => Some(Register(26)),
        X86_REG_XMM10 | X86_REG_YMM10 => Some(Register(27)),
        X86_REG_XMM11 | X86_REG_YMM11 => Some(Register(28)),
        X86_REG_XMM12 | X86_REG_YMM12 => Some(Register(29)),
        X86_REG_XMM13 | X86_REG_YMM13 => Some(Register(30)),
        X86_REG_XMM14 | X86_REG_YMM14 => Some(Register(31)),
        X86_REG_XMM15 | X86_REG_YMM15 => Some(Register(32)),

        // Don't need RIP/EIP, there's never variables/parameters there.
        X86_REG_INVALID | X86_REG_RIP | X86_REG_EIP => None,

        _ => {
            debug!("Unsupported x86 register {}", reg.0);
            None
        }
    };
}
