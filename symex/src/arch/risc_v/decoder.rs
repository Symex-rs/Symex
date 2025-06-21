use general_assembly::{
    condition::{Comparison, Condition},
    operand::{DataWord, Operand},
    operation::Operation as GAOperation,
};
use risc_v_disassembler::{ParsedInstruction32, Register};

use super::RISCV;
use crate::executor::instruction::Instruction as GAInstruction;

impl RISCV {
    // Make sure to change the shift implementation to 6-bits if you want to support
    // RV64I
    pub fn instruction_to_ga_operations(instr: &ParsedInstruction32) -> Vec<GAOperation> {
        match instr {
            ParsedInstruction32::add(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sub(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::xor(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::or(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::and(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sll(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::srl(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sra(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::slt(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sltu(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::addi(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::xori(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::ori(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::andi(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::slli(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::srli(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::srai(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::slti(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sltiu(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lb(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lh(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lw(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lbu(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lhu(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sb(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sh(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sw(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::beq(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bne(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::blt(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bge(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bltu(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bgeu(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::jal(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::jalr(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lui(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::auipc(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::ecall(inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::ebreak(inner) => inner.instruction_to_ga_operations(instr),
        }
    }
}

pub trait InstructionToGAOperations {
    fn instruction_to_ga_operations(&self, instr: &ParsedInstruction32) -> Vec<GAOperation>;
}

pub(crate) mod sealed {
    pub trait Into<T> {
        fn local_into(self) -> T;
    }
}

use sealed::Into;

impl Into<Operand> for u32 {
    fn local_into(self) -> Operand {
        Operand::Immediate(DataWord::Word32(self))
    }
}

impl Into<Operand> for i32 {
    fn local_into(self) -> Operand {
        Operand::Immediate(DataWord::Word32(self as u32))
    }
}

impl Into<Operand> for u8 {
    fn local_into(self) -> Operand {
        Operand::Immediate(DataWord::Word8(self))
    }
}

impl Into<Operand> for &str {
    fn local_into(self) -> Operand {
        Operand::Register(self.to_ascii_uppercase())
    }
}
