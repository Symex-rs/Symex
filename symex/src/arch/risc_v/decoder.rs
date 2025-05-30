#![allow(warnings)]

use risc_v_disassembler::{
    ParsedInstruction32,
    Register,
};

use general_assembly::{
    condition::{Condition, Comparison},
    operand::{DataWord, Operand},
    operation::Operation as GAOperation,
};

use super::{
    RISCV,
};
use crate::executor::instruction::Instruction as GAInstruction;

impl InstructionToGAOperations for RISCV {
    // Make sure to change the shift implementation to 6-bits if you want to support RV64I
    fn instruction_to_ga_operations(&self, instr: &ParsedInstruction32) -> Vec<GAOperation> {
        match instr {
            ParsedInstruction32::add (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sub (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::xor (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::or (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::and (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sll (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::srl (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sra (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::slt (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sltu (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::addi (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::xori (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::ori (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::andi (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::slli (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::srli (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::srai (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::slti (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sltiu (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lb (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lh (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lw (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lbu (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lhu (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sb (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sh (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::sw (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::beq (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bne (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::blt (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bge (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bltu (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::bgeu (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::jal (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::jalr (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::lui (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::auipc (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::ecall (inner) => inner.instruction_to_ga_operations(instr),
            ParsedInstruction32::ebreak (inner) => inner.instruction_to_ga_operations(instr),
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

impl Into<Operand> for Register {
    fn local_into(self) -> Operand {
        Operand::Register(match self {
            Register::x0 => "X0".to_owned(),
            Register::x1 => "X1".to_owned(),
            Register::x2 => "X2".to_owned(),
            Register::x3 => "X3".to_owned(),
            Register::x4 => "X4".to_owned(),
            Register::x5 => "X5".to_owned(),
            Register::x6 => "X6".to_owned(),
            Register::x7 => "X7".to_owned(),
            Register::x8 => "X8".to_owned(),
            Register::x9 => "X9".to_owned(),
            Register::x10 => "X10".to_owned(),
            Register::x11 => "X11".to_owned(),
            Register::x12 => "X12".to_owned(),
            Register::x13 => "X13".to_owned(),
            Register::x14 => "X14".to_owned(),
            Register::x15 => "X15".to_owned(),
            Register::x16 => "X16".to_owned(),
            Register::x17 => "X17".to_owned(),
            Register::x18 => "X18".to_owned(),
            Register::x19 => "X19".to_owned(),
            Register::x20 => "X20".to_owned(),
            Register::x21 => "X21".to_owned(),
            Register::x22 => "X22".to_owned(),
            Register::x23 => "X23".to_owned(),
            Register::x24 => "X24".to_owned(),
            Register::x25 => "X25".to_owned(),
            Register::x26 => "X26".to_owned(),
            Register::x27 => "X27".to_owned(),
            Register::x28 => "X28".to_owned(),
            Register::x29 => "X29".to_owned(),
            Register::x30 => "X30".to_owned(),
            Register::x31 => "X31".to_owned(),
        })
    }
}

