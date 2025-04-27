use risc_v_disassembler::ParsedInstruction32;

use crate::executor::{instruction::CycleCount, state::GAState};

impl super::RISCV {
    pub fn memory_access(instr: &ParsedInstruction32) -> bool {
        match instr {
            ParsedInstruction32::lb(_)
            | ParsedInstruction32::lh(_)
            | ParsedInstruction32::lw(_)
            | ParsedInstruction32::lbu(_)
            | ParsedInstruction32::lhu(_)
            | ParsedInstruction32::sb(_)
            | ParsedInstruction32::sh(_)
            | ParsedInstruction32::sw(_) => true,
            _ => false,
        }
    }

    // Hippomenes is a single cycle processor, all intructions are guaranteed to take
    // 1 cycle. https://riscv-europe.org/summit/2024/media/proceedings/posters/116_poster.pdf
    pub fn cycle_count_hippomenes<C: crate::Composition>(instr: &ParsedInstruction32) -> CycleCount<C> {
        CycleCount::new(1)
    }
}
