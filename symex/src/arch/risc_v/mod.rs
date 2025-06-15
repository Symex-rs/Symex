//!# RISCV
//!
//!## Supported instructions
//!RISC-V (only RV32I base integer instruction set is currently supported), 
//!for the [Hippomenes architecture](https://github.com/perlindgren/hippomenes).
//!
//!## Cycle counting support
//!The cycle counts are based on the single-cycle, non-pipelined 
//![Hippomenes architecture](https://github.com/perlindgren/hippomenes).
//!
use std::fmt::Display;

use anyhow::Context;

use disarmv7::Parse;
use risc_v_disassembler::{DisassemblerError, ParsedInstruction32, Register};

use crate::{
    arch::{risc_v::decoder::InstructionToGAOperations, ArchError, Architecture, ArchitectureOverride, InterfaceRegister, ParseError, SupportedArchitecture},
    debug,
    executor::{
        hooks::{HookContainer, PCHook},
        instruction::Instruction,
        state::GAState,
    },
    general_assembly::operation::Operation,
    memory,
    project::dwarf_helper::SubProgramMap,
    smt::{ProgramMemory, SmtExpr, SmtMap},
    trace, Composition, Endianness,
};

mod decoder;
mod decoder_implementations;
mod test;
mod timing;

/** 
# RISCV

## Supported instructions
RISC-V (only RV32I base integer instruction set is currently supported), 
for the [Hippomenes architecture](https://github.com/perlindgren/hippomenes).

## Cycle counting support
The cycle counts are based on the single-cycle, non-pipelined 
[Hippomenes architecture](https://github.com/perlindgren/hippomenes).
*/
#[derive(Debug, Default, Clone)]
pub struct RISCV {}

impl<Override: ArchitectureOverride> Architecture<Override> for RISCV {
    type ISA = ();

    fn translate<C: Composition>(&self, buff: &[u8], state: &GAState<C>) -> Result<Instruction<C>, ArchError> {
        let mut buffer = [0; 4];
        for (source, dest) in buff[0..4].iter().zip(buffer.iter_mut()) {
            *dest = *source;
        }
        trace!("decoding, buff : {:?}", buff);
        let endianness = state.memory.program_memory().get_endianness();
        let is_big_endian = match endianness {
            Endianness::Big => true,
            Endianness::Little => false,
        };
        let use_abi_register_names = true;
        let instr = risc_v_disassembler::parse(&buff, is_big_endian, use_abi_register_names).map_err(|e| ArchError::ParsingError(e.into(), buffer));

        debug!("PC{:#x} -> Running {:?}", state.memory.get_pc().unwrap().get_constant().unwrap(), instr);
        let instr = instr?;
        // Hippomenes is a single cycle processor, all intructions are guaranteed to take
        // 1 cycle. https://riscv-europe.org/summit/2024/media/proceedings/posters/116_poster.pdf
        let timing = Self::cycle_count_hippomenes(&instr);
        let ops: Vec<Operation> = Self::instruction_to_ga_operations(&self, &instr);

        let instruction_size = 32; // Need to update the parser to make this automatic and robust

        Ok(Instruction {
            instruction_size: instruction_size as u32,
            operations: ops,
            max_cycle: timing,
            memory_access: Self::memory_access(&instr),
        })
    }

    fn add_hooks<C: crate::Composition>(&self, cfg: &mut HookContainer<C>, map: &mut SubProgramMap) {
        trace!("Adding RISCV hooks");
        let symbolic_sized = |state: &mut GAState<C>| {
            let value_ptr = match state.memory.get_register("A0") {
                Ok(val) => val,
                Err(e) => return Err(e).context("While resolving address for new symbolic value"),
            };

            let size = (match state.memory.get_register("A1") {
                Ok(val) => val,
                Err(e) => return Err(e).context("While resolving size for new symbolic value"),
            })
            .get_constant()
            .unwrap()
                * 8;
            let name = state.label_new_symbolic("any");
            if size == 0 {
                let ra_register_name = state.architecture.get_register_name(InterfaceRegister::ReturnAddress);
                let ra = state.get_register(ra_register_name.to_owned()).unwrap();
                let pc_register_name = state.architecture.get_register_name(InterfaceRegister::ProgramCounter);
                state.set_register(pc_register_name.to_owned(), ra)?;
                return Ok(());
            }
            let symb_value = state.memory.unconstrained(&name, size as u32);

            match state.memory.set(&value_ptr, symb_value) {
                Ok(_) => {}
                Err(e) => return Err(e).context("While assigning new symbolic value"),
            };

            let register_name = state.architecture.get_register_name(InterfaceRegister::ReturnAddress);
            let ra = state.get_register(register_name.to_owned()).unwrap();
            let pc_register_name = state.architecture.get_register_name(InterfaceRegister::ProgramCounter);
            state.set_register(pc_register_name.to_owned(), ra)?;
            Ok(())
        };

        if let Err(_) = cfg.add_pc_hook_regex(map, r"^symbolic_size$", PCHook::Intrinsic(symbolic_sized)) {
            debug!("Could not add symoblic hook, must not contain any calls to `symbolic_size`");
        }
        if let Err(_) = cfg.add_pc_hook_regex(map, r"^symbolic_size<.+>$", PCHook::Intrinsic(symbolic_sized)) {
            debug!("Could not add symoblic hook, must not contain any calls to `symbolic_size<.+>`");
        }

        if let Err(_) = cfg.add_pc_hook_regex(map, r"^HardFault.*$", PCHook::EndFailure("Hardfault")) {
            trace!("Could not add hardfault hook");
        }

        // Writing to zero register should not change the state.
        let write_zero = |state: &mut GAState<C>, _value: C::SmtExpression| {
            trace!("Writing to zero register, no effect");
            Ok(())
        };
        cfg.add_register_write_hook("ZERO".to_owned(), write_zero);

        // Symex increments PC BEFORE executing the instruction, which means that any instruction
        // that reads PC is actually reading PC + instruction size.
        // To compensate for this, we need to tell our instructions to read from register "PC-" instead of "PC",
        // and the hook below will then provide (PC+ instruction size - instruction size) = PC.

        let pc_decrementer = |state: &mut GAState<C>| {
            let instruction_length_in_bytes = state.current_instruction.as_ref().unwrap().instruction_size / 8;
            let current_pc = state.memory.get_pc()?.get_constant().unwrap();
            let new_pc = state.memory.from_u64(current_pc - instruction_length_in_bytes as u64, state.memory.get_word_size()).simplify();
            Ok(new_pc)
        };

        cfg.add_register_read_hook("PC-".to_string(), pc_decrementer);
    }

    fn pre_instruction_loading_hook<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>,
    {
    }

    fn post_instruction_execution_hook<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>,
    {
    }

    fn initiate_state<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>,
    {
        trace!("Setting ZERO register to zero");
        state.memory.set_register("ZERO", state.memory.from_u64(0, 32));
    }

    fn get_register_name(reg: InterfaceRegister) -> String {
        match reg {
            InterfaceRegister::ProgramCounter => "PC",
            InterfaceRegister::ReturnAddress => "RA",
        }
        .to_string()
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
    }
}

impl Display for RISCV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RISC-V")
    }
}

impl From<DisassemblerError> for ParseError {
    fn from(value: DisassemblerError) -> Self {
        match value {
            DisassemblerError::UnsupportedInstructionLength(_) => ParseError::InsufficientInput,
            DisassemblerError::InvalidFunct3(_) => ParseError::MalfromedInstruction,
            DisassemblerError::InvalidFunct7(_) => ParseError::MalfromedInstruction,
            DisassemblerError::InvalidOpcode(_) => ParseError::InvalidInstruction,
            DisassemblerError::InvalidImmediate(_) => ParseError::MalfromedInstruction,
            DisassemblerError::InvalidRegister(_) => ParseError::InvalidRegister,
            DisassemblerError::BitExtensionError(_) => ParseError::Generic("Bit extension error."),
            DisassemblerError::BitExtractionError(_) => ParseError::Generic("Bit extraction error."),
        }
    }
}

impl<Override: ArchitectureOverride> From<RISCV> for SupportedArchitecture<Override> {
    fn from(val: RISCV) -> SupportedArchitecture<Override> {
        SupportedArchitecture::RISCV(val)
    }
}
