#![allow(warnings)] // Until all the unimplemented!() are implemented

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

pub mod decoder;
pub mod decoder_implementations;
pub mod timing;

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
        let instr = risc_v_disassembler::parse(&buff, is_big_endian).map_err(|e| ArchError::ParsingError(e.into(), buffer));

        debug!("PC{:#x} -> Running {:?}", state.memory.get_pc().unwrap().get_constant().unwrap(), instr);
        let instr = instr?;
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
            let value_ptr = match state.memory.get_register("X10") {
                Ok(val) => val,
                Err(e) => return Err(e).context("While resolving address for new symbolic value"),
            };

            let size = (match state.memory.get_register("X11") {
                Ok(val) => val,
                Err(e) => return Err(e).context("While resolving size for new symbolic value"),
            })
            .get_constant()
            .unwrap()
                * 8;
            let name = state.label_new_symbolic("any");
            if size == 0 {
                let register_name = state.architecture.get_register_name(InterfaceRegister::ReturnAddress);
                let ra = state.get_register(register_name.to_owned()).unwrap();
                state.set_register("PC".to_owned(), ra)?;
                return Ok(());
            }
            let symb_value = state.memory.unconstrained(&name, size as u32);
            // We should be able to do this now!
            // TODO: We need to label this with proper variable names if possible.
            //state.marked_symbolic.push(Variable {
            //    name: Some(name),
            //    value: symb_value.clone(),
            //    ty: ExpressionType::Integer(size as usize),
            //});

            match state.memory.set(&value_ptr, symb_value) {
                Ok(_) => {}
                Err(e) => return Err(e).context("While assigning new symbolic value"),
            };

            let register_name = state.architecture.get_register_name(InterfaceRegister::ReturnAddress);
            let ra = state.get_register(register_name.to_owned()).unwrap();
            state.set_register("PC".to_owned(), ra)?;
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
    }

    fn get_register_name(reg: InterfaceRegister) -> String {
        match reg {
            InterfaceRegister::ProgramCounter => "PC",
            InterfaceRegister::ReturnAddress => "X1",
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
