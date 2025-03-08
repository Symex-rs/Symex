use std::fmt::Display;

use decoder::Convert;
use disarmv7::prelude::{Operation as V7Operation, *};
use general_assembly::operation::Operation;

use crate::{
    arch::{ArchError, Architecture, ParseError, SupportedArchitecture},
    debug,
    executor::{
        hooks::{HookContainer, PCHook},
        instruction::Instruction,
        state::GAState,
    },
    project::dwarf_helper::SubProgramMap,
    smt::{SmtExpr, SmtMap},
};

//#[rustfmt::skip]
pub mod compare;
pub mod decoder;
#[cfg(test)]
pub mod test;
pub mod timing;

/// Type level denotation for the ARMV7-EM ISA.
#[derive(Debug, Default, Clone)]
pub struct ArmV7EM {}

impl Architecture for ArmV7EM {
    fn add_hooks<C: crate::Composition>(&self, cfg: &mut HookContainer<C>, map: &mut SubProgramMap) {
        let symbolic_sized = |state: &mut GAState<C>| {
            let value_ptr = state.memory.get_register("R0")?;
            let size = state.memory.get_register("R1")?.get_constant().unwrap() * 8;
            let name = state.label_new_symbolic("any");
            let symb_value = state.memory.unconstrained(&name, size as usize);
            // We should be able to do this now!
            // TODO: We need to label this with proper variable names if possible.
            //state.marked_symbolic.push(Variable {
            //    name: Some(name),
            //    value: symb_value.clone(),
            //    ty: ExpressionType::Integer(size as usize),
            //});
            state.memory.set(&value_ptr, symb_value)?;

            let lr = state.get_register("LR".to_owned())?;
            state.set_register("PC".to_owned(), lr)?;
            Ok(())
        };

        let _ = cfg.add_pc_hook_regex(map, r"^symbolic_size<.+>$", PCHook::Intrinsic(symbolic_sized));

        // §B1.4 Specifies that R[15] => Addr(Current instruction) + 4
        //
        // This can be translated in to
        //
        // PC - Size(prev instruction) / 8 + 4
        // as PC points to the next instruction, we
        //
        //
        // Or we can simply take the previous PC + 4.
        let read_pc = |state: &mut GAState<C>| {
            let new_pc = state.memory.from_u64(state.last_pc + 4, state.memory.get_word_size()).simplify();
            Ok(new_pc)
        };

        let read_primask = |state: &mut GAState<C>| {
            let primask: C::SmtExpression = state.memory.from_u64(0, state.memory.get_word_size()).simplify();
            Ok(primask)
        };

        let write_primask = |_state: &mut GAState<C>, _| {
            panic!("Cannot write to PRIMASK");
        };

        let read_sp = |state: &mut GAState<C>| {
            let two = state.memory.from_u64((!(0b11u32)) as u64, 32);
            let sp = state.get_register("SP".to_owned()).unwrap();
            let sp = sp.simplify();
            Ok(sp.and(&two))
        };

        let write_pc = |state: &mut GAState<C>, value| state.set_register("PC".to_owned(), value);
        let write_sp = |state: &mut GAState<C>, value: C::SmtExpression| {
            state.set_register("SP".to_string(), value.and(&state.memory.from_u64((!(0b11u32)) as u64, 32)))?;
            let sp = state.get_register("SP".to_owned()).unwrap();
            let sp = sp.simplify();
            state.set_register("SP".to_owned(), sp)
        };

        cfg.add_register_read_hook("PC+".to_string(), read_pc);
        cfg.add_register_read_hook("PRIMASK".to_string(), read_primask);
        cfg.add_register_write_hook("PRIMASK".to_string(), write_primask);
        cfg.add_register_write_hook("PC+".to_owned(), write_pc);
        cfg.add_register_read_hook("SP&".to_owned(), read_sp);
        cfg.add_register_write_hook("SP&".to_owned(), write_sp);

        // reset always done
        let read_reset_done = |state: &mut GAState<C>, _addr| {
            let value = state.memory.from_u64(0xffff_ffff, 32);
            Ok(value)
        };
        cfg.add_memory_read_hook(0x4000c008, read_reset_done);
    }

    fn translate<C: crate::Composition>(&self, buff: &[u8], state: &GAState<C>) -> Result<Instruction<C>, ArchError> {
        let mut buff: disarmv7::buffer::PeekableBuffer<u8, _> = buff.iter().cloned().into();

        let instr = V7Operation::parse(&mut buff).map_err(|e| ArchError::ParsingError(e.into()))?;
        debug!("PC{:#x} -> Running {:?}", state.last_pc, instr.1);
        let timing = Self::cycle_count_m4_core(&instr.1);
        let ops: Vec<Operation> = instr.clone().convert(state.get_in_conditional_block());

        Ok(Instruction {
            instruction_size: instr.0 as u32,
            operations: ops,
            max_cycle: timing,
            memory_access: Self::memory_access(&instr.1),
        })
    }

    //fn discover(file: &File<'_>) -> Result<Option<Self>, ArchError> {
    //    let f = match file {
    //        File::Elf32(f) => Ok(f),
    //        _ => Err(ArchError::IncorrectFileType),
    //    }?;
    //    let section = match f.section_by_name(".ARM.attributes") {
    //        Some(section) => Ok(section),
    //        None => Err(ArchError::MissingSection(".ARM.attributes")),
    //    }?;
    //    let isa = arm_isa(&section)?;
    //    match isa {
    //        ArmIsa::ArmV6M => Ok(None),
    //        ArmIsa::ArmV7EM => Ok(Some(ArmV7EM::default())),
    //    }
    //}

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
    }
}

impl Display for ArmV7EM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ARMv7-M")
    }
}

impl From<disarmv7::ParseError> for ParseError {
    fn from(value: disarmv7::ParseError) -> Self {
        match value {
            disarmv7::ParseError::Undefined => ParseError::InvalidInstruction,
            disarmv7::ParseError::ArchError(aerr) => match aerr {
                disarmv7::prelude::arch::ArchError::InvalidCondition => ParseError::InvalidCondition,
                disarmv7::prelude::arch::ArchError::InvalidRegister(_) => ParseError::InvalidRegister,
                disarmv7::prelude::arch::ArchError::InvalidField(_) => ParseError::MalfromedInstruction,
            },
            disarmv7::ParseError::Unpredictable => ParseError::Unpredictable,
            disarmv7::ParseError::Invalid16Bit(_) | disarmv7::ParseError::Invalid32Bit(_) => ParseError::InvalidInstruction,
            disarmv7::ParseError::InvalidField(_) => ParseError::MalfromedInstruction,
            disarmv7::ParseError::Incomplete32Bit => ParseError::InsufficientInput,
            disarmv7::ParseError::InternalError(info) => ParseError::Generic(info),
            disarmv7::ParseError::IncompleteParser => ParseError::Generic("Encountered instruction that is not yet supported."),
            disarmv7::ParseError::InvalidCondition => ParseError::InvalidCondition,
            disarmv7::ParseError::IncompleteProgram => ParseError::InsufficientInput,
            disarmv7::ParseError::InvalidRegister(_) => ParseError::InvalidRegister,
            disarmv7::ParseError::PartiallyParsed(error, _) => (*error).into(),
            disarmv7::ParseError::InvalidFloatingPointRegister(_) => ParseError::InvalidRegister,
            disarmv7::ParseError::InvalidRoundingMode(_) => ParseError::InvalidRoundingMode,
        }
    }
}

impl Into<SupportedArchitecture> for ArmV7EM {
    fn into(self) -> SupportedArchitecture {
        SupportedArchitecture::Armv7EM(self)
    }
}
