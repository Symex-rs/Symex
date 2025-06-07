//! Defines armv6 hooks, instruction translation and timings.

use std::fmt::Display;

use armv6_m_instruction_parser::Error;

use crate::{
    arch::{ArchError, Architecture, ArchitectureOverride, ParseError, SupportedArchitecture, InterfaceRegister},
    executor::{hooks::PCHook, state::GAState},
    smt::{SmtExpr, SmtMap},
    trace,
    Composition,
};

pub mod decoder;
pub mod timing;

/// Type level denotation for the
/// [Armv6-M](https://developer.arm.com/documentation/ddi0419/latest/) ISA.
#[derive(Clone, Copy, Debug)]
pub struct ArmV6M {}

impl<Override: ArchitectureOverride> Architecture<Override> for ArmV6M {
    type ISA = armv6_m_instruction_parser::instructons::Operation;

    fn initiate_state<C>(state: &mut GAState<C>)
    where
        C: crate::Composition<ArchitectureOverride = Override>,
    {
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

    fn get_register_name(reg:InterfaceRegister) -> String {
        match reg {
            InterfaceRegister::ProgramCounter => "PC",
            InterfaceRegister::ReturnAddress => "LR"
        }.to_string()
    }

    #[allow(clippy::cast_possible_truncation)]
    fn add_hooks<C: crate::Composition>(&self, cfg: &mut crate::executor::hooks::HookContainer<C>, map: &mut crate::project::dwarf_helper::SubProgramMap) {
        let symbolic_sized = |state: &mut GAState<_>| {
            let value_ptr = state.get_register("R0".to_owned())?;
            let size_expr: C::SmtExpression = state.get_register("R1".to_owned())?;
            let size: u64 = size_expr.get_constant().unwrap() * 8;
            trace!("trying to create symbolic: addr: {:?}, size: {}", value_ptr, size);
            let name = state.label_new_symbolic("any");
            let memory: &mut C::Memory = &mut state.memory;

            let symb_value = memory.unconstrained(&name, size as u32);
            //state.marked_symbolic.push(Variable {
            //    name: Some(name),
            //    value: symb_value.clone(),
            //    ty: ExpressionType::Integer(size as usize),
            //});
            memory.set(&value_ptr, symb_value)?;

            let lr = state.get_register("LR".to_owned())?;
            state.set_register("PC".to_owned(), lr)?;
            Ok(())
        };

        cfg.add_pc_hook_regex(map, r"^symbolic_size<.+>$", PCHook::Intrinsic(symbolic_sized))
            .expect("Symbol not found in symtab");

        let read_pc = |state: &mut GAState<C>| {
            let two = state.memory.from_u64(1, 32);
            let pc = state.get_register("PC".to_owned()).unwrap();
            Ok(pc.add(&two))
        };

        let write_pc = |state: &mut GAState<C>, value: C::SmtExpression| state.set_register("PC".to_owned(), value);

        cfg.add_register_read_hook("PC+".to_owned(), read_pc);
        cfg.add_register_write_hook("PC+".to_owned(), write_pc);

        // reset always done
        let read_reset_done = |state: &mut GAState<C>, _addr| {
            let value = state.memory.from_u64(0xffff_ffff, 32);
            Ok(value)
        };
        cfg.add_memory_read_hook(0x4000c008, read_reset_done);
    }

    fn translate<C: crate::Composition>(buff: &[u8], _state: &mut GAState<C>) -> Result<crate::executor::instruction::Instruction<C>, ArchError> {
        let mut buffer = [0; 4];
        for (source, dest) in buff[0..4].iter().zip(buffer.iter_mut()) {
            *dest = *source;
        }
        let ret = armv6_m_instruction_parser::parse(buff).map_err(|e| map_err(e, buffer))?;
        let to_exec = Self::expand(ret);
        Ok(to_exec)
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
    //        ArmIsa::ArmV6M => Ok(Some(ArmV6M {})),
    //        ArmIsa::ArmV7EM => Ok(None),
    //    }
    //}

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
    }

    fn nan_encoding(ty: general_assembly::extension::ieee754::OperandType) -> u64 {
        unimplemented!("No support for floating point arithmetic")
    }
}

impl Display for ArmV6M {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ARMv6-M")
    }
}

fn map_err(err: Error, data: [u8; 4]) -> ArchError {
    ArchError::ParsingError(
        match err {
            Error::InsufficientInput => ParseError::InvalidRegister,
            Error::Malfromed32BitInstruction => ParseError::MalfromedInstruction,
            Error::Invalid32BitInstruction => ParseError::InvalidInstruction("Invalid 32 bit".to_string()),
            Error::InvalidOpCode => ParseError::InvalidInstruction("Invalid opcode".to_string()),
            Error::Unpredictable => ParseError::Unpredictable,
            Error::InvalidRegister => ParseError::InvalidRegister,
            Error::InvalidCondition => ParseError::InvalidCondition,
        },
        data,
    )
}

impl<Override: ArchitectureOverride> From<ArmV6M> for SupportedArchitecture<Override> {
    fn from(val: ArmV6M) -> SupportedArchitecture<Override> {
        SupportedArchitecture::Armv6M(val)
    }
}
