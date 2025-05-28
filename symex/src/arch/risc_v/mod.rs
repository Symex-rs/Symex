#![allow(warnings)] // Until all the unimplemented!() are implemented

use std::fmt::Display;

use anyhow::Context;

use crate::{
    arch::{ArchError, Architecture, ArchitectureOverride, SupportedArchitecture, InterfaceRegister},
    executor::{
        hooks::{HookContainer, PCHook},
        instruction::Instruction,
        state::GAState,
    },
    smt::{SmtExpr, SmtMap},
    trace,
    debug,
    project::dwarf_helper::SubProgramMap,
    Composition,
};


pub mod decoder;
pub mod decoder_implementations;
pub mod timing;

#[derive(Debug, Default, Clone)]
pub struct RISCV {}

impl<Override: ArchitectureOverride> Architecture<Override> for RISCV {
    type ISA = ();
    
    fn translate<C: Composition>(&self, buff: &[u8], state: &GAState<C>) -> Result<Instruction<C>, ArchError> {
        unimplemented!();
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

    fn get_register_name(reg:InterfaceRegister) -> String {
        match reg {
            InterfaceRegister::ProgramCounter => "PC",
            InterfaceRegister::ReturnAddress => "X1"
        }.to_string()
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

impl From<risc_v_disassembler::DisassemblerError> for ArchError{
    fn from(value: risc_v_disassembler::DisassemblerError) -> Self {
        unimplemented!()
    }
}

impl<Override: ArchitectureOverride> From<RISCV> for SupportedArchitecture<Override> {
    fn from(val: RISCV) -> SupportedArchitecture<Override> {
        SupportedArchitecture::RISCV(val)
    }
}
