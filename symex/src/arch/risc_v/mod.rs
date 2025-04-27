#![allow(warnings)] // Until all the unimplemented!() are implemented

use std::fmt::Display;

use crate::{
    arch::{ArchError, Architecture, SupportedArchitecture},
    executor::{
        hooks::HookContainer,
        instruction::Instruction,
        state::GAState,
    },
    project::dwarf_helper::SubProgramMap,
};

pub mod decoder;
pub mod decoder_implementations;
pub mod timing;

#[derive(Debug, Default, Clone)]
pub struct RISCV {}

impl Architecture for RISCV {
    fn translate<C: crate::Composition>(&self, buff: &[u8], state: &GAState<C>) -> Result<Instruction<C>, ArchError> {
        unimplemented!()
    }
    fn add_hooks<C: crate::Composition>(&self, hooks: &mut HookContainer<C>, sub_program_lookup: &mut SubProgramMap) {
        unimplemented!()
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

impl Into<SupportedArchitecture> for RISCV {
    fn into(self) -> SupportedArchitecture {
        SupportedArchitecture::RISCV(self)
    }
}
