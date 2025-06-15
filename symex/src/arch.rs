//! Defines a generic architecture
//!
//! An architecture is in the scope of this crate
//! something that defines a instruction set that
//! can be translated in to general_assembly [`Instruction`]s.
//! Moreover the architecture may define a few
//! architecture specific hooks.

pub mod arm;
pub mod risc_v;
/// Defines discovery behaviour for the architectures.
pub mod discover;

use std::fmt::{Debug, Display};

use arm::{v6::ArmV6M, v7::ArmV7EM};
use risc_v::RISCV;
use thiserror::Error;

use crate::{
    executor::{hooks::HookContainer, instruction::Instruction, state::GAState},
    initiation::NoArchOverride,
    project::dwarf_helper::SubProgramMap,
    Composition,
};

#[derive(Debug, Eq, PartialEq, PartialOrd, Clone, Error)]
/// General architecture related errors.
pub enum ArchError {
    /// Thrown when an unsupported architecture is requested.
    #[error("Tried to execute code for an unsupported architecture")]
    UnsupportedArchitechture,

    /// Thrown when an unsupported file type is used.
    #[error("Tried to execute code from a non elf file.")]
    IncorrectFileType,

    /// Thrown when the binary files fields are malformed.
    #[error("Tried to read a malformed section.")]
    MalformedSection,

    /// Thrown when a specific required section does not exist in the binary
    #[error("Elf file missing critical section {0}.")]
    MissingSection(&'static str),

    /// Thrown when a different module errors and that error is not convertible
    /// in to an [`ArchError`]
    #[error("Generic archerror : {0}.")]
    ImplementorStringError(&'static str),

    /// Thrown when something goes wrong during instruction parsing.
    #[error("Error occurred while parsing. {1:?} => {0:?}")]
    ParsingError(ParseError, [u8; 4]),
}

#[derive(Debug, Eq, PartialEq, PartialOrd, Clone, Error)]
pub enum ParseError {
    /// Input not long enough for an instruction.
    #[error("Insufficient input")]
    InsufficientInput,

    /// 32 bit instruction not long enough.
    #[error("Tried to parse a malformed instruction.")]
    MalfromedInstruction,

    /// Opcode not matching valid 32 bit instruction.
    #[error("Instruction not supported in the parser.")]
    InvalidInstruction,

    /// This instruction causes unpredictable behaviour.
    #[error("Instruction defined as unpredictable.")]
    Unpredictable,

    /// Trying to access an invalid register.
    #[error("Parser encountered an invalid register.")]
    InvalidRegister,

    /// Invalid condition code used.
    #[error("Parser encountered an invalid condition.")]
    InvalidCondition,

    /// IEEE 754 invalid rounding mode requested.
    #[error("Requested an invalid roudning mode.")]
    InvalidRoundingMode,

    /// A generic parsing error.
    #[error("Parser encountered some unspecified error.")]
    Generic(&'static str),
}

/// Enumerates all of the registers required to be compatible with the 
/// [`general_assembly`] crate.
/// 
/// These registers are used to define architecture-specific mappings for 
/// general assembly instructions and operations.
#[derive(Debug, Clone)]
pub enum InterfaceRegister {
    /// The program counter register, likely "PC"
    ProgramCounter,
    /// The return address register, "LR" on ARM
    ReturnAddress,
}

/// Enumerates the discoverable machine code formats.
///
/// # Note
///
/// One might add support for other formats using the [`Architecture`] trait
/// with the caveat that they cannot be automatically discovered.
#[derive(Debug, Clone)]
pub enum SupportedArchitecture<Override: ArchitectureOverride> {
    Armv7EM(ArmV7EM),
    Armv6M(ArmV6M),
    RISCV(RISCV),
    Override(Override),
}

/// This trait allows an architecture to be used as an architecture override.
pub trait ArchitectureOverride: Architecture<Self> + Clone + Default {
    /// Checks if the  value is an armv7em override.
    ///
    /// If so, it returns the underlying representation.
    
    fn as_riscv(&mut self) -> Option<&mut RISCV> {
        None
    }
    fn as_arm_v7(&mut self) -> Option<&mut ArmV7EM> {
        None
    }
    fn as_arm_v6(&mut self) -> Option<&mut ArmV6M> {
        None
    }
}
#[derive(Debug, Clone, Default)]
pub struct NoArchitectureOverride;
impl ArchitectureOverride for NoArchitectureOverride {}

/// A generic architecture
///
/// Denotes that the implementer can be treated as an architecture in this
/// crate.
pub trait Architecture<Override: ArchitectureOverride>: Debug + Display + Into<SupportedArchitecture<Override>> {
    type ISA: Sized + Debug;
    /// Converts a slice of bytes to an [`Instruction`]
    fn translate<C>(&self, buff: &[u8], state: &GAState<C>) -> Result<Instruction<C>, ArchError>
    where
        C: Composition<ArchitectureOverride = Override>;

    /// Adds the architecture specific hooks to the [`HookContainer`]
    fn add_hooks<C>(&self, hooks: &mut HookContainer<C>, sub_program_lookup: &mut SubProgramMap)
    where
        C: Composition<ArchitectureOverride = Override>;

    /// Allows the architecture to define behaviour that must happen befor an
    /// instruction is executed.
    fn pre_instruction_loading_hook<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>;

    /// Allows the architecture to define behaviour that must happen after an
    /// instruction is executed.
    fn post_instruction_execution_hook<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>;

    /// Initiates the [`GAState`] to support execution.
    fn initiate_state<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>;

    /// Architecture dependent register names required by general assembly.
    fn get_register_name(reg: InterfaceRegister) -> String;

    /// Creates a new instance of the architecture
    fn new() -> Self
    where
        Self: Sized;
}

impl Architecture<Self> for NoArchitectureOverride {
    type ISA = ();

    fn new() -> Self
        where
            Self: Sized {
        Self
    }
    /// Converts a slice of bytes to an [`Instruction`]
    fn translate<C: Composition>(&self, buff: &[u8], state: &GAState<C>) -> Result<Instruction<C>, ArchError> {
        unimplemented!("NoArchitectureOverride is not an architecture. Runtime checks failed.");
    }

    /// Adds the architecture specific hooks to the [`HookContainer`]
    fn add_hooks<C: Composition>(&self, hooks: &mut HookContainer<C>, sub_program_lookup: &mut SubProgramMap) {
        unimplemented!("NoArchitectureOverride is not an architecture. Runtime checks failed.");
    }

    fn pre_instruction_loading_hook<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Self>,
    {
        unimplemented!("NoArchitectureOverride is not an architecture. Runtime checks failed.");
    }

    fn post_instruction_execution_hook<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Self>,
    {
        unimplemented!("NoArchitectureOverride is not an architecture. Runtime checks failed.");
    }

    fn initiate_state<C>(state: &mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Self>,
    {
        unimplemented!("NoArchitectureOverride is not an architecture. Runtime checks failed.");
    }

    fn get_register_name(reg: InterfaceRegister) -> String 
    {
        unimplemented!("NoArchitectureOverride is not an architecture. Runtime checks failed.");
    }
}

impl<Override: ArchitectureOverride> SupportedArchitecture<Override> {
    /// Converts a slice of bytes to an [`Instruction`]
    pub fn translate<C>(&self, buff: &[u8], state: &GAState<C>) -> Result<Instruction<C>, ArchError>
    where
        C: Composition<ArchitectureOverride = Override>,
    {
        match self {
            Self::Armv6M(a) => a.translate(buff, state),
            Self::Armv7EM(a) => a.translate(buff, state),
            Self::RISCV(a) => a.translate(buff, state),
            Self::Override(o) => o.translate(buff, state),
        }
    }

    /// Adds the architecture specific hooks to the [`HookContainer`]
    pub fn add_hooks<C>(&self, hooks: &mut HookContainer<C>, sub_program_lookup: &mut SubProgramMap)
    where
        C: Composition<ArchitectureOverride = Override>,
    {
        match self {
            Self::Armv6M(a) => a.add_hooks(hooks, sub_program_lookup),
            Self::Armv7EM(a) => a.add_hooks(hooks, sub_program_lookup),
            Self::RISCV(a) => a.add_hooks(hooks, sub_program_lookup),
            Self::Override(o) => o.add_hooks(hooks, sub_program_lookup),
        }
    }

    /// Allows the architecture to define behaviour that must happen befor an
    /// instruction is executed.
    pub fn pre_instruction_loading_hook<C>(&self) -> fn(&mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>,
    {
        match self {
            Self::Armv6M(_) => ArmV6M::pre_instruction_loading_hook,
            Self::Armv7EM(_) => ArmV7EM::pre_instruction_loading_hook,
            Self::RISCV(_) => RISCV::pre_instruction_loading_hook,
            Self::Override(_) => C::ArchitectureOverride::pre_instruction_loading_hook,
        }
    }

    /// Allows the architecture to define behaviour that must happen after an
    /// instruction is executed.
    pub fn post_instruction_execution_hook<C>(&self) -> fn(&mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>,
    {
        match self {
            Self::Armv6M(_) => ArmV6M::post_instruction_execution_hook,
            Self::Armv7EM(_) => ArmV7EM::post_instruction_execution_hook,
            Self::RISCV(_) => RISCV::post_instruction_execution_hook,
            Self::Override(_) => C::ArchitectureOverride::post_instruction_execution_hook,
        }
    }

    pub fn initiate_state<C>(&self) -> fn(&mut GAState<C>)
    where
        C: Composition<ArchitectureOverride = Override>,
    {
        match self {
            Self::Armv6M(_) => ArmV6M::initiate_state,
            Self::Armv7EM(_) => ArmV7EM::initiate_state,
            Self::RISCV(_) => RISCV::initiate_state,
            Self::Override(_) => C::ArchitectureOverride::initiate_state,
        }
    }

    pub fn get_register_name(&self, reg:InterfaceRegister) -> String
    {
        match self {
            Self::Armv6M(_) => <ArmV6M as Architecture<Override>>::get_register_name(reg),
            Self::Armv7EM(_) => <ArmV7EM as Architecture<Override>>::get_register_name(reg),
            Self::RISCV(_) => <RISCV as Architecture<Override>>::get_register_name(reg),
            Self::Override(_) => Override::get_register_name(reg),
        }
    }
    
    fn as_riscv(&mut self) -> &mut RISCV {
        match self {
            Self::RISCV(riscv) => riscv,
            Self::Override(o) => o.as_riscv().expect("Runtime checks to be valid."),
            _ => unimplemented!("Runtime checks failed."),
        }
    }

    fn as_v7(&mut self) -> &mut ArmV7EM {
        match self {
            Self::Armv7EM(v7) => v7,
            Self::Override(o) => o.as_arm_v7().expect("Runtime checks to be valid."),
            _ => unimplemented!("Runtime checks failed."),
        }
    }

    fn as_v6(&mut self) -> &mut ArmV6M {
        match self {
            Self::Armv6M(v6) => v6,
            Self::Override(o) => o.as_arm_v6().expect("Runtime checks to be valid."),
            _ => unimplemented!("Runtime checks failed."),
        }
    }
}

pub trait TryAsMut<T> {
    /// Tries to convert the value to another value.
    fn try_mut(&mut self) -> crate::Result<&mut T>;
}

impl<Override: ArchitectureOverride> TryAsMut<ArmV7EM> for SupportedArchitecture<Override> {
    fn try_mut(&mut self) -> crate::Result<&mut ArmV7EM> {
        match self {
            Self::Armv7EM(a) => Ok(a),
            _ => Err(crate::GAError::InvalidArchitectureRequested.into()),
        }
    }
}

impl<Override: ArchitectureOverride> TryAsMut<ArmV6M> for SupportedArchitecture<Override> {
    fn try_mut(&mut self) -> crate::Result<&mut ArmV6M> {
        match self {
            Self::Armv6M(a) => Ok(a),
            _ => Err(crate::GAError::InvalidArchitectureRequested.into()),
        }
    }
}

impl<Override: ArchitectureOverride> TryAsMut<RISCV> for SupportedArchitecture<Override> {
    fn try_mut(&mut self) -> crate::Result<&mut RISCV> {
        match self {
            Self::RISCV(a) => Ok(a),
            _ => Err(crate::GAError::InvalidArchitectureRequested.into()),
        }
    }
}

impl<Override: ArchitectureOverride> TryAsMut<Override> for SupportedArchitecture<Override> {
    fn try_mut(&mut self) -> crate::Result<&mut Override> {
        match self {
            Self::Override(o) => Ok(o),
            _ => Err(crate::GAError::InvalidArchitectureRequested.into()),
        }
    }
}

impl<Override: ArchitectureOverride> From<Override> for SupportedArchitecture<Override> {
    fn from(value: Override) -> Self {
        Self::Override(value)
    }
}

impl std::fmt::Display for NoArchitectureOverride {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "no architecture override provided.")
    }
}
