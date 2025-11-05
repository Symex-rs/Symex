#![deny(
    clippy::all,
    clippy::perf,
    clippy::pedantic,
    clippy::nursery,
    rustdoc::all,
    // rust_2024_compatibility,
    rust_2018_idioms,
    warnings
)]
// Add exceptions for things that are not error prone.
#![allow(
    // clippy::module_name_repetitions,
    // clippy::too_many_arguments,
    // This is just not a bad thing.
    clippy::option_if_let_else,
    // This makes for longer lines.
    clippy::single_match_else,
    // TODO: Add comments for these.
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::cast_lossless,
    // TODO: Remove this and add crate level docs.
    rustdoc::missing_crate_level_docs,
    tail_expr_drop_order,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::match_like_matches_macro,
    clippy::match_same_arms,
    clippy::inline_always,
    clippy::match_bool,
    clippy::used_underscore_items,
)]
// If the user wants to use boolector or other deprectated dependencies inform them that they may
// not work as intended.
#![cfg_attr(feature = "deprecated", warn(warnings))]

use std::fmt::Debug;

use arch::{ArchError, ArchitectureOverride};
use executor::memory_interface::MemoryFilter;
use logging::Logger;
use memory::MemoryError;
use path_selection::PathSelector;
use project::ProjectError;
use smt::{ProgramMemory, SmtExpr, SmtFPExpr, SmtMap, SmtSolver, SolverError};

pub mod arch;
pub mod defaults;
pub mod executor;
pub mod initiation;
pub mod logging;
pub mod manager;
pub mod memory;
pub mod path_selection;
pub mod project;
pub mod smt;
pub use general_assembly;

pub type Result<T> = std::result::Result<T, anyhow::Error>;

/// Denotes a tool composition used for analysis.
pub trait Composition: Clone + Debug {
    /// The state container, this can be either only architecture specific data
    /// or it may include user provided data.
    type StateContainer: UserStateContainer + Clone;
    type SMT: SmtSolver<Expression = Self::SmtExpression, FpExpression = Self::SmtFPExpression>;
    type Logger: Logger;

    type SmtExpression: SmtExpr<FPExpression = Self::SmtFPExpression>;
    type SmtFPExpression: SmtFPExpr<Expression = Self::SmtExpression>;
    type Memory: SmtMap<SMT = Self::SMT, Expression = <Self::SMT as SmtSolver>::Expression, ProgramMemory = Self::ProgramMemory, StateContainer = Self::StateContainer>;

    /// If this is not
    /// [`NoArchitectureOverride`](crate::arch::NoArchitectureOverride) the
    /// target architecture is expected to be the provided architecture.
    type ArchitectureOverride: ArchitectureOverride;

    /// Represents the underlying program memory.
    type ProgramMemory: ProgramMemory<Self::SmtExpression>;

    type PathSelector: PathSelector<Self>;

    type MemoryFilter: MemoryFilter<Self>;
}

/// Helper to mask fields from a type.
pub trait Mask {
    #[must_use]
    /// Masks out the bit field from START until END.
    fn mask<const START: usize, const END: usize>(&self) -> Self;
}

impl Mask for u32 {
    #[allow(clippy::cast_possible_truncation)]
    fn mask<const START: usize, const END: usize>(&self) -> Self {
        let intermediate = self >> START;
        let mask = ((1u32 << (END - START + 1) as Self) as Self) - 1u32;

        let ret = intermediate & mask;
        assert!(ret <= mask);
        ret
    }
}

impl Mask for u64 {
    fn mask<const START: usize, const END: usize>(&self) -> Self {
        let intermediate = self >> START;
        let mask = ((1u64 << (END - START + 1usize) as Self) as Self) - 1u64;

        let ret = intermediate & mask;
        assert!(ret <= mask);
        ret
    }
}
/// Represents a generic state container.
pub trait UserStateContainer: Debug + Clone {}
impl UserStateContainer for () {}
impl<T: Debug + Clone> UserStateContainer for Box<T> {}

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum GAError {
    #[error("Project error: {0}")]
    ProjectError(#[from] ProjectError),

    #[error("memory error: {0}")]
    MemoryError(#[from] MemoryError),

    #[error("memory error: {0}")]
    SmtMemoryError(#[from] smt::MemoryError),

    #[error("Entry function {0} not found.")]
    EntryFunctionNotFound(String),

    #[error("Writing to static memory not permitted.")]
    WritingToStaticMemoryProhibited,

    #[error("Program counter is not deterministic.")]
    NonDeterministicPC,

    #[error("Could not open the specified file.")]
    CouldNotOpenFile(String),

    #[error("Solver error.")]
    SolverError(#[from] SolverError),

    #[error("Architecture error.")]
    ArchError(#[from] ArchError),

    #[error("Tried to resolve architecture to non supported architecture after configuration.")]
    InvalidArchitectureRequested,

    #[error("An internal error occurred")]
    InternalError(#[from] InternalError),

    #[error("Invalid floating point rounding mode requested.")]
    InvalidRoundingMode,
}

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum InternalError {
    #[error("Invalid type requested by GA.")]
    TypeError,

    #[error("Got error of ok value.")]
    InvalidErrorCombination,
}

#[derive(Debug, Clone, Copy)]
pub enum WordSize {
    Bit64,
    Bit32,
    Bit16,
    Bit8,
}

#[derive(Debug, Clone, Copy)]
#[must_use]
pub enum Endianness {
    Little,
    Big,
}

pub(crate) mod sealed {
    #[macro_export]
    macro_rules! error{
        ($($tt:tt)*) => {
            {
                #[cfg(feature = "log")]
                tracing::error!($($tt)*)
            }
        };
    }
    #[macro_export]
    macro_rules! warn{
        ($($tt:tt)*) => {
            {
                #[cfg(feature = "log")]
                tracing::warn!($($tt)*)
            }
        };
    }
    #[macro_export]
    macro_rules! debug{
        ($($tt:tt)*) => {
            {
                #[cfg(feature = "log")]
                tracing::debug!($($tt)*)
            }
        };
    }
    #[macro_export]
    macro_rules! trace {
        ($($tt:tt)*) => {
            {
                #[cfg(feature = "log")]
                tracing::trace!($($tt)*);
            }
        };
    }
    #[macro_export]
    macro_rules! info {
        ($($tt:tt)*) => {

            {
                #[cfg(feature = "log")]
                tracing::info!($($tt)*);
            }
        };
    }

    #[macro_export]
    macro_rules! repeat {
        (for {$($id:ty),*}$($tokens:tt)*) => {
            $(
            paste::paste!{

                mod [<$id:snake _tests>] {
                    use super::*;
                    type TestType = $id;
                    $($tokens)*
                }
            };
            )*
        };
    }
}
#[allow(unused_imports)]
pub(crate) use sealed::*;
