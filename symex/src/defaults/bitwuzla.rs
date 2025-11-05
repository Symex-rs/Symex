use std::marker::PhantomData;

use super::logger::SimplePathLogger;
use crate::{
    arch::NoArchitectureOverride,
    executor::memory_interface::MemoryBucketingFilter,
    logging::NoLogger,
    manager::SymexArbiter,
    path_selection::DFSPathSelection,
    project::Project,
    smt::bitwuzla::{expr::BitwuzlaExpr, fpexpr::FpExpr, memory::BitwuzlaMemory, Bitwuzla},
    Composition,
    UserStateContainer,
};

#[cfg(not(test))]
pub type Symex = SymexArbiter<DefaultComposition>;
#[cfg(test)]
pub type Symex = SymexArbiter<DefaultCompositionNoLogger>;
pub type SymexWithState<Data> = SymexArbiter<UserState<Data>>;

#[derive(Clone, Debug)]
/// Default configuration for a defined architecture.
pub struct DefaultComposition {}

impl Composition for DefaultComposition {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = SimplePathLogger;
    type Memory = BitwuzlaMemory<()>;
    type MemoryFilter = MemoryBucketingFilter<Self>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = std::sync::Arc<Project<Self::SMT>>;
    type SMT = Bitwuzla;
    type SmtExpression = BitwuzlaExpr;
    type SmtFPExpression = FpExpr;
    type StateContainer = ();
}

#[derive(Clone, Debug)]
/// Default configuration for a defined architecture.
pub struct DefaultCompositionNoLogger {}

impl Composition for DefaultCompositionNoLogger {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = NoLogger;
    type Memory = BitwuzlaMemory<()>;
    type MemoryFilter = MemoryBucketingFilter<Self>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = std::sync::Arc<Project<Self::SMT>>;
    type SMT = Bitwuzla;
    type SmtExpression = BitwuzlaExpr;
    type SmtFPExpression = FpExpr;
    type StateContainer = ();
}

#[derive(Clone, Debug)]
pub struct UserState<State: UserStateContainer> {
    state: PhantomData<State>,
}

impl<State: UserStateContainer> Composition for UserState<State> {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = SimplePathLogger;
    type Memory = BitwuzlaMemory<State>;
    type MemoryFilter = MemoryBucketingFilter<Self>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = std::sync::Arc<Project<Self::SMT>>;
    type SMT = Bitwuzla;
    type SmtExpression = BitwuzlaExpr;
    type SmtFPExpression = FpExpr;
    type StateContainer = State;
}
