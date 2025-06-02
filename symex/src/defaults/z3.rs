use std::marker::PhantomData;

use general_assembly::extension::ieee754::OperandType;

use super::logger::SimplePathLogger;
use crate::{
    arch::NoArchitectureOverride,
    logging::NoLogger,
    manager::SymexArbiter,
    path_selection::DFSPathSelection,
    project::Project,
    smt::z3::{Z3Array, Z3Bv, Z3Context, Z3Fp, Z3Solver},
    Composition,
    UserStateContainer,
};

#[cfg(not(test))]
pub type Z3 = SymexArbiter<DefaultComposition>;
#[cfg(test)]
pub type Symex = SymexArbiter<DefaultCompositionNoLogger>;
pub type SymexWithState<Data> = SymexArbiter<UserState<Data>>;

#[derive(Clone, Debug)]
/// Default configuration for a defined architecture.
pub struct DefaultComposition {}

impl Composition for DefaultComposition {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = SimplePathLogger;
    type Memory = Z3Array<()>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = &'static Project;
    type SMT = Z3Solver;
    type SmtExpression = Z3Bv;
    type SmtFPExpression = Z3Fp;
    type StateContainer = ();

    fn logger<'a>() -> &'a mut Self::Logger {
        todo!()
    }
}

#[derive(Clone, Debug)]
/// Default configuration for a defined architecture.
pub struct DefaultCompositionNoLogger {}

impl Composition for DefaultCompositionNoLogger {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = NoLogger;
    type Memory = Z3Array<()>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = &'static Project;
    type SMT = Z3Solver;
    type SmtExpression = Z3Bv;
    type SmtFPExpression = Z3Fp;
    type StateContainer = ();

    fn logger<'a>() -> &'a mut Self::Logger {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct UserState<State: UserStateContainer> {
    state: PhantomData<State>,
}

impl<State: UserStateContainer> Composition for UserState<State> {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = SimplePathLogger;
    type Memory = Z3Array<State>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = &'static Project;
    type SMT = Z3Solver;
    type SmtExpression = Z3Bv;
    type SmtFPExpression = Z3Fp;
    type StateContainer = State;

    fn logger<'a>() -> &'a mut Self::Logger {
        todo!()
    }
}
