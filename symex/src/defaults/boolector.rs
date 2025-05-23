use std::marker::PhantomData;

use general_assembly::extension::ieee754::OperandType;

use super::logger::SimplePathLogger;
use crate::{
    arch::NoArchitectureOverride,
    logging::NoLogger,
    manager::SymexArbiter,
    path_selection::DFSPathSelection,
    project::Project,
    smt::smt_boolector::{memory::BoolectorMemory, Boolector, BoolectorExpr},
    Composition,
    UserStateContainer,
};

pub type Symex = SymexArbiter<DefaultComposition>;
pub type SymexWithState<Data> = SymexArbiter<UserState<Data>>;

#[derive(Clone, Debug)]
/// Default configuration for a defined architecture.
pub struct DefaultComposition {}

impl Composition for DefaultComposition {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = SimplePathLogger;
    type Memory = BoolectorMemory<()>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = &'static Project;
    type SMT = Boolector;
    type SmtExpression = BoolectorExpr;
    type SmtFPExpression = (BoolectorExpr, OperandType);
    type StateContainer = ();

    fn logger<'a>() -> &'a mut Self::Logger {
        todo!()
    }
}

#[derive(Clone, Debug)]
/// Default configuration for a defined architecture.
///
/// But without any path logging.
pub struct DefaultCompositionNoLogger {}

impl Composition for DefaultCompositionNoLogger {
    type ArchitectureOverride = NoArchitectureOverride;
    type Logger = NoLogger;
    type Memory = BoolectorMemory<()>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = &'static Project;
    type SMT = Boolector;
    type SmtExpression = BoolectorExpr;
    type SmtFPExpression = (BoolectorExpr, OperandType);
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
    type Memory = BoolectorMemory<State>;
    type PathSelector = DFSPathSelection<Self>;
    type ProgramMemory = &'static Project;
    type SMT = Boolector;
    type SmtExpression = BoolectorExpr;
    type SmtFPExpression = (BoolectorExpr, OperandType);
    type StateContainer = State;

    fn logger<'a>() -> &'a mut Self::Logger {
        todo!()
    }
}
