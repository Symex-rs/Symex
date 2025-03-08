use std::marker::PhantomData;

use super::logger::SimplePathLogger;
use crate::{
    logging::NoLogger,
    manager::SymexArbiter,
    memory::array_memory::BoolectorMemory,
    smt::smt_boolector::{Boolector, BoolectorExpr},
    Composition,
    UserStateContainer,
};

pub type Symex = SymexArbiter<DefaultComposition>;
pub type SymexWithState<Data> = SymexArbiter<UserState<Data>>;

#[derive(Clone, Debug)]
/// Default configuration for a defined architecture.
pub struct DefaultComposition {}

impl Composition for DefaultComposition {
    type Logger = SimplePathLogger;
    type Memory = BoolectorMemory;
    type SMT = Boolector;
    type SmtExpression = BoolectorExpr;
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
    type Logger = NoLogger;
    type Memory = BoolectorMemory;
    type SMT = Boolector;
    type SmtExpression = BoolectorExpr;
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
    type Logger = SimplePathLogger;
    type Memory = BoolectorMemory;
    type SMT = Boolector;
    type SmtExpression = BoolectorExpr;
    type StateContainer = State;

    fn logger<'a>() -> &'a mut Self::Logger {
        todo!()
    }
}
