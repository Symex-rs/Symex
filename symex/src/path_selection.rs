use crate::{
    executor::state::GAState,
    smt::{SmtExpr, SmtMap, SmtSolver},
    Composition,
};

#[derive(Debug, Clone)]
pub struct Path<C: Composition> {
    /// The state to use when resuming execution.
    ///
    /// The location in the state should be where to resume execution at.
    pub state: GAState<C>,

    /// Constraints to add before starting execution on this path.
    pub constraints: Vec<<C::SMT as SmtSolver>::Expression>,
    /// The last pc visisted before creating the path.
    pub pc: u64,

    pub logger: C::Logger,
}

impl<C: Composition> Path<C> {
    /// Creates a new path starting at a certain state, optionally asserting a
    /// condition on the created path.
    pub fn new(state: GAState<C>, constraint: Option<<C::SMT as SmtSolver>::Expression>, pc: u64, logger: C::Logger) -> Self {
        let constraints = match constraint {
            Some(c) => vec![c],
            None => vec![],
        };

        Self { state, constraints, pc, logger }
    }
}

/// Depth-first search path exploration.
///
/// Each path is explored for as long as possible, when a path finishes the most
/// recently added path is the next to be run.
#[derive(Debug, Clone)]
pub struct DFSPathSelection<C: Composition> {
    paths: Vec<Path<C>>,
}

impl<C: Composition> DFSPathSelection<C> {
    /// Creates new without any stored paths.
    pub fn new() -> Self {
        Self { paths: Vec::new() }
    }

    /// Add a new path to be explored.
    pub fn save_path(&mut self, path: Path<C>) {
        path.state.constraints.push();
        self.paths.push(path);
    }

    /// Retrieve the next path to explore.
    pub fn get_path(&mut self) -> Option<Path<C>> {
        match self.paths.pop() {
            Some(path) => {
                path.state.constraints.pop();
                Some(path)
            }
            None => None,
        }
    }

    pub fn get_pc(&self) -> Option<u64> {
        self.paths.last().map(|el| el.state.memory.get_pc().unwrap().get_constant().unwrap())
    }

    pub fn waiting_paths(&self) -> usize {
        self.paths.len()
    }
}
