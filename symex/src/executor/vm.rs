//! Describes the VM for general assembly

use std::u64;

use super::{hooks::HookContainer, state::GAState, GAExecutor, PathResult};
use crate::{
    arch::SupportedArchitecture,
    path_selection::{DFSPathSelection, Path},
    project::dwarf_helper::SubProgram,
    smt::{SmtMap, SmtSolver},
    trace,
    Composition,
    Result,
};

#[derive(Debug)]
pub struct VM<C: Composition> {
    pub project: <C::Memory as SmtMap>::ProgramMemory,
    pub paths: DFSPathSelection<C>,
}

impl<C: Composition> VM<C> {
    pub fn new(
        project: <C::Memory as SmtMap>::ProgramMemory,
        ctx: &C::SMT,
        function: &SubProgram,
        end_pc: u64,
        state_container: C::StateContainer,
        hooks: HookContainer<C>,
        architecture: SupportedArchitecture,
        logger: C::Logger,
    ) -> Result<Self> {
        let mut vm = Self {
            project: project.clone(),
            paths: DFSPathSelection::new(),
        };

        let mut state = GAState::<C>::new(
            ctx.clone(),
            ctx.clone(),
            project,
            hooks,
            end_pc,
            function.bounds.0 & ((u64::MAX >> 1) << 1),
            state_container,
            architecture,
        )?;
        let _ = state.memory.set_pc(function.bounds.0 as u32)?;

        vm.paths.save_path(Path::new(state, None, 0, logger.clone()));

        Ok(vm)
    }

    #[cfg(test)]
    pub(crate) fn new_test_vm(project: <C::Memory as SmtMap>::ProgramMemory, state: GAState<C>, logger: C::Logger) -> Result<Self> {
        let mut vm = Self {
            project: project.clone(),
            paths: DFSPathSelection::new(),
        };

        vm.paths.save_path(Path::new(state, None, 0, logger));

        Ok(vm)
    }

    pub fn new_with_state(project: <C::Memory as SmtMap>::ProgramMemory, state: GAState<C>, logger: C::Logger) -> Self {
        let mut vm = Self {
            project,
            paths: DFSPathSelection::new(),
        };

        vm.paths.save_path(Path::new(state, None, 0, logger));

        vm
    }

    pub fn condition_address(&self) -> Option<u64> {
        self.paths.get_pc()
    }

    pub fn run(&mut self) -> Result<Option<(PathResult<C>, GAState<C>, Vec<C::SmtExpression>, u64, C::Logger)>> {
        trace!("VM::run");
        if let Some(mut path) = self.paths.get_path() {
            trace!("VM running path {path:?}");
            let mut executor = GAExecutor::from_state(path.state, self, self.project.clone());

            for constraint in path.constraints.clone() {
                executor.state.constraints.assert(&constraint);
            }

            let result = executor.resume_execution(&mut path.logger)?;
            return Ok(Some((result, executor.state, path.constraints, path.pc, path.logger)));
        }
        trace!("No more paths!");
        Ok(None)
    }
}
