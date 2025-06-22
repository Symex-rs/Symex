//! Describes the VM for general assembly

use super::{hooks::HookContainer, state::GAState, GAExecutor, PathResult};
use crate::{
    arch::SupportedArchitecture,
    path_selection::{Path, PathSelector},
    project::dwarf_helper::{DebugData, LineMap, SubProgram},
    smt::{SmtMap, SmtSolver},
    trace,
    Composition,
    Result,
};

#[derive(Debug)]
pub struct VM<C: Composition> {
    pub project: <C::Memory as SmtMap>::ProgramMemory,
    pub paths: C::PathSelector,
}

impl<C: Composition> VM<C> {
    #[inline]
    #[allow(clippy::too_many_arguments)]
    /// Creates a new virtual machine.
    pub fn new(
        project: <C::Memory as SmtMap>::ProgramMemory,
        ctx: &C::SMT,
        function: &SubProgram,
        end_pc: u64,
        state_container: C::StateContainer,
        hooks: HookContainer<C>,
        architecture: SupportedArchitecture<C::ArchitectureOverride>,
        logger: C::Logger,
        line_map: LineMap,
        debug_data: DebugData,
    ) -> Result<Self> {
        let mut vm = Self {
            project: project.clone(),
            paths: C::PathSelector::new(),
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
            line_map,
            debug_data,
            Some(function.clone()),
        )?;
        state.memory.set_pc(function.bounds.0 as u32)?;

        vm.paths.save_path(Path::new(state, None, 0, logger.clone()));

        Ok(vm)
    }

    pub fn new_from_state(project: <C::Memory as SmtMap>::ProgramMemory, state: GAState<C>, logger: C::Logger) -> Result<Self> {
        let mut vm = Self {
            project: project.clone(),
            paths: C::PathSelector::new(),
        };

        vm.paths.save_path(Path::new(state, None, 0, logger.clone()));

        Ok(vm)
    }

    #[cfg(test)]
    pub(crate) fn new_test_vm(project: <C::Memory as SmtMap>::ProgramMemory, state: GAState<C>, logger: C::Logger) -> Result<Self> {
        let mut vm = Self {
            project: project.clone(),
            paths: C::PathSelector::new(),
        };

        vm.paths.save_path(Path::new(state, None, 0, logger));

        Ok(vm)
    }

    pub fn new_with_state(project: <C::Memory as SmtMap>::ProgramMemory, state: GAState<C>, logger: C::Logger) -> Self {
        let mut vm = Self {
            project,
            paths: C::PathSelector::new(),
        };

        vm.paths.save_path(Path::new(state, None, 0, logger));

        vm
    }

    pub fn condition_address(&self) -> Option<u64> {
        self.paths.get_pc()
    }

    #[allow(clippy::type_complexity)]
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

    pub fn stepper(&mut self) -> Result<Option<SymexStepper<'_, C>>> {
        if let Some(mut path) = self.paths.get_path() {
            trace!("VM running path {path:?}");
            let project = self.project.clone();
            let mut executor = GAExecutor::from_state(path.state.clone(), self, self.project.clone());

            for constraint in path.constraints.clone() {
                executor.state.constraints.assert(&constraint);
            }

            let _result = executor.resume_execution_stepper(&mut path.logger)?;
            return Ok(Some(SymexStepper { executor, project, path }));
        }
        trace!("No more paths!");
        Ok(None)
    }
}

pub struct SymexStepper<'vm, C: Composition> {
    executor: GAExecutor<'vm, C>,
    project: <C::Memory as SmtMap>::ProgramMemory,
    // NOTE: This is not linked to the executor state. This is merely the state at initiation
    // timeis merely the state at initiation time.
    path: Path<C>,
}

impl<'vm, C: Composition> SymexStepper<'vm, C> {
    /// Returns none if the path did not terminate.
    #[allow(clippy::type_complexity)]
    pub fn step(&mut self, steps: usize) -> Result<Option<(PathResult<C>, &GAState<C>, &Vec<C::SmtExpression>, u64, &C::Logger)>> {
        match self.executor.step(steps, &mut self.path.logger)? {
            Some(result) => Ok(Some((result, &self.executor.state, &self.path.constraints, self.path.pc, &self.path.logger))),
            None => Ok(None),
        }
    }

    pub fn executor(&mut self) -> &mut GAExecutor<'vm, C> {
        &mut self.executor
    }

    pub fn project(&mut self) -> &mut <C::Memory as SmtMap>::ProgramMemory {
        &mut self.project
    }

    pub fn path(&mut self) -> &mut Path<C> {
        &mut self.path
    }
}
