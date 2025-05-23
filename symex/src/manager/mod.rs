use anyhow::Context;

use crate::{
    arch::SupportedArchitecture,
    executor::{
        hooks::{HookContainer, PrioriHookContainer},
        state::GAState,
        vm::{SymexStepper, VM},
        PathResult,
    },
    logging::Logger,
    project::dwarf_helper::{SubProgram, SubProgramMap},
    smt::{ProgramMemory, SmtExpr, SmtMap, SmtSolver},
    Composition,
    GAError,
};

pub struct SymexArbiter<C: Composition> {
    logger: C::Logger,
    project: <C::Memory as SmtMap>::ProgramMemory,
    ctx: C::SMT,
    state_container: C::StateContainer,
    hooks: HookContainer<C>,
    symbol_lookup: SubProgramMap,
    architecture: SupportedArchitecture<C::ArchitectureOverride>,
}

impl<C: Composition> SymexArbiter<C> {
    pub(crate) fn new(
        logger: C::Logger,
        project: <C::Memory as SmtMap>::ProgramMemory,
        ctx: C::SMT,
        state_container: C::StateContainer,
        hooks: HookContainer<C>,
        symbol_lookup: SubProgramMap,
        architecture: SupportedArchitecture<C::ArchitectureOverride>,
    ) -> Self {
        Self {
            logger,
            project,
            ctx,
            state_container,
            hooks,
            symbol_lookup,
            architecture,
        }
    }
}

impl<C: Composition> SymexArbiter<C> {
    pub fn add_hooks<F: FnMut(&mut HookContainer<C>, &SubProgramMap)>(&mut self, mut f: F) -> &mut Self {
        f(&mut self.hooks, &self.symbol_lookup);
        self
    }

    pub fn get_symbol_map(&self) -> &SubProgramMap {
        &self.symbol_lookup
    }

    pub fn run_with_hooks(&mut self, function: &SubProgram, hooks: Option<PrioriHookContainer<C>>) -> crate::Result<Runner<C>> {
        let mut intermediate_hooks = self.hooks.clone();
        if let Some(hooks) = hooks {
            intermediate_hooks.add_all(hooks);
        }

        let vm = VM::new(
            self.project.clone(),
            &self.ctx,
            function,
            0xfffffffe,
            self.state_container.clone(),
            intermediate_hooks,
            self.architecture.clone(),
            self.logger.clone(),
        )?;
        Ok(Runner { vm, path_idx: 0 })
    }

    pub fn run_with_strict_memory(&mut self, function: &SubProgram, ranges: &[(u64, u64)], hooks: Option<PrioriHookContainer<C>>) -> crate::Result<Runner<C>> {
        let mut intermediate_hooks = self.hooks.clone();
        let allowed = ranges
            .iter()
            .map(|(low, high)| {
                (
                    self.ctx.from_u64(*low, self.project.get_ptr_size() as u32),
                    self.ctx.from_u64(*high, self.project.get_ptr_size() as u32),
                )
            })
            .collect::<Vec<_>>();

        intermediate_hooks.allow_access(allowed);
        if let Some(hooks) = hooks {
            intermediate_hooks.add_all(hooks);
        }

        let vm = VM::new(
            self.project.clone(),
            &self.ctx,
            function,
            0xfffffffe,
            self.state_container.clone(),
            intermediate_hooks,
            self.architecture.clone(),
            self.logger.clone(),
        )?;
        Ok(Runner { vm, path_idx: 0 })
    }

    pub fn run(&mut self, function: &str) -> crate::Result<Runner<C>> {
        let function = match self.symbol_lookup.get_by_name(function) {
            Some(value) => value,
            None => {
                return Err(GAError::EntryFunctionNotFound(function.to_string()).into());
            }
        };
        let vm = VM::new(
            self.project.clone(),
            &self.ctx,
            function,
            0xfffffffe,
            self.state_container.clone(),
            self.hooks.clone(),
            self.architecture.clone(),
            self.logger.clone(),
        )?;
        Ok(Runner { vm, path_idx: 0 })
    }

    pub fn run_from_pc(&mut self, pc: u64) -> crate::Result<Runner<C>> {
        let state = GAState::new(
            self.ctx.clone(),
            self.ctx.clone(),
            self.project.clone(),
            self.hooks.clone(),
            0xfffffffe,
            pc,
            self.state_container.clone(),
            self.architecture.clone(),
        )?;

        let vm = VM::new_from_state(
            self.project.clone(),
            &self.ctx,
            state,
            0xfffffffe,
            self.state_container.clone(),
            self.hooks.clone(),
            self.architecture.clone(),
            self.logger.clone(),
        )?;
        Ok(Runner { vm, path_idx: 0 })
    }

    pub fn consume(self) -> C::Logger {
        self.logger
    }
}

pub struct Runner<C: Composition> {
    vm: VM<C>,
    path_idx: usize,
}

impl<C: Composition> Iterator for Runner<C> {
    type Item = crate::Result<(GAState<C>, C::Logger, PathResult<C>)>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((result, mut state, conditions, pc, mut logger)) = match self.vm.run() {
            Ok(res) => res,
            Err(e) => {
                eprintln!("Error {e:?}");
                return Some(Err(e).context("While running from iterator"));
            }
        } {
            let cycles = state.get_cycle_count();
            logger.set_path_idx(self.path_idx);
            logger.update_delimiter(pc);
            logger.add_constraints(
                conditions
                    .iter()
                    .map(|el| match el.get_constant() {
                        Some(val) => {
                            format!("{} = {val:#x}", el.get_identifier().unwrap_or("un_named".to_string()))
                        }
                        None => format!("{} -> {el:?}", el.get_identifier().unwrap_or("un_named".to_string())),
                    })
                    .collect::<Vec<_>>(),
            );

            if let PathResult::Suppress = result {
                logger.warn("Suppressing path");
                self.path_idx += 1;
                return self.next();
            }

            logger.record_path_result(result.clone());
            logger.record_execution_time(cycles);
            logger.record_final_state(state.clone());
            self.path_idx += 1;
            return Some(Ok((state, logger.clone(), result)));
        }
        None
    }
}

impl<C: Composition> Runner<C> {
    /// Returns None if the paths are exhausted
    pub fn stepper<'vm>(&'vm mut self) -> crate::Result<Option<SymexStepper<'vm, C>>> {
        self.vm.stepper()
    }
}
