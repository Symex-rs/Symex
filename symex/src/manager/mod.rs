use anyhow::Context;

use crate::{
    arch::SupportedArchitecture,
    executor::{
        hooks::{HookContainer, LangagueHooks, PrioriHookContainer},
        state::GAState,
        vm::{SymexStepper, VM},
        PathResult,
    },
    logging::Logger,
    path_selection::PathSelector,
    project::dwarf_helper::{DebugData, LineMap, SubProgram, SubProgramMap},
    smt::{SmtExpr, SmtMap},
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
    line_map: LineMap,
    debug_data: DebugData,
}

impl<C: Composition> SymexArbiter<C> {
    #[must_use]
    #[inline]
    #[allow(clippy::too_many_arguments)]
    pub(crate) const fn new(
        logger: C::Logger,
        project: <C::Memory as SmtMap>::ProgramMemory,
        ctx: C::SMT,
        state_container: C::StateContainer,
        hooks: HookContainer<C>,
        symbol_lookup: SubProgramMap,
        architecture: SupportedArchitecture<C::ArchitectureOverride>,
        line_map: LineMap,
        debug_data: DebugData,
    ) -> Self {
        Self {
            logger,
            project,
            ctx,
            state_container,
            hooks,
            symbol_lookup,
            architecture,
            line_map,
            debug_data,
        }
    }
}

impl<C: Composition> SymexArbiter<C> {
    pub fn add_hooks<F: FnMut(&mut HookContainer<C>, &SubProgramMap)>(&mut self, mut f: F) -> &mut Self {
        f(&mut self.hooks, &self.symbol_lookup);
        self
    }

    pub const fn get_symbol_map(&self) -> &SubProgramMap {
        &self.symbol_lookup
    }

    pub fn run_with_hooks(&mut self, function: &SubProgram, hooks: Option<PrioriHookContainer<C>>, language: &LangagueHooks) -> crate::Result<Runner<C>> {
        let mut intermediate_hooks = self.hooks.clone();
        intermediate_hooks.add_language_hooks(&self.symbol_lookup, language);
        if let Some(hooks) = hooks {
            intermediate_hooks.add_all(hooks);
        }

        let vm = VM::new(
            self.project.clone(),
            &mut self.ctx,
            function,
            0xffff_fffe,
            self.state_container.clone(),
            intermediate_hooks,
            self.architecture.clone(),
            self.logger.clone(),
            self.line_map.clone(),
            self.debug_data.clone(),
        )?;
        Ok(Runner { vm, path_idx: 0 })
    }

    pub fn run(&mut self, function: &str, language: &LangagueHooks) -> crate::Result<Runner<C>> {
        let Some(function) = self.symbol_lookup.get_by_name(function) else {
            return Err(GAError::EntryFunctionNotFound(function.to_string()).into());
        };
        let mut intermediate_hooks = self.hooks.clone();
        intermediate_hooks.add_language_hooks(&self.symbol_lookup, language);
        let vm = VM::new(
            self.project.clone(),
            &mut self.ctx,
            function,
            0xffff_fffe,
            self.state_container.clone(),
            intermediate_hooks,
            self.architecture.clone(),
            self.logger.clone(),
            self.line_map.clone(),
            self.debug_data.clone(),
        )?;
        Ok(Runner { vm, path_idx: 0 })
    }

    pub fn run_from_pc(&mut self, pc: u64, language: &LangagueHooks) -> crate::Result<Runner<C>> {
        let mut hooks = self.hooks.clone();
        hooks.add_language_hooks(&self.symbol_lookup, language);
        let ctx_clone = self.ctx.clone();
        let state = GAState::new(
            &mut self.ctx,
            ctx_clone,
            self.project.clone(),
            hooks,
            0xffff_fffe,
            pc,
            self.state_container.clone(),
            self.architecture.clone(),
            self.line_map.clone(),
            self.debug_data.clone(),
            None,
        )?;

        let vm = VM::new_from_state(self.project.clone(), state, self.logger.clone())?;
        Ok(Runner { vm, path_idx: 0 })
    }

    pub fn run_from_pc_with_hooks(&mut self, pc: u64, language: &LangagueHooks, add_hooks: Option<PrioriHookContainer<C>>) -> crate::Result<Runner<C>> {
        let mut hooks = self.hooks.clone();
        hooks.add_language_hooks(&self.symbol_lookup, language);
        if let Some(new_hooks) = add_hooks {
            hooks.add_all(new_hooks);
        }
        let ctx_clone = self.ctx.clone();
        let state = GAState::new(
            &mut self.ctx,
            ctx_clone,
            self.project.clone(),
            hooks,
            0xffff_fffe,
            pc,
            self.state_container.clone(),
            self.architecture.clone(),
            self.line_map.clone(),
            self.debug_data.clone(),
            None,
        )?;

        let vm = VM::new_from_state(self.project.clone(), state, self.logger.clone())?;
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

impl<C: Composition> Runner<C> {
    /// Returns the number of enqueued paths.
    pub fn number_of_queued_paths(&self) -> usize {
        self.vm.paths.waiting_paths()
    }
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
            logger.update_delimiter(pc, &mut state);
            // logger.record_backtrace(state.get_back_trace(&conditions));
            logger.add_constraints(
                conditions
                    .iter()
                    .map(|el| match el.get_constant() {
                        Some(val) => {
                            format!("{} = {val:#x}", el.get_identifier().unwrap_or_else(|| "un_named".to_string()))
                        }
                        None => format!("{} -> {el:?}", el.get_identifier().unwrap_or_else(|| "un_named".to_string())),
                    })
                    .collect::<Vec<_>>(),
            );

            if matches!(result, PathResult::Suppress) {
                logger.warn("Suppressing path");
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
    pub fn stepper(&mut self) -> crate::Result<Option<SymexStepper<'_, C>>> {
        self.vm.stepper()
    }
}
