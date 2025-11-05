use std::fmt::Debug;

use anyhow::Context;
use general_assembly::extension::ieee754::{OperandType, RoundingMode};
use hashbrown::HashMap;

use super::{state::GAState, ResultOrTerminate};
use crate::{
    arch::InterfaceRegister,
    executor::memory_interface::{Reader, Writer},
    project::dwarf_helper::SubProgramMap,
    smt::{SmtMap, SmtSolver},
    trace,
    Composition,
    Result,
};

#[derive(Debug, Clone)]
pub enum PCHook<C: Composition> {
    Continue,
    EndSuccess,
    EndFailure(&'static str),
    Intrinsic(fn(state: &mut GAState<C>) -> super::Result<()>),
    Suppress,
}

#[derive(Debug, Clone)]
#[must_use]
pub struct PrioriHookContainer<C: Composition> {
    register_read_hook: HashMap<String, RegisterReadHook<C>>,

    register_write_hook: HashMap<String, RegisterWriteHook<C>>,

    flag_read_hook: HashMap<String, FlagReadHook<C>>,

    flag_write_hook: HashMap<String, FlagWriteHook<C>>,

    pc_hook: HashMap<u64, PCHook<C>>,

    pc_preconditions: HashMap<u64, Vec<Precondition<C>>>,

    pc_preconditions_one_shots: HashMap<u64, Vec<Precondition<C>>>,

    single_memory_read_hook: HashMap<u64, MemoryReadHook<C>>,

    single_memory_write_hook: HashMap<u64, MemoryWriteHook<C>>,

    // TODO: Replace with a proper range tree implementation.
    range_memory_read_hook: Vec<((u64, u64), MemoryRangeReadHook<C>)>,

    range_memory_write_hook: Vec<((u64, u64), MemoryRangeWriteHook<C>)>,

    fp_register_read_hook: HashMap<String, FpRegisterReadHook<C>>,
    fp_register_write_hook: HashMap<String, FpRegisterWriteHook<C>>,
}

#[derive(Debug, Clone)]
#[must_use]
pub struct HookContainer<C: Composition> {
    pub(crate) register_read_hook: HashMap<String, RegisterReadHook<C>>,

    pub(crate) register_write_hook: HashMap<String, RegisterWriteHook<C>>,

    pub(crate) flag_read_hook: HashMap<String, FlagReadHook<C>>,

    pub(crate) flag_write_hook: HashMap<String, FlagWriteHook<C>>,

    pub(crate) pc_hook: HashMap<u64, PCHook<C>>,

    pub(crate) pc_preconditions: HashMap<u64, Vec<Precondition<C>>>,

    pub(crate) pc_preconditions_one_shots: HashMap<u64, Vec<Precondition<C>>>,

    pub(crate) single_memory_read_hook: HashMap<u64, MemoryReadHook<C>>,

    pub(crate) single_memory_write_hook: HashMap<u64, MemoryWriteHook<C>>,

    // TODO: Replace with a proper range tree implementation.
    pub(crate) range_memory_read_hook: Vec<((u64, u64), MemoryRangeReadHook<C>)>,

    pub(crate) range_memory_write_hook: Vec<((u64, u64), MemoryRangeWriteHook<C>)>,

    pub(crate) fp_register_read_hook: HashMap<String, FpRegisterReadHook<C>>,
    pub(crate) fp_register_write_hook: HashMap<String, FpRegisterWriteHook<C>>,
}

pub type FlagReadHook<C> = fn(state: &mut GAState<C>) -> super::Result<<C as Composition>::SmtExpression>;
pub type FlagWriteHook<C> = fn(state: &mut GAState<C>, value: <C as Composition>::SmtExpression) -> super::Result<()>;
pub type RegisterReadHook<C> = fn(state: &mut GAState<C>) -> super::Result<<C as Composition>::SmtExpression>;
pub type RegisterWriteHook<C> = fn(state: &mut GAState<C>, value: <C as Composition>::SmtExpression) -> super::Result<()>;

pub type FpRegisterReadHook<C> = fn(&mut GAState<C>) -> Result<<<C as Composition>::SMT as SmtSolver>::FpExpression>;
pub type FpRegisterWriteHook<C> = fn(&mut GAState<C>, <<C as Composition>::SMT as SmtSolver>::FpExpression) -> Result<()>;

pub type MemoryReadHook<C> = fn(state: &mut GAState<C>, address: <C as Composition>::SmtExpression) -> super::Result<<C as Composition>::SmtExpression>;
pub type MemoryWriteHook<C> = fn(state: &mut GAState<C>, value: <C as Composition>::SmtExpression, address: <C as Composition>::SmtExpression) -> super::Result<()>;

pub type MemoryRangeReadHook<C> = fn(state: &mut GAState<C>, address: <C as Composition>::SmtExpression) -> super::Result<<C as Composition>::SmtExpression>;
pub type MemoryRangeWriteHook<C> = fn(state: &mut GAState<C>, value: <C as Composition>::SmtExpression, address: <C as Composition>::SmtExpression) -> super::Result<()>;

/// Temporal hooks are hooks that are dispatched at a specific time.
///
/// These are typically managed by the memory model.
pub type TemporalHook<C> = fn(&mut GAState<C>) -> ResultOrTerminate<()>;

pub type Precondition<C> = fn(state: &mut GAState<C>) -> super::ResultOrTerminate<()>;

impl<C: Composition> HookContainer<C> {
    /// Adds all the hooks contained in another state container.
    pub fn add_all(&mut self, other: PrioriHookContainer<C>) {
        for (pc, hook) in other.pc_hook {
            self.add_pc_hook(pc, hook);
        }

        for (reg, hook) in other.register_read_hook {
            self.add_register_read_hook(&reg, hook);
        }

        for (reg, hook) in other.register_write_hook {
            self.add_register_write_hook(&reg, hook);
        }

        for (reg, hook) in other.fp_register_read_hook {
            self.add_fp_register_read_hook(&reg, hook);
        }

        for (reg, hook) in other.fp_register_write_hook {
            self.add_fp_register_write_hook(&reg, hook);
        }

        for (range, hook) in other.range_memory_read_hook {
            self.add_range_memory_read_hook(range, hook);
        }

        for (range, hook) in other.range_memory_write_hook {
            self.add_range_memory_write_hook(range, hook);
        }

        for (addr, hook) in other.single_memory_read_hook {
            self.add_memory_read_hook(addr, hook);
        }

        for (addr, hook) in other.single_memory_write_hook {
            self.add_memory_write_hook(addr, hook);
        }

        for (addr, preconditions) in other.pc_preconditions {
            for precondition in preconditions {
                self.add_pc_precondition(addr, precondition);
            }
        }

        for (addr, preconditions) in other.pc_preconditions_one_shots {
            for precondition in preconditions {
                self.add_pc_precondition_oneshot(addr, precondition);
            }
        }
    }

    /// Adds a PC hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_pc_hook(&mut self, pc: u64, value: PCHook<C>) -> &mut Self {
        self.pc_hook.insert(pc & ((u64::MAX >> 1) << 1), value);
        self
    }

    /// Adds a PC hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_pc_precondition(&mut self, pc: u64, value: Precondition<C>) -> &mut Self {
        let pc = pc & ((u64::MAX >> 1) << 1);
        match self.pc_preconditions.get_mut(&pc) {
            Some(hooks) => {
                hooks.push(value);
            }
            None => {
                let _ = self.pc_preconditions.insert(pc, vec![value]);
            }
        }
        self
    }

    /// Adds a PC hook to the executor once this hook has been executed it will
    /// never be called again.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_pc_precondition_oneshot(&mut self, pc: u64, value: Precondition<C>) -> &mut Self {
        let pc = pc & ((u64::MAX >> 1) << 1);
        match self.pc_preconditions_one_shots.get_mut(&pc) {
            Some(hooks) => {
                hooks.push(value);
            }
            None => {
                let _ = self.pc_preconditions.insert(pc, vec![value]);
            }
        }
        self
    }

    /// Adds a flag read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_flag_read_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterReadHook<C>) -> &mut Self {
        self.flag_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a flag write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_flag_write_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterWriteHook<C>) -> &mut Self {
        self.flag_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_read_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterReadHook<C>) -> &mut Self {
        self.register_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_write_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterWriteHook<C>) -> &mut Self {
        self.register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_write_hook(&mut self, register: &(impl ToString + ?Sized), hook: FpRegisterWriteHook<C>) -> &mut Self {
        self.fp_register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_read_hook(&mut self, register: &(impl ToString + ?Sized), hook: FpRegisterReadHook<C>) -> &mut Self {
        self.fp_register_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a memory read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_memory_read_hook(&mut self, address: u64, hook: MemoryReadHook<C>) -> &mut Self {
        self.single_memory_read_hook.insert(address, hook);
        self
    }

    /// Adds a memory write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_memory_write_hook(&mut self, address: u64, hook: MemoryWriteHook<C>) -> &mut Self {
        self.single_memory_write_hook.insert(address, hook);
        self
    }

    /// Adds a range memory read hook to the executor.
    ///
    /// If any address in this range is read it will trigger this hook.
    pub fn add_range_memory_read_hook(&mut self, (lower, upper): (u64, u64), hook: MemoryRangeReadHook<C>) -> &mut Self {
        self.range_memory_read_hook.push(((lower, upper), hook));
        self
    }

    /// Adds a range memory write hook to the executor.
    ///
    /// If any address in this range is written it will trigger this hook.
    pub fn add_range_memory_write_hook(&mut self, (lower, upper): (u64, u64), hook: MemoryRangeWriteHook<C>) -> &mut Self {
        self.range_memory_write_hook.push(((lower, upper), hook));
        self
    }

    pub fn add_pc_precondition_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: Precondition<C>) -> Result<()> {
        for program in map.get_all_by_regex(pattern) {
            trace!("[{pattern}]: Adding precondition for subprogram {:?}", program);
            let addr = program.bounds.0 & ((u64::MAX >> 1) << 1);
            match self.pc_preconditions.get_mut(&addr) {
                Some(hooks) => {
                    hooks.push(hook);
                }
                None => {
                    let _ = self.pc_preconditions.insert(addr, vec![hook]);
                }
            }
        }
        Ok(())
    }

    pub fn add_pc_precondition_regex_oneshot(&mut self, map: &SubProgramMap, pattern: &'static str, hook: Precondition<C>) -> Result<()> {
        for program in map.get_all_by_regex(pattern) {
            trace!("[{pattern}]: Adding precondition for subprogram {:?}", program);
            let addr = program.bounds.0 & ((u64::MAX >> 1) << 1);
            match self.pc_preconditions_one_shots.get_mut(&addr) {
                Some(hooks) => {
                    hooks.push(hook);
                }
                None => {
                    let _ = self.pc_preconditions.insert(addr, vec![hook]);
                }
            }
        }
        Ok(())
    }

    /// Adds a pc hook via regex matching in the dwarf data.
    pub fn add_pc_hook_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: &PCHook<C>) -> Result<()> {
        let mut added = false;
        for program in map.get_all_by_regex(pattern) {
            trace!("[{pattern}]: Adding hooks for subprogram {:?}", program);
            self.add_pc_hook(program.bounds.0 & ((u64::MAX >> 1) << 1), hook.clone());
            added = true;
        }
        if !added {
            return Err(crate::GAError::ProjectError(crate::project::ProjectError::InvalidSymbol(pattern))).context("While adding hooks via regex");
        }
        Ok(())
    }

    #[must_use]
    pub fn could_possibly_be_read_hook(&self) -> Vec<&MemoryRangeReadHook<C>> {
        todo!("We need to generate both paths, if address is symbolic")
    }
}

impl<C: Composition> PrioriHookContainer<C> {
    /// Adds a PC hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_pc_hook(&mut self, pc: u64, value: PCHook<C>) -> &mut Self {
        self.pc_hook.insert(pc & ((u64::MAX >> 1) << 1), value);
        self
    }

    /// Adds a PC hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_pc_precondition(&mut self, pc: u64, value: Precondition<C>) -> &mut Self {
        let pc = pc & ((u64::MAX >> 1) << 1);
        match self.pc_preconditions.get_mut(&pc) {
            Some(hooks) => {
                hooks.push(value);
            }
            None => {
                let _ = self.pc_preconditions.insert(pc, vec![value]);
            }
        }
        self
    }

    /// Adds a PC hook to the executor once this hook has been executed it will
    /// never be called again.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_pc_precondition_oneshot(&mut self, pc: u64, value: Precondition<C>) -> &mut Self {
        let pc = pc & ((u64::MAX >> 1) << 1);
        match self.pc_preconditions_one_shots.get_mut(&pc) {
            Some(hooks) => {
                hooks.push(value);
            }
            None => {
                let _ = self.pc_preconditions.insert(pc, vec![value]);
            }
        }
        self
    }

    /// Adds a flag read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_flag_read_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterReadHook<C>) -> &mut Self {
        self.flag_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a flag write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_flag_write_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterWriteHook<C>) -> &mut Self {
        self.flag_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_read_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterReadHook<C>) -> &mut Self {
        self.register_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_write_hook(&mut self, register: &(impl ToString + ?Sized), hook: RegisterWriteHook<C>) -> &mut Self {
        self.register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_write_hook(&mut self, register: &(impl ToString + ?Sized), hook: FpRegisterWriteHook<C>) -> &mut Self {
        self.fp_register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_read_hook(&mut self, register: &(impl ToString + ?Sized), hook: FpRegisterReadHook<C>) -> &mut Self {
        self.fp_register_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a memory read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_memory_read_hook(&mut self, address: u64, hook: MemoryReadHook<C>) -> &mut Self {
        self.single_memory_read_hook.insert(address, hook);
        self
    }

    /// Adds a memory write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_memory_write_hook(&mut self, address: u64, hook: MemoryWriteHook<C>) -> &mut Self {
        self.single_memory_write_hook.insert(address, hook);
        self
    }

    /// Adds a range memory read hook to the executor.
    ///
    /// If any address in this range is read it will trigger this hook.
    pub fn add_range_memory_read_hook(&mut self, (lower, upper): (u64, u64), hook: MemoryRangeReadHook<C>) -> &mut Self {
        self.range_memory_read_hook.push(((lower, upper), hook));
        self
    }

    /// Adds a range memory write hook to the executor.
    ///
    /// If any address in this range is written it will trigger this hook.
    pub fn add_range_memory_write_hook(&mut self, (lower, upper): (u64, u64), hook: MemoryRangeWriteHook<C>) -> &mut Self {
        self.range_memory_write_hook.push(((lower, upper), hook));
        self
    }

    pub fn add_pc_precondition_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: Precondition<C>) -> Result<()> {
        for program in map.get_all_by_regex(pattern) {
            trace!("[{pattern}]: Adding precondition for subprogram {:?}", program);
            let addr = program.bounds.0 & ((u64::MAX >> 1) << 1);
            match self.pc_preconditions.get_mut(&addr) {
                Some(hooks) => {
                    hooks.push(hook);
                }
                None => {
                    let _ = self.pc_preconditions.insert(addr, vec![hook]);
                }
            }
        }
        Ok(())
    }

    pub fn add_pc_precondition_regex_oneshot(&mut self, map: &SubProgramMap, pattern: &'static str, hook: Precondition<C>) -> Result<()> {
        for program in map.get_all_by_regex(pattern) {
            trace!("[{pattern}]: Adding precondition for subprogram {:?}", program);
            let addr = program.bounds.0 & ((u64::MAX >> 1) << 1);
            match self.pc_preconditions_one_shots.get_mut(&addr) {
                Some(hooks) => {
                    hooks.push(hook);
                }
                None => {
                    let _ = self.pc_preconditions.insert(addr, vec![hook]);
                }
            }
        }
        Ok(())
    }

    /// Adds a pc hook via regex matching in the dwarf data.
    pub fn add_pc_hook_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: &PCHook<C>) -> Result<()> {
        let mut added = false;
        for program in map.get_all_by_regex(pattern) {
            trace!("[{pattern}]: Adding hooks for subprogram {:?}", program);
            self.add_pc_hook(program.bounds.0 & ((u64::MAX >> 1) << 1), hook.clone());
            added = true;
        }
        if !added {
            return Err(crate::GAError::ProjectError(crate::project::ProjectError::InvalidSymbol(pattern))).context("While adding hooks via regex");
        }
        Ok(())
    }
}

impl<C: Composition> PrioriHookContainer<C> {
    pub fn new() -> Self {
        Self {
            register_read_hook: HashMap::new(),
            register_write_hook: HashMap::new(),
            pc_hook: HashMap::new(),
            single_memory_read_hook: HashMap::new(),
            single_memory_write_hook: HashMap::new(),
            range_memory_read_hook: Vec::new(),
            range_memory_write_hook: Vec::new(),
            fp_register_read_hook: HashMap::new(),
            fp_register_write_hook: HashMap::new(),
            flag_read_hook: HashMap::new(),
            flag_write_hook: HashMap::new(),
            pc_preconditions: HashMap::new(),
            pc_preconditions_one_shots: HashMap::new(),
        }
    }
}

impl<C: Composition> HookContainer<C> {
    pub fn new() -> Self {
        Self {
            register_read_hook: HashMap::new(),
            register_write_hook: HashMap::new(),
            pc_hook: HashMap::new(),
            single_memory_read_hook: HashMap::new(),
            single_memory_write_hook: HashMap::new(),
            range_memory_read_hook: Vec::new(),
            range_memory_write_hook: Vec::new(),
            fp_register_read_hook: HashMap::new(),
            fp_register_write_hook: HashMap::new(),
            flag_read_hook: HashMap::new(),
            flag_write_hook: HashMap::new(),
            pc_preconditions: HashMap::new(),
            pc_preconditions_one_shots: HashMap::new(),
        }
    }

    pub const fn reader<'a>(&'a mut self, memory: &'a mut C::Memory, memory_filter: &'a mut C::MemoryFilter) -> Reader<'a, C> {
        Reader {
            memory,
            container: self,
            memory_filter,
        }
    }

    pub const fn writer<'a>(&'a mut self, memory: &'a mut C::Memory, memory_filter: &'a mut C::MemoryFilter) -> Writer<'a, C> {
        Writer {
            memory,
            container: self,
            memory_filter,
        }
    }

    pub fn get_pc_hooks(&self, value: u32) -> ResultOrHook<u32, &PCHook<C>> {
        if let Some(pchook) = self.pc_hook.get(&(value as u64)) {
            return ResultOrHook::Hook(pchook);
        }
        ResultOrHook::Result(value)
    }
}

#[must_use]
pub enum ResultOrHook<A: Sized, B: Sized> {
    Result(A),
    Hook(B),
    Hooks(Vec<B>),
    EndFailure(String),
}

impl<C: Composition> HookContainer<C> {
    pub fn read_fp_register(
        &mut self,
        kind: OperandType,
        id: &String,
        registers: &HashMap<String, <C::SMT as SmtSolver>::FpExpression>,
        _rm: RoundingMode,
        memory: &mut C::Memory,
    ) -> ResultOrHook<<C::SMT as SmtSolver>::FpExpression, FpRegisterReadHook<C>> {
        if let Some(hook) = self.fp_register_read_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        if let Some(value) = registers.get(id) {
            return ResultOrHook::Result(value.clone());
        }
        let any = memory.unconstrained_fp(kind, id);
        ResultOrHook::Result(any)
    }

    pub fn write_fp_register(
        &mut self,
        id: &String,
        value: <C::SMT as SmtSolver>::FpExpression,
        registers: &mut HashMap<String, <C::SMT as SmtSolver>::FpExpression>,
    ) -> ResultOrHook<crate::Result<()>, FpRegisterWriteHook<C>> {
        if let Some(hook) = self.fp_register_write_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        registers.insert(id.clone(), value);
        ResultOrHook::Result(Ok(()))
    }

    pub fn get_preconditions(&mut self, pc: &u64) -> Option<Vec<Precondition<C>>> {
        let one_shots = self.pc_preconditions_one_shots.remove(&((*pc >> 1) << 1)).clone();
        let mut ret = self.pc_preconditions.get(&((*pc >> 1) << 1)).cloned();
        if let Some(one_shots) = one_shots {
            if let Some(ret) = &mut ret {
                ret.extend(one_shots.iter());
            }
        }
        ret
    }
}

pub enum LangagueHooks {
    None,
    Rust,
}

impl<C: Composition> HookContainer<C> {
    pub fn add_language_hooks(&mut self, map: &SubProgramMap, language: &LangagueHooks) {
        match language {
            LangagueHooks::None => {}
            LangagueHooks::Rust => self.add_rust_hooks(map),
        }
    }

    pub fn add_rust_hooks(&mut self, map: &SubProgramMap) {
        let _ = self.add_pc_hook_regex(map, r"^panic.*", &PCHook::EndFailure("panic"));
        let _ = self.add_pc_hook_regex(map, r"^panic_cold_explicit$", &PCHook::EndFailure("explicit panic"));
        let _ = self.add_pc_hook_regex(
            map,
            r"^unwrap_failed$",
            &PCHook::EndFailure(
                "unwrap
        failed",
            ),
        );
        let _ = self.add_pc_hook_regex(map, r"^panic_bounds_check$", &PCHook::EndFailure("(panic) bounds check failed"));
        let _ = self.add_pc_hook_regex(
            map,
            r"^unreachable_unchecked$",
            &PCHook::EndFailure("reached a unreachable unchecked call, undefined behavior"),
        );
    }

    pub fn default(map: &SubProgramMap) -> Result<Self> {
        let mut ret = Self::new();
        // intrinsic functions
        let start_cyclecount = |state: &mut GAState<C>| {
            state.set_cycle_count(0);
            trace!("Reset the cycle count (cycle count: {})", state.get_cycle_count());

            // jump back to where the function was called from
            let ra_name = state.architecture.get_register_name(InterfaceRegister::ReturnAddress);
            let ra = state.get_register(ra_name).unwrap();
            let pc_name = state.architecture.get_register_name(InterfaceRegister::ProgramCounter);
            state.set_register(pc_name, ra)?;
            Ok(())
        };
        let end_cyclecount = |state: &mut GAState<C>| {
            // stop counting
            state.count_cycles = false;
            trace!("Stopped counting cycles (cycle count: {})", state.get_cycle_count());

            // jump back to where the function was called from
            let ra_name = state.architecture.get_register_name(InterfaceRegister::ReturnAddress);
            let ra = state.get_register(ra_name).unwrap();
            let pc_name = state.architecture.get_register_name(InterfaceRegister::ProgramCounter);
            state.set_register(pc_name, ra)?;
            Ok(())
        };

        let _ = ret.add_pc_hook_regex(map, r"^suppress_path$", &PCHook::Suppress);
        let _ = ret.add_pc_hook_regex(map, r"^start_cyclecount$", &PCHook::Intrinsic(start_cyclecount));
        let _ = ret.add_pc_hook_regex(map, r"^end_cyclecount$", &PCHook::Intrinsic(end_cyclecount));

        ret.add_pc_hook(0xffff_fffe, PCHook::EndSuccess);
        Ok(ret)
    }
}

impl<C: Composition> Default for PrioriHookContainer<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: Composition> Default for HookContainer<C> {
    fn default() -> Self {
        Self::new()
    }
}
