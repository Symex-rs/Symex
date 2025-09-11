use std::fmt::Debug;

use anyhow::Context;
use general_assembly::extension::ieee754::{OperandType, RoundingMode};
use hashbrown::HashMap;

use super::{state::GAState, ResultOrTerminate};
use crate::{
    arch::InterfaceRegister,
    debug,
    project::dwarf_helper::SubProgramMap,
    smt::{MemoryError, ProgramMemory, SmtExpr, SmtMap, SmtSolver},
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

pub trait HookBuilder<C: Composition> {
    /// Adds all the hooks contained in another state container.
    fn add_all(&mut self, other: Self);

    /// Adds a PC hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    fn add_pc_hook(&mut self, pc: u64, value: PCHook<C>) -> &mut Self;

    /// Adds a PC hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    fn add_pc_precondition(&mut self, pc: u64, value: Precondition<C>) -> &mut Self;

    /// Adds a PC hook to the executor once this hook has been executed it will
    /// never be called again.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    fn add_pc_precondition_oneshot(&mut self, pc: u64, value: Precondition<C>) -> &mut Self;

    /// Adds a flag read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    fn add_flag_read_hook(&mut self, register: impl ToString, hook: RegisterReadHook<C>) -> &mut Self;

    /// Adds a flag write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    fn add_flag_write_hook(&mut self, register: impl ToString, hook: RegisterWriteHook<C>) -> &mut Self;

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    fn add_register_read_hook(&mut self, register: impl ToString, hook: RegisterReadHook<C>) -> &mut Self;

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    fn add_register_write_hook(&mut self, register: impl ToString, hook: RegisterWriteHook<C>) -> &mut Self;

    /// Adds a memory read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    fn add_memory_read_hook(&mut self, address: u64, hook: MemoryReadHook<C>) -> &mut Self;

    /// Adds a memory write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    fn add_memory_write_hook(&mut self, address: u64, hook: MemoryWriteHook<C>) -> &mut Self;

    /// Adds a range memory read hook to the executor.
    ///
    /// If any address in this range is read it will trigger this hook.
    fn add_range_memory_read_hook(&mut self, bounds: (u64, u64), hook: MemoryRangeReadHook<C>) -> &mut Self;

    /// Adds a range memory write hook to the executor.
    ///
    /// If any address in this range is written it will trigger this hook.
    fn add_range_memory_write_hook(&mut self, bounds: (u64, u64), hook: MemoryRangeWriteHook<C>) -> &mut Self;

    fn add_pc_precondition_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: Precondition<C>) -> Result<()>;

    fn add_pc_precondition_regex_oneshot(&mut self, map: &SubProgramMap, pattern: &'static str, hook: Precondition<C>) -> Result<()>;

    /// Adds a pc hook via regex matching in the dwarf data.
    fn add_pc_hook_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: PCHook<C>) -> Result<()>;
}

pub trait HookContainter<C: Composition>: HookBuilder<C> {}

#[derive(Debug, Clone)]
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

    /// Maps regions of priviledged code.
    privelege_map: Vec<(u64, u64)>,

    strict: bool,

    priority: u64,
    pub priority_floor: u64,
}

#[derive(Debug, Clone)]
pub struct HookContainer<C: Composition> {
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

    /// Disallows access to any memory region not contained in this vector.
    pub great_filter: Vec<(u64, C::SmtExpression, C::SmtExpression)>,

    /// Same as great filter but non smt expressions.
    pub great_filter_const: Vec<(u64, u64, u64)>,

    fp_register_read_hook: HashMap<String, FpRegisterReadHook<C>>,
    fp_register_write_hook: HashMap<String, FpRegisterWriteHook<C>>,

    /// Maps regions of priviledged code.
    privelege_map: Vec<(u64, u64)>,

    strict: bool,
    pub priority: u64,
    pub priority_floor: u64,
}

pub enum PriveledgeLevel {
    User,
    System,
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
            self.add_register_read_hook(reg, hook);
        }

        for (reg, hook) in other.register_write_hook {
            self.add_register_write_hook(reg, hook);
        }

        for (reg, hook) in other.fp_register_read_hook {
            self.add_fp_register_read_hook(reg, hook);
        }

        for (reg, hook) in other.fp_register_write_hook {
            self.add_fp_register_write_hook(reg, hook);
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

        for (addr, preconditons) in other.pc_preconditions {
            for precondition in preconditons {
                self.add_pc_precondition(addr, precondition);
            }
        }

        for (addr, preconditons) in other.pc_preconditions_one_shots {
            for precondition in preconditons {
                self.add_pc_precondition_oneshot(addr, precondition);
            }
        }

        for (low, high) in other.privelege_map {
            self.privelege_map.push((low, high));
        }

        self.priority = other.priority;
        self.priority_floor = other.priority_floor;
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
    pub fn add_flag_read_hook(&mut self, register: impl ToString, hook: RegisterReadHook<C>) -> &mut Self {
        self.flag_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a flag write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_flag_write_hook(&mut self, register: impl ToString, hook: RegisterWriteHook<C>) -> &mut Self {
        self.flag_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_read_hook(&mut self, register: impl ToString, hook: RegisterReadHook<C>) -> &mut Self {
        self.register_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_write_hook(&mut self, register: impl ToString, hook: RegisterWriteHook<C>) -> &mut Self {
        self.register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_write_hook(&mut self, register: impl ToString, hook: FpRegisterWriteHook<C>) -> &mut Self {
        self.fp_register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_read_hook(&mut self, register: impl ToString, hook: FpRegisterReadHook<C>) -> &mut Self {
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
    pub fn add_pc_hook_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: PCHook<C>) -> Result<()> {
        let mut added = false;
        // println!("Looking in {map:?}");
        for program in map.get_all_by_regex(pattern) {
            // if program.bounds.1 == program.bounds.0 {
            //     println!("[{pattern}]: Ignoring {:?} as it has 0 length", program);
            //     continue;
            // }
            trace!("[{pattern}]: Adding hooks for subprogram {:?}", program);
            self.add_pc_hook(program.bounds.0 & ((u64::MAX >> 1) << 1), hook.clone());
            added = true;
        }
        if !added {
            return Err(crate::GAError::ProjectError(crate::project::ProjectError::InvalidSymbol(pattern))).context("While adding hooks via regex");
        }
        Ok(())
    }

    pub fn make_priveleged(&mut self, pc_low: u64, symbols: &SubProgramMap) -> crate::Result<()> {
        trace!("Looking for {pc_low:#04x} in \n{symbols:?}");
        let sub_program = match symbols.get_by_address(&((pc_low >> 1) << 1)) {
            None => return Ok(()), //Err(crate::GAError::ProjectError(crate::project::ProjectError::InvalidSymbolAddress(pc_low)).into()),
            Some(val) => val,
        };
        self.privelege_map.push((pc_low, sub_program.bounds.1));
        Ok(())
    }

    pub fn make_priveleged_progam(&mut self, subprogram: &crate::project::dwarf_helper::SubProgram) -> crate::Result<()> {
        self.privelege_map.push(subprogram.bounds);
        Ok(())
    }

    pub fn is_privileged(&self, pc: u64) -> bool {
        self.privelege_map.iter().any(|(low, high)| (*low..=*high).contains(&pc))
    }

    pub fn allow_access(&mut self, addresses: Vec<(u64, C::SmtExpression, C::SmtExpression)>) {
        self.strict = true;
        for el in &addresses {
            let lower = el.1.get_constant().expect("Addresses to be constants");
            let upper = el.2.get_constant().expect("Addresses to be constants");
            self.great_filter_const.push((el.0, lower, upper));
        }
        self.great_filter = addresses;
    }

    pub fn could_possibly_be_invalid_read(&self, pre_condition: C::SmtExpression, addr: C::SmtExpression) -> C::SmtExpression {
        let mut new_expr = pre_condition.clone();
        let filter = self.sufficient_priority();
        for (_, lower, upper) in self.great_filter.iter().filter(filter) {
            new_expr = new_expr.and(&addr.ult(lower).or(&addr.ugt(upper)));
        }
        new_expr
    }

    pub fn could_possibly_be_invalid_read_const(&self, pre_condition: bool, addr: u64) -> bool {
        let mut new_expr = pre_condition.clone();
        let filter = self.sufficient_priority();
        for (_prio, lower, upper) in self.great_filter_const.iter().filter(filter) {
            // println!("Checking {lower:#x} <= {addr:#x} <= {upper:#x} @ {prio}");

            new_expr = new_expr && ((addr < *lower) || (addr > *upper));
        }
        new_expr
    }

    pub fn could_possibly_be_invalid_write(&self, pre_condition: C::SmtExpression, addr: C::SmtExpression) -> C::SmtExpression {
        let mut new_expr = pre_condition.clone();
        let filter = self.sufficient_priority();
        let iter = self.great_filter.iter().filter(filter);
        for (_, lower, upper) in iter {
            new_expr = new_expr.and(&addr.ult(lower).or(&addr.ugt(upper)));
        }
        new_expr
    }

    pub fn could_possibly_be_invalid_write_const(&self, pre_condition: bool, addr: u64) -> bool {
        let mut new_expr = pre_condition.clone();
        let filter = self.sufficient_priority();
        for (_, lower, upper) in self.great_filter_const.iter().filter(filter) {
            new_expr = new_expr && ((addr < *lower) || (addr > *upper));
        }
        new_expr
    }

    // TODO: Make this cleaner with generics.
    #[inline]
    const fn sufficient_priority<T1, T2>(&self) -> impl Fn(&&(u64, T1, T2)) -> bool {
        let prio = self.priority;
        move |t| prio >= t.0
    }

    #[inline]
    const fn sufficient_priority_single_borrow<T1, T2>(&self) -> impl Fn(&(u64, T1, T2)) -> bool {
        let prio = self.priority;
        move |t| prio >= t.0
    }

    pub fn is_strict(&self) -> bool {
        self.strict
    }

    pub fn could_possibly_be_read_hook(
        &self,
        //addr: C::SmtExpression,
    ) -> Vec<&MemoryRangeReadHook<C>> {
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
    pub fn add_flag_read_hook(&mut self, register: impl ToString, hook: RegisterReadHook<C>) -> &mut Self {
        self.flag_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a flag write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_flag_write_hook(&mut self, register: impl ToString, hook: RegisterWriteHook<C>) -> &mut Self {
        self.flag_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_read_hook(&mut self, register: impl ToString, hook: RegisterReadHook<C>) -> &mut Self {
        self.register_read_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_write_hook(&mut self, register: impl ToString, hook: RegisterWriteHook<C>) -> &mut Self {
        self.register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_write_hook(&mut self, register: impl ToString, hook: FpRegisterWriteHook<C>) -> &mut Self {
        self.fp_register_write_hook.insert(register.to_string(), hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_fp_register_read_hook(&mut self, register: impl ToString, hook: FpRegisterReadHook<C>) -> &mut Self {
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
    pub fn add_pc_hook_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: PCHook<C>) -> Result<()> {
        let mut added = false;
        // println!("Looking in {map:?}");
        for program in map.get_all_by_regex(pattern) {
            // if program.bounds.1 == program.bounds.0 {
            //     println!("[{pattern}]: Ignoring {:?} as it has 0 length", program);
            //     continue;
            // }
            trace!("[{pattern}]: Adding hooks for subprogram {:?}", program);
            self.add_pc_hook(program.bounds.0 & ((u64::MAX >> 1) << 1), hook.clone());
            added = true;
        }
        if !added {
            return Err(crate::GAError::ProjectError(crate::project::ProjectError::InvalidSymbol(pattern))).context("While adding hooks via regex");
        }
        Ok(())
    }

    pub fn make_priveleged(&mut self, pc_low: u64, symbols: &SubProgramMap) -> crate::Result<()> {
        trace!("Looking for {pc_low:#04x} in \n{symbols:?}");
        let sub_program = match symbols.get_by_address(&((pc_low >> 1) << 1)) {
            None => return Ok(()), //Err(crate::GAError::ProjectError(crate::project::ProjectError::InvalidSymbolAddress(pc_low)).into()),
            Some(val) => val,
        };
        self.privelege_map.push((pc_low, sub_program.bounds.1));
        Ok(())
    }

    pub fn make_priveleged_progam(&mut self, subprogram: &crate::project::dwarf_helper::SubProgram) -> crate::Result<()> {
        self.privelege_map.push(subprogram.bounds);
        Ok(())
    }

    pub fn is_strict(&self) -> bool {
        self.strict
    }

    /// Disables the memory protection.
    pub fn disable_memory_protection(&mut self) {
        self.strict = false;
    }

    /// Enables the memory protection.
    pub fn enable_memory_protection(&mut self) {
        self.strict = true;
    }
}

pub struct Reader<'a, C: Composition> {
    memory: &'a mut C::Memory,
    container: &'a mut HookContainer<C>,
}

pub struct Writer<'a, C: Composition> {
    memory: &'a mut C::Memory,
    container: &'a mut HookContainer<C>,
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
            strict: false,
            pc_preconditions: HashMap::new(),
            pc_preconditions_one_shots: HashMap::new(),
            privelege_map: Vec::new(),
            priority: 0,
            priority_floor: 0,
        }
    }

    pub const fn set_priority(&mut self, priority: u64) {
        self.priority = priority;
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
            great_filter: Vec::new(),
            great_filter_const: Vec::new(),
            fp_register_read_hook: HashMap::new(),
            fp_register_write_hook: HashMap::new(),
            flag_read_hook: HashMap::new(),
            flag_write_hook: HashMap::new(),
            strict: false,
            pc_preconditions: HashMap::new(),
            pc_preconditions_one_shots: HashMap::new(),
            privelege_map: Vec::new(),
            priority: 0,
            priority_floor: 0,
        }
    }

    pub const fn set_priority(&mut self, priority: u64) {
        self.priority = priority;
    }

    /// Disables the memory protection.
    pub fn disable_memory_protection(&mut self) {
        self.strict = false;
    }

    /// Enables the memory protection.
    pub fn enable_memory_protection(&mut self) {
        self.strict = true;
    }

    pub fn reader<'a>(&'a mut self, memory: &'a mut C::Memory) -> Reader<'a, C> {
        Reader { memory, container: self }
    }

    pub fn writer<'a>(&'a mut self, memory: &'a mut C::Memory) -> Writer<'a, C> {
        Writer { memory, container: self }
    }

    pub fn get_pc_hooks(&self, value: u32) -> ResultOrHook<u32, &PCHook<C>> {
        if let Some(pchook) = self.pc_hook.get(&(value as u64)) {
            return ResultOrHook::Hook(pchook);
        }
        ResultOrHook::Result(value)
    }

    #[allow(dead_code)]
    pub fn permitted_regions(&mut self) -> impl Iterator<Item = impl FnOnce(&C::Memory) -> (C::SmtExpression, C::SmtExpression)> {
        self.permitted_regions_const()
            .map(|(lower, upper)| move |mem: &C::Memory| (mem.from_u64(lower, mem.get_ptr_size()), mem.from_u64(upper, mem.get_ptr_size())))
    }

    #[allow(dead_code)]
    #[inline]
    pub fn permitted_regions_const(&self) -> impl Iterator<Item = (u64, u64)> {
        let filter = self.sufficient_priority_single_borrow();
        self.great_filter_const.clone().into_iter().filter(filter).map(|(.., lower, upper)| (lower, upper))
    }

    #[allow(dead_code)]
    pub fn all_regions(&self, mem: &C::Memory) -> impl Iterator<Item = impl FnOnce(&C::Memory) -> (C::SmtExpression, C::SmtExpression)> {
        self.all_regions_const(mem)
            .map(|(lower, upper)| move |mem: &C::Memory| (mem.from_u64(lower, mem.get_ptr_size()), mem.from_u64(upper, mem.get_ptr_size())))
    }

    #[allow(dead_code)]
    pub fn all_regions_const(&self, mem: &C::Memory) -> impl Iterator<Item = (u64, u64)> {
        // TODO: These should be in static memory.
        let regs = self.permitted_regions_const().collect::<Vec<_>>().into_iter();
        let regs = regs.chain(mem.regions().collect::<Vec<_>>());
        let regs = regs.chain(mem.program_memory().regions().collect::<Vec<_>>());
        regs
    }
}

pub enum ResultOrHook<A: Sized, B: Sized> {
    Result(A),
    Hook(B),
    Hooks(Vec<B>),
    EndFailure(String),
}

impl<'a, C: Composition> Reader<'a, C> {
    #[allow(clippy::if_same_then_else)]
    pub fn read_memory(&mut self, addr: C::SmtExpression, size: u32) -> ResultOrHook<anyhow::Result<C::SmtExpression>, MemoryReadHook<C>> {
        let caddr = addr.get_constant();
        if self.container.strict && self.container.priority != 16 && self.container.priority != 0 {
            if let Some(addr) = caddr {
                let (stack_start, stack_end) = self.memory.get_stack();
                let stack_start = stack_start.get_constant().expect("Stack pointers to be known!");
                let stack_end = stack_end.get_constant().expect("Stack pointers to be known!");
                let lower = addr < stack_end;
                let upper = addr > stack_start;
                let total = lower || upper;

                let mut cond = self.container.could_possibly_be_invalid_read_const(total, addr);
                let not_stack = cond;
                if not_stack {
                    if not_stack {
                        trace!("Address {:#x?} not contained in resources or stack. Trying to locate it in memory.", addr);
                    }
                    let not_in_program_data = { self.memory.out_of_bounds_const(addr) };
                    if not_stack && not_in_program_data {
                        trace!("Address {:#x?} not contained in memory segments. Trying to locate it in memory.", addr);
                    } else if not_stack {
                        trace!("Address {:#x?} contained in a segment of constants.", addr);
                    }
                    cond = cond && not_in_program_data;
                }
                if cond
                    && !self
                        .container
                        .is_privileged((self.memory.get_pc().expect("PC must be accessible").get_constant().expect("PC must be deterministic") >> 1) << 1)
                    && self.container.priority != 16
                    && self.container.priority != 0
                {
                    return ResultOrHook::EndFailure(format!("Tried to read from {}", format!("{:#x}", addr)));
                }
            } else {
                let (stack_start, stack_end) = self.memory.get_stack();
                let lower = addr.ult(&stack_end);
                let upper = addr.ugt(&stack_start);
                let total = lower.or(&upper);
                let total = total;

                let mut cond = self.container.could_possibly_be_invalid_read(total.clone(), addr.clone());
                let not_stack = cond.get_constant_bool().unwrap_or(true);
                if not_stack {
                    if not_stack {
                        trace!("Address {:#x?} not contained in resources or stack. Trying to locate it in memory.", addr.get_constant());
                    }
                    let not_in_program_data = { self.memory.out_of_bounds(&addr) };
                    if not_stack && not_in_program_data.get_constant_bool().unwrap_or(true) {
                        trace!("Address {:#x?} not contained in memory segments. Trying to locate it in memory.", addr.get_constant());
                    } else if not_stack {
                        trace!("Address {:#x?} contained in a segment of constants.", addr.get_constant());
                    }
                    cond = cond.and(&not_in_program_data);
                }
                if cond.get_constant_bool().unwrap_or(true)
                    && !self
                        .container
                        .is_privileged((self.memory.get_pc().expect("PC must be accessible").get_constant().expect("PC must be deterministic") >> 1) << 1)
                    && self.container.priority != 16
                    && self.container.priority != 0
                {
                    return ResultOrHook::EndFailure(format!("Tried to read from {}", match addr.get_constant() {
                        Some(val) => format!("{:#x}", val),
                        _ => addr.to_binary_string().to_string(),
                    }));
                }
            }
        }
        // TODO: Run hooks if symbol could be containend in them....
        if caddr.is_none() {
            return match self.memory.get(&addr, size) {
                ResultOrTerminate::Result(r) => ResultOrHook::Result(r.context("While reading from a non- constant address")),
                ResultOrTerminate::Failure(f) => ResultOrHook::EndFailure(f),
            };
        }

        let caddr = caddr.unwrap();

        if let Some(hook) = self.container.single_memory_read_hook.get(&caddr) {
            debug!("Address {caddr} had a hook : {:?}", hook);
            let mut ret = self
                .container
                .range_memory_read_hook
                .iter()
                .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
                .map(|el| el.1)
                .collect::<Vec<_>>();
            ret.push(*hook);
            return ResultOrHook::Hooks(ret.clone());
        }

        let mut ret = self
            .container
            .range_memory_read_hook
            .iter()
            .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
            .map(|el| el.1)
            .peekable();
        if !ret.peek().is_none() {
            // debug!("Address {caddr} had a hooks : {:?}", ret);
            return ResultOrHook::Hooks(ret.collect());
        }
        let res = match self.memory.get_from_const_address(caddr, size) {
            ResultOrTerminate::Failure(f) => return ResultOrHook::EndFailure(f),
            ResultOrTerminate::Result(r) => r.context("While reading from a static address"),
        };
        ResultOrHook::Result(res)
    }

    #[allow(clippy::if_same_then_else)]
    pub fn read_memory_constant(&mut self, addr: u64, size: u32) -> ResultOrHook<anyhow::Result<C::SmtExpression>, MemoryReadHook<C>> {
        if self.container.strict {
            let (stack_start, stack_end) = self.memory.get_stack();
            let stack_start = stack_start.get_constant().expect("Stack pointers to be known!");
            let stack_end = stack_end.get_constant().expect("Stack pointers to be known!");
            let lower = addr < stack_end;
            let upper = addr > stack_start;
            let total = lower || upper;
            let total = total;

            let mut cond = self.container.could_possibly_be_invalid_read_const(total, addr);
            let not_stack = cond;
            if not_stack {
                if not_stack {
                    trace!("Address {:#x?} not contained in resources or stack. Trying to locate it in memory.", addr);
                }
                let not_in_program_data = { self.memory.out_of_bounds_const(addr) };
                if not_stack && not_in_program_data {
                    trace!("Address {:#x?} not contained in memory segments. Trying to locate it in memory.", addr);
                } else if not_stack {
                    trace!("Address {:#x?} contained in a segment of constants.", addr);
                }
                cond = cond && not_in_program_data;
            }
            if cond
                && !self
                    .container
                    .is_privileged((self.memory.get_pc().expect("PC must be accessible").get_constant().expect("PC must be deterministic") >> 1) << 1)
                && self.container.priority != 16
                && self.container.priority != 0
            {
                return ResultOrHook::EndFailure(format!("Tried to read from {} @ {}", format!("{:#x}", addr), self.container.priority));
            }
        }

        let caddr = addr;

        if let Some(hook) = self.container.single_memory_read_hook.get(&caddr) {
            debug!("Address {caddr} had a hook : {:?}", hook);
            let mut ret = self
                .container
                .range_memory_read_hook
                .iter()
                .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
                .map(|el| el.1)
                .collect::<Vec<_>>();
            ret.push(*hook);
            return ResultOrHook::Hooks(ret.clone());
        }

        let mut ret = self
            .container
            .range_memory_read_hook
            .iter()
            .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
            .map(|el| el.1)
            .peekable();
        if !ret.peek().is_none() {
            return ResultOrHook::Hooks(ret.collect());
        }
        let res = match self.memory.get_from_const_address(caddr, size) {
            ResultOrTerminate::Failure(f) => return ResultOrHook::EndFailure(f),
            ResultOrTerminate::Result(r) => r.context("While reading from a static address"),
        };
        ResultOrHook::Result(res)
    }

    pub fn read_register(&mut self, id: &String) -> ResultOrHook<std::result::Result<C::SmtExpression, MemoryError>, RegisterReadHook<C>> {
        if let Some(hook) = self.container.register_read_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        ResultOrHook::Result(self.memory.get_register(id))
    }

    pub fn read_fp_register(
        &mut self,
        id: &str,
        source_ty: OperandType,
        dest_ty: OperandType,
        rm: RoundingMode,
        signed: bool,
    ) -> ResultOrHook<std::result::Result<C::SmtFPExpression, MemoryError>, FpRegisterReadHook<C>> {
        if let Some(hook) = self.container.fp_register_read_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        ResultOrHook::Result(self.memory.get_fp_register(id, source_ty, dest_ty, rm, signed))
    }

    pub fn read_flag(&mut self, id: &String) -> ResultOrHook<std::result::Result<C::SmtExpression, MemoryError>, FlagReadHook<C>> {
        if let Some(hook) = self.container.flag_read_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        ResultOrHook::Result(self.memory.get_flag(id))
    }

    pub fn read_pc(&mut self) -> std::result::Result<C::SmtExpression, MemoryError> {
        self.memory.get_pc()
    }
}

impl<'a, C: Composition> Writer<'a, C> {
    pub fn write_memory(&mut self, addr: C::SmtExpression, value: C::SmtExpression) -> ResultOrHook<std::result::Result<(), MemoryError>, MemoryWriteHook<C>> {
        let caddr = addr.get_constant();
        if self.container.strict && self.container.priority != 16 && self.container.priority != 0 {
            if let Some(addr) = caddr {
                let (stack_start, stack_end) = self.memory.get_stack();
                let stack_start = stack_start.get_constant().expect("Stack pointers to be known!");
                let stack_end = stack_end.get_constant().expect("Stack pointers to be known!");
                let lower = addr < stack_end;
                let upper = addr > stack_start;
                let total = lower || upper;

                let cond = self.container.could_possibly_be_invalid_write_const(total, addr);
                if cond
                    && !self
                        .container
                        .is_privileged((self.memory.get_pc().expect("PC must be accessible").get_constant().expect("PC must be deterministic") >> 1) << 1)
                    && self.container.priority != 16
                    && self.container.priority != 0
                {
                    return ResultOrHook::EndFailure(format!("Tried to write to {:#x}", addr));
                }
            } else {
                let (stack_start, stack_end) = self.memory.get_stack();
                let lower = addr.ult(&stack_end);
                let upper = addr.ugt(&stack_start);
                let total = lower.or(&upper);
                let on_stack = total.clone();
                if self.container.could_possibly_be_invalid_write(total, addr.clone()).get_constant_bool().unwrap_or(true)
                    && !self
                        .container
                        .is_privileged((self.memory.get_pc().expect("PC must be accessible").get_constant().expect("PC must be deterministic") >> 1) << 1)
                    && self.container.priority != 16
                    && self.container.priority != 0
                {
                    return ResultOrHook::EndFailure(format!(
                        "Tried to write to {}, on stack: {:?}",
                        match addr.get_constant() {
                            Some(val) => format!("{:#x}", val),
                            _ => self.memory.with_model_gen(|| match self.memory.is_sat() {
                                true => addr.to_binary_string().to_string(),
                                false => "Unsat".to_string(),
                            }),
                        },
                        on_stack.get_constant_bool().map(|el| !el),
                    ));
                }
            }
        }
        let caddr = addr.get_constant();
        if caddr.is_none() {
            return ResultOrHook::Result(self.memory.set(&addr, value));
        }

        let caddr = caddr.unwrap();

        if let Some(hook) = self.container.single_memory_write_hook.get(&caddr) {
            let mut ret = self
                .container
                .range_memory_write_hook
                .iter()
                .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
                .map(|el| el.1)
                .collect::<Vec<_>>();
            ret.push(*hook);
            return ResultOrHook::Hooks(ret.clone());
        }

        let mut ret = self
            .container
            .range_memory_write_hook
            .iter()
            .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
            .map(|el| el.1)
            .peekable();
        if !ret.peek().is_none() {
            return ResultOrHook::Hooks(ret.collect());
        }
        ResultOrHook::Result(self.memory.set_to_const_address(caddr, value))
    }

    pub fn write_memory_constant(&mut self, caddr: u64, value: C::SmtExpression) -> ResultOrHook<std::result::Result<(), MemoryError>, MemoryWriteHook<C>> {
        if self.container.strict && self.container.priority != 16 && self.container.priority != 0 {
            let (stack_start, stack_end) = self.memory.get_stack();
            let stack_start = stack_start.get_constant().expect("Stack pointers to be known!");
            let stack_end = stack_end.get_constant().expect("Stack pointers to be known!");
            let lower = caddr < stack_end;
            let upper = caddr > stack_start;
            let total = lower || upper;
            let total = total;

            let cond = self.container.could_possibly_be_invalid_write_const(total, caddr);
            if cond
                && !self
                    .container
                    .is_privileged((self.memory.get_pc().expect("PC must be accessible").get_constant().expect("PC must be deterministic") >> 1) << 1)
                && self.container.priority != 16
                && self.container.priority != 0
            {
                return ResultOrHook::EndFailure(format!("Tried to write to {}", format!("{:#x}", caddr)));
            }
        }

        if let Some(hook) = self.container.single_memory_write_hook.get(&caddr) {
            let mut ret = self
                .container
                .range_memory_write_hook
                .iter()
                .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
                .map(|el| el.1)
                .collect::<Vec<_>>();
            ret.push(*hook);
            return ResultOrHook::Hooks(ret.clone());
        }

        let mut ret = self
            .container
            .range_memory_write_hook
            .iter()
            .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
            .map(|el| el.1)
            .peekable();
        if !ret.peek().is_none() {
            return ResultOrHook::Hooks(ret.collect());
        }
        ResultOrHook::Result(self.memory.set_to_const_address(caddr, value))
    }

    pub fn write_register(&mut self, id: &String, value: &C::SmtExpression) -> ResultOrHook<std::result::Result<(), MemoryError>, RegisterWriteHook<C>> {
        if let Some(hook) = self.container.register_write_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        ResultOrHook::Result(self.memory.set_register(id, value.clone()))
    }

    pub fn write_fp_register(
        &mut self,
        id: &str,
        value: &C::SmtFPExpression,
        rm: RoundingMode,
        signed: bool,
    ) -> ResultOrHook<std::result::Result<(), MemoryError>, FpRegisterWriteHook<C>> {
        if let Some(hook) = self.container.fp_register_write_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        ResultOrHook::Result(self.memory.set_fp_register(id, value.clone(), rm, signed))
    }

    pub fn write_flag(&mut self, id: &String, value: &C::SmtExpression) -> ResultOrHook<std::result::Result<(), MemoryError>, FlagWriteHook<C>> {
        if let Some(hook) = self.container.flag_write_hook.get(id) {
            return ResultOrHook::Hook(*hook);
        }

        ResultOrHook::Result(self.memory.set_flag(id, value.clone()))
    }

    pub fn write_pc(&mut self, value: u32) -> std::result::Result<(), MemoryError> {
        self.memory.set_pc(value)
    }
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
    pub fn add_language_hooks(&mut self, map: &SubProgramMap, language: LangagueHooks) {
        match language {
            LangagueHooks::None => {}
            LangagueHooks::Rust => self.add_rust_hooks(map),
        }
    }

    pub fn add_rust_hooks(&mut self, map: &SubProgramMap) {
        let _ = self.add_pc_hook_regex(map, r"^panic.*", PCHook::EndFailure("panic"));
        let _ = self.add_pc_hook_regex(map, r"^panic_cold_explicit$", PCHook::EndFailure("explicit panic"));
        let _ = self.add_pc_hook_regex(
            map,
            r"^unwrap_failed$",
            PCHook::EndFailure(
                "unwrap
        failed",
            ),
        );
        let _ = self.add_pc_hook_regex(map, r"^panic_bounds_check$", PCHook::EndFailure("(panic) bounds check failed"));
        let _ = self.add_pc_hook_regex(
            map,
            r"^unreachable_unchecked$",
            PCHook::EndFailure("reached a unreachable unchecked call, undefined behavior"),
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
            let ra = state.get_register(ra_name.to_owned()).unwrap();
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
            let ra = state.get_register(ra_name.to_owned()).unwrap();
            let pc_name = state.architecture.get_register_name(InterfaceRegister::ProgramCounter);
            state.set_register(pc_name, ra)?;
            Ok(())
        };

        let _ = ret.add_pc_hook_regex(map, r"^suppress_path$", PCHook::Suppress);
        let _ = ret.add_pc_hook_regex(map, r"^start_cyclecount$", PCHook::Intrinsic(start_cyclecount));
        let _ = ret.add_pc_hook_regex(map, r"^end_cyclecount$", PCHook::Intrinsic(end_cyclecount));

        ret.add_pc_hook(0xfffffffe, PCHook::EndSuccess);
        Ok(ret)
    }
}
