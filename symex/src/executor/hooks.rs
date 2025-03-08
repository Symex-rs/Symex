use std::fmt::Debug;

use hashbrown::HashMap;

use super::state::GAState;
use crate::{
    project::dwarf_helper::SubProgramMap,
    smt::{MemoryError, SmtExpr, SmtMap, SmtSolver},
    trace,
    Composition,
    Result,
};

#[derive(Debug, Clone, Copy)]
pub enum PCHook<C: Composition> {
    Continue,
    EndSuccess,
    EndFailure(&'static str),
    Intrinsic(fn(state: &mut GAState<C>) -> super::Result<()>),
    Suppress,
}

#[derive(Debug, Clone)]
pub struct HookContainer<C: Composition> {
    register_read_hook: HashMap<String, fn(state: &mut GAState<C>) -> super::Result<C::SmtExpression>>,

    register_write_hook: HashMap<String, fn(state: &mut GAState<C>, value: C::SmtExpression) -> super::Result<()>>,

    pc_hook: HashMap<u64, PCHook<C>>,

    single_memory_read_hook: HashMap<u64, fn(state: &mut GAState<C>, address: u64) -> super::Result<C::SmtExpression>>,

    single_memory_write_hook: HashMap<u64, fn(state: &mut GAState<C>, value: C::SmtExpression, address: u64) -> super::Result<()>>,

    // TODO: Replace with a proper range tree implementation.
    range_memory_read_hook: Vec<((u64, u64), fn(state: &mut GAState<C>, address: u64) -> super::Result<C::SmtExpression>)>,

    range_memory_write_hook: Vec<((u64, u64), fn(state: &mut GAState<C>, value: C::SmtExpression, address: u64) -> super::Result<()>)>,

    great_filter: Vec<(C::SmtExpression, C::SmtExpression)>,

    strict: bool,
}

pub type RegisterReadHook<C> = fn(state: &mut GAState<C>) -> super::Result<<C as Composition>::SmtExpression>;
pub type RegisterWriteHook<C> = fn(state: &mut GAState<C>, value: <C as Composition>::SmtExpression) -> super::Result<()>;

pub type MemoryReadHook<C> = fn(state: &mut GAState<C>, address: u64) -> super::Result<<C as Composition>::SmtExpression>;
pub type MemoryWriteHook<C> = fn(state: &mut GAState<C>, value: <C as Composition>::SmtExpression, address: u64) -> super::Result<()>;

pub type MemoryRangeReadHook<C> = fn(state: &mut GAState<C>, address: u64) -> super::Result<<C as Composition>::SmtExpression>;
pub type MemoryRangeWriteHook<C> = fn(state: &mut GAState<C>, value: <C as Composition>::SmtExpression, address: u64) -> super::Result<()>;

impl<C: Composition> HookContainer<C> {
    /// Adds all the hooks contained in another state container.
    pub fn add_all(&mut self, other: HookContainer<C>) {
        for (pc, hook) in other.pc_hook {
            self.add_pc_hook(pc, hook);
        }

        for (reg, hook) in other.register_read_hook {
            self.add_register_read_hook(reg, hook);
        }

        for (reg, hook) in other.register_write_hook {
            self.add_register_write_hook(reg, hook);
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
    }

    /// Adds a PC hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_pc_hook(&mut self, pc: u64, value: PCHook<C>) -> &mut Self {
        let _ = self.pc_hook.insert(pc & ((u64::MAX >> 1) << 1), value);
        self
    }

    /// Adds a register read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_read_hook(&mut self, register: String, hook: RegisterReadHook<C>) -> &mut Self {
        let _ = self.register_read_hook.insert(register, hook);
        self
    }

    /// Adds a register write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this register it will be overwritten.
    pub fn add_register_write_hook(&mut self, register: String, hook: RegisterWriteHook<C>) -> &mut Self {
        let _ = self.register_write_hook.insert(register, hook);
        self
    }

    /// Adds a memory read hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_memory_read_hook(&mut self, address: u64, hook: MemoryReadHook<C>) -> &mut Self {
        let _ = self.single_memory_read_hook.insert(address, hook);
        self
    }

    /// Adds a memory write hook to the executor.
    ///
    /// ## NOTE
    ///
    /// If a hook already exists for this address it will be overwritten.
    pub fn add_memory_write_hook(&mut self, address: u64, hook: MemoryWriteHook<C>) -> &mut Self {
        let _ = self.single_memory_write_hook.insert(address, hook);
        self
    }

    /// Adds a range memory read hook to the executor.
    ///
    /// If any address in this range is read it will trigger this hook.
    pub fn add_range_memory_read_hook(&mut self, (lower, upper): (u64, u64), hook: MemoryRangeReadHook<C>) -> &mut Self {
        let _ = self.range_memory_read_hook.push(((lower, upper), hook));
        self
    }

    /// Adds a range memory write hook to the executor.
    ///
    /// If any address in this range is written it will trigger this hook.
    pub fn add_range_memory_write_hook(&mut self, (lower, upper): (u64, u64), hook: MemoryRangeWriteHook<C>) -> &mut Self {
        let _ = self.range_memory_write_hook.push(((lower, upper), hook));
        self
    }

    /// Adds a pc hook via regex matching in the dwarf data.
    pub fn add_pc_hook_regex(&mut self, map: &SubProgramMap, pattern: &'static str, hook: PCHook<C>) -> Result<()> {
        for program in map.get_all_by_regex(pattern) {
            trace!("[{pattern}]: Adding hooks for subprogram {:?}", program);
            self.add_pc_hook(program.bounds.0 & ((u64::MAX >> 1) << 1), hook.clone());
        }
        Ok(())
    }

    pub fn allow_access(&mut self, addresses: Vec<(C::SmtExpression, C::SmtExpression)>) {
        self.strict = true;
        self.great_filter = addresses;
    }

    pub fn could_possibly_be_invalid(&self, pre_condition: C::SmtExpression, addr: C::SmtExpression) -> C::SmtExpression {
        let mut new_expr = pre_condition.clone();
        for (lower, upper) in &self.great_filter {
            new_expr = new_expr.and(&addr.ult(&lower).or(&addr.ugt(&upper)));
        }
        new_expr
    }

    pub fn could_possibly_be_read_hook(
        &self,
        //addr: C::SmtExpression,
    ) -> Vec<&MemoryRangeReadHook<C>> {
        todo!("We need to generate both paths, if address is symbolic")
    }
}

pub struct Reader<'a, C: Composition> {
    memory: &'a mut <C::SMT as SmtSolver>::Memory,
    container: &'a mut HookContainer<C>,
}

pub struct Writer<'a, C: Composition> {
    memory: &'a mut <C::SMT as SmtSolver>::Memory,
    container: &'a mut HookContainer<C>,
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
            strict: false,
        }
    }

    pub fn reader<'a>(&'a mut self, memory: &'a mut <C::SMT as SmtSolver>::Memory) -> Reader<'a, C> {
        Reader { memory, container: self }
    }

    pub fn writer<'a>(&'a mut self, memory: &'a mut <C::SMT as SmtSolver>::Memory) -> Writer<'a, C> {
        Writer { memory, container: self }
    }

    pub fn get_pc_hooks(&self, value: u32) -> ResultOrHook<u32, &PCHook<C>> {
        if let Some(pchook) = self.pc_hook.get(&(value as u64)) {
            return ResultOrHook::Hook(pchook);
        }
        ResultOrHook::Result(value)
    }
}

pub enum ResultOrHook<A: Sized, B: Sized> {
    Result(A),
    Hook(B),
    Hooks(Vec<B>),
    EndFailure(String),
}

impl<'a, C: Composition> Reader<'a, C> {
    pub fn read_memory(
        &mut self,
        addr: C::SmtExpression,
        size: usize,
    ) -> ResultOrHook<std::result::Result<C::SmtExpression, MemoryError>, fn(state: &mut GAState<C>, address: u64) -> Result<C::SmtExpression>> {
        if self.container.strict {
            let (stack_start, stack_end) = self.memory.get_stack();
            let lower = addr.ult(&stack_end);
            let upper = addr.ugt(&stack_start);
            let total = lower.or(&upper);
            let cond = self.container.could_possibly_be_invalid(total.clone(), addr.clone());
            if cond.get_constant_bool().unwrap_or(true) {
                return ResultOrHook::EndFailure(format!("Tried to access {} which is out of bounds out of bounds memory", match addr.get_constant() {
                    Some(val) => format!("{:#x}", val),
                    _ => format!("{}", addr.to_binary_string()),
                }));
            }
        }
        let caddr = addr.get_constant();
        if caddr.is_none() {
            return ResultOrHook::Result(self.memory.get(&addr, size));
        }

        let caddr = caddr.unwrap();

        if let Some(hook) = self.container.single_memory_read_hook.get(&caddr) {
            let mut ret = self
                .container
                .range_memory_read_hook
                .iter()
                .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
                .map(|el| el.1)
                .collect::<Vec<_>>();
            ret.push(hook.clone());
            return ResultOrHook::Hooks(ret.clone());
        }

        let ret = self
            .container
            .range_memory_read_hook
            .iter()
            .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
            .map(|el| el.1)
            .collect::<Vec<_>>();
        if !ret.is_empty() {
            return ResultOrHook::Hooks(ret);
        }
        ResultOrHook::Result(self.memory.get(&addr, size))
    }

    pub fn read_register(&mut self, id: &String) -> ResultOrHook<std::result::Result<C::SmtExpression, MemoryError>, fn(state: &mut GAState<C>) -> Result<C::SmtExpression>> {
        if let Some(hook) = self.container.register_read_hook.get(id) {
            return ResultOrHook::Hook(hook.clone());
        }

        ResultOrHook::Result(self.memory.get_register(id))
    }

    pub fn read_pc(&mut self) -> std::result::Result<C::SmtExpression, MemoryError> {
        self.memory.get_pc()
    }
}

impl<'a, C: Composition> Writer<'a, C> {
    pub fn write_memory(
        &mut self,
        addr: C::SmtExpression,
        value: C::SmtExpression,
    ) -> ResultOrHook<std::result::Result<(), MemoryError>, fn(state: &mut GAState<C>, value: <<C as Composition>::SMT as SmtSolver>::Expression, address: u64) -> Result<()>> {
        if self.container.strict {
            let (stack_start, stack_end) = self.memory.get_stack();
            let lower = addr.ult(&stack_end);
            let upper = addr.ugt(&stack_start);
            let total = lower.or(&upper);
            if self.container.could_possibly_be_invalid(total.clone(), addr.clone()).get_constant_bool().unwrap_or(true) {
                return ResultOrHook::EndFailure(format!("Tried to access {} which is out of bounds out of bounds memory", match addr.get_constant() {
                    Some(val) => format!("{:#x}", val),
                    _ => format!("{}", addr.to_binary_string()),
                }));
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
            ret.push(hook.clone());
            return ResultOrHook::Hooks(ret.clone());
        }

        let ret = self
            .container
            .range_memory_write_hook
            .iter()
            .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
            .map(|el| el.1)
            .collect::<Vec<_>>();
        if !ret.is_empty() {
            return ResultOrHook::Hooks(ret);
        }
        ResultOrHook::Result(self.memory.set(&addr, value))
    }

    pub fn write_register(
        &mut self,
        id: &String,
        value: &C::SmtExpression,
    ) -> ResultOrHook<std::result::Result<(), MemoryError>, fn(&mut GAState<C>, <<C as Composition>::SMT as SmtSolver>::Expression) -> Result<()>> {
        if let Some(hook) = self.container.register_write_hook.get(id) {
            return ResultOrHook::Hook(hook.clone());
        }

        ResultOrHook::Result(self.memory.set_register(id, value.clone()))
    }

    pub fn write_pc(&mut self, value: u32) -> std::result::Result<(), MemoryError> {
        self.memory.set_pc(value)
    }
}

impl<C: Composition> HookContainer<C> {
    pub fn default(map: &SubProgramMap) -> Result<Self> {
        let mut ret = Self::new();
        // intrinsic functions
        let start_cyclecount = |state: &mut GAState<C>| {
            state.cycle_count = 0;
            trace!("Reset the cycle count (cycle count: {})", state.cycle_count);

            // jump back to where the function was called from
            let lr = state.get_register("LR".to_owned()).unwrap();
            state.set_register("PC".to_owned(), lr)?;
            Ok(())
        };
        let end_cyclecount = |state: &mut GAState<C>| {
            // stop counting
            state.count_cycles = false;
            trace!("Stopped counting cycles (cycle count: {})", state.cycle_count);

            // jump back to where the function was called from
            let lr = state.get_register("LR".to_owned()).unwrap();
            state.set_register("PC".to_owned(), lr)?;
            Ok(())
        };

        ret.add_pc_hook_regex(map, r"^panic.*", PCHook::EndFailure("panic")).unwrap();
        let _ = ret.add_pc_hook_regex(map, r"^panic_cold_explicit$", PCHook::EndFailure("explicit panic"));
        let _ = ret.add_pc_hook_regex(map, r"^unwrap_failed$", PCHook::EndFailure("unwrap failed"));
        let _ = ret.add_pc_hook_regex(map, r"^panic_bounds_check$", PCHook::EndFailure("bounds check failed"));
        let _ = ret.add_pc_hook_regex(
            map,
            r"^unreachable_unchecked$",
            PCHook::EndFailure("reached a unreachable unchecked call undefined behavior"),
        );
        let _ = ret.add_pc_hook_regex(map, r"^suppress_path$", PCHook::Suppress);
        let _ = ret.add_pc_hook_regex(map, r"^start_cyclecount$", PCHook::Intrinsic(start_cyclecount));
        let _ = ret.add_pc_hook_regex(map, r"^end_cyclecount$", PCHook::Intrinsic(end_cyclecount));

        ret.add_pc_hook(0xfffffffe, PCHook::EndSuccess);
        Ok(ret)
    }
}
