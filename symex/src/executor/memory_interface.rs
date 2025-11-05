use std::fmt::Debug;

use anyhow::Context;
use general_assembly::extension::ieee754::{OperandType, RoundingMode};

use crate::{
    debug,
    executor::{
        hooks::{
            FlagReadHook,
            FlagWriteHook,
            FpRegisterReadHook,
            FpRegisterWriteHook,
            HookContainer,
            MemoryReadHook,
            MemoryWriteHook,
            RegisterReadHook,
            RegisterWriteHook,
            ResultOrHook,
        },
        ResultOrTerminate,
    },
    smt::{Lambda, MemoryError, ProgramMemory, SmtExpr, SmtMap, SmtSolver},
    Composition,
};

pub struct Reader<'a, C: Composition> {
    pub memory: &'a mut C::Memory,
    pub memory_filter: &'a mut C::MemoryFilter,
    pub container: &'a mut HookContainer<C>,
}

pub struct Writer<'a, C: Composition> {
    pub memory: &'a mut C::Memory,
    pub memory_filter: &'a mut C::MemoryFilter,
    pub container: &'a mut HookContainer<C>,
}

/// A simple memory filter that only buckets the memory accesses in to the
/// segments of the program.
#[derive(Clone, Debug)]
pub struct MemoryBucketingFilter<C: Composition> {
    pub region_lookup: Option<<C::SMT as SmtSolver>::UnaryLambda>,
    pub number_of_regions: usize,
}

pub trait MemoryFilter<C: Composition>: Debug + Clone {
    /// Creates a new memory filter out of thin air.
    fn new() -> Self;
    /// Defines the number of distinct memory regions in the program.
    ///
    /// # Note
    ///
    /// This is mainly used to bucket the memory addresses for faster
    /// resolution.
    fn define_regions(&mut self, ctx: &mut C::SMT, program_memory: &C::ProgramMemory);

    /// Returns the number of distinct memory regions in the program.
    ///
    /// # Note
    ///
    /// This is mainly used to bucket the memory addresses for faster
    /// resolution.
    fn number_of_regions(&self) -> usize;

    /// Returns true if reading from the given address is permitted.
    fn read_memory_permitted(&mut self, address: &C::SmtExpression, length: u32) -> bool;

    /// Returns true if reading from the given address is permitted.
    fn read_memory_permitted_const(&mut self, address: u64, length: u32) -> bool;

    /// Returns true if writing to the given address is permitted.
    fn write_memory_permitted(&mut self, address: &C::SmtExpression, length: u32) -> bool;

    /// Returns true if writing to the given address is permitted.
    fn write_memory_permitted_const(&mut self, address: u64, length: u32) -> bool;

    /// Returns true if reading from the given register is permitted.
    fn read_register_permitted(&mut self, register: &str) -> bool;

    /// Returns true if writing to the given register is permitted.
    fn write_register_permitted(&mut self, register: &str) -> bool;

    /// Returns a lambda that returns the start address of the section that it
    /// is contained in.
    ///
    /// If no section contains the data it will return a bitvector with only
    /// zeros.
    fn section_lookup(&self) -> &Option<<C::SMT as SmtSolver>::UnaryLambda>;
}

impl<C: Composition> Reader<'_, C> {
    #[allow(clippy::if_same_then_else)]
    pub fn read_memory(&mut self, addr: &C::SmtExpression, size: u32) -> ResultOrHook<anyhow::Result<C::SmtExpression>, MemoryReadHook<C>> {
        let caddr = addr.get_constant();
        // TODO: Run hooks if symbol could be containend in them....
        if caddr.is_none() {
            if !self.memory_filter.read_memory_permitted(addr, size) {
                return ResultOrHook::EndFailure("Tried to write a non permitted symbolic address".to_owned());
            }
            return match self.memory.get(addr, size) {
                ResultOrTerminate::Result(r) => ResultOrHook::Result(r.context("While reading from a non- constant address")),
                ResultOrTerminate::Failure(f) => ResultOrHook::EndFailure(f),
            };
        }

        let caddr = caddr.unwrap();
        if !self.memory_filter.read_memory_permitted_const(caddr, size) {
            return ResultOrHook::EndFailure(format!("Tried to write a non premitted constant address {caddr:#x}"));
        }

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
        if ret.peek().is_some() {
            return ResultOrHook::Hooks(ret.collect());
        }
        let result = match self.memory.get_from_const_address(caddr, size) {
            ResultOrTerminate::Failure(f) => return ResultOrHook::EndFailure(f),
            ResultOrTerminate::Result(r) => r.context("While reading from a static address"),
        };
        ResultOrHook::Result(result)
    }

    #[allow(clippy::if_same_then_else)]
    pub fn read_memory_constant(&mut self, caddr: u64, size: u32) -> ResultOrHook<anyhow::Result<C::SmtExpression>, MemoryReadHook<C>> {
        if let Some(hook) = self.container.single_memory_read_hook.get(&caddr) {
            debug!("Address {caddr} had a hook : {:?}", hook);
            let mut return_value = self
                .container
                .range_memory_read_hook
                .iter()
                .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
                .map(|el| el.1)
                .collect::<Vec<_>>();
            return_value.push(*hook);
            return ResultOrHook::Hooks(return_value.clone());
        }

        let mut return_value = self
            .container
            .range_memory_read_hook
            .iter()
            .filter(|el| ((el.0 .0)..=(el.0 .1)).contains(&caddr))
            .map(|el| el.1)
            .peekable();
        if return_value.peek().is_some() {
            return ResultOrHook::Hooks(return_value.collect());
        }
        let result = match self.memory.get_from_const_address(caddr, size) {
            ResultOrTerminate::Failure(f) => return ResultOrHook::EndFailure(f),
            ResultOrTerminate::Result(r) => r.context("While reading from a static address"),
        };
        ResultOrHook::Result(result)
    }

    pub fn read_register(&mut self, id: &String) -> ResultOrHook<std::result::Result<C::SmtExpression, MemoryError>, RegisterReadHook<C>> {
        if !self.memory_filter.read_register_permitted(id) {
            return ResultOrHook::EndFailure(format!("Tried to read from a non permitted register {id}"));
        }
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
        if !self.memory_filter.read_register_permitted(id) {
            return ResultOrHook::EndFailure(format!("Tried to read from a non permitted register {id}"));
        }
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

impl<C: Composition> Writer<'_, C> {
    #[allow(clippy::match_bool)]
    pub fn write_memory(&mut self, addr: &C::SmtExpression, value: C::SmtExpression) -> ResultOrHook<std::result::Result<(), MemoryError>, MemoryWriteHook<C>> {
        let caddr = addr.get_constant();
        if caddr.is_none() {
            if !self.memory_filter.write_memory_permitted(addr, value.size()) {
                return ResultOrHook::EndFailure("Tried to write a non permitted symbolic address".to_owned());
            }
            return ResultOrHook::Result(self.memory.set(addr, value));
        }

        let caddr = caddr.unwrap();
        if !self.memory_filter.write_memory_permitted_const(caddr, value.size()) {
            return ResultOrHook::EndFailure(format!("Tried to write a non permitted address {caddr:#x}"));
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
        if ret.peek().is_some() {
            return ResultOrHook::Hooks(ret.collect());
        }
        ResultOrHook::Result(self.memory.set_to_const_address(caddr, value))
    }

    pub fn write_memory_constant(&mut self, caddr: u64, value: C::SmtExpression) -> ResultOrHook<std::result::Result<(), MemoryError>, MemoryWriteHook<C>> {
        if !self.memory_filter.write_memory_permitted_const(caddr, value.size()) {
            return ResultOrHook::EndFailure(format!("Tried to write a non permitted address {caddr:#x}"));
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
        if ret.peek().is_some() {
            return ResultOrHook::Hooks(ret.collect());
        }
        ResultOrHook::Result(self.memory.set_to_const_address(caddr, value))
    }

    pub fn write_register(&mut self, id: &str, value: &C::SmtExpression) -> ResultOrHook<std::result::Result<(), MemoryError>, RegisterWriteHook<C>> {
        if !self.memory_filter.write_register_permitted(id) {
            return ResultOrHook::EndFailure(format!("Tried to write a non permitted register {id}"));
        }
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
        if !self.memory_filter.write_register_permitted(id) {
            return ResultOrHook::EndFailure(format!("Tried to write a non permitted register {id}"));
        }
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

impl<C: Composition> MemoryFilter<C> for MemoryBucketingFilter<C> {
    fn new() -> Self {
        Self {
            region_lookup: None,
            number_of_regions: 0,
        }
    }

    fn define_regions(&mut self, ctx: &mut <C as Composition>::SMT, program_memory: &<C as Composition>::ProgramMemory) {
        let word_size = program_memory.get_word_size();
        let regions = program_memory
            .regions()
            .map(|(low, high)| (ctx.from_u64(low, word_size), ctx.from_u64(high, word_size)))
            .collect::<Vec<_>>();
        self.number_of_regions = regions.len();
        let new_expr = ctx.from_bool(true);
        let ctx_clone = ctx.clone();

        let region_lookup = <C::SMT as SmtSolver>::UnaryLambda::new(ctx, word_size, move |address: C::SmtExpression| {
            let mut new_expr = new_expr.clone();
            for (idx, (lower, upper)) in regions.iter().enumerate() {
                let idx = idx + 1;
                let idx = ctx_clone.from_u64(idx as u64, word_size);
                let req = address.ugte(lower);
                let req = req.or(&address.ulte(upper));
                new_expr = req.ite(&idx, &new_expr.resize_unsigned(word_size));
            }
            new_expr.resize_unsigned(word_size)
        });

        self.region_lookup = Some(region_lookup);
    }

    fn number_of_regions(&self) -> usize {
        self.number_of_regions
    }

    fn section_lookup(&self) -> &Option<<<C as Composition>::SMT as SmtSolver>::UnaryLambda> {
        &self.region_lookup
    }

    fn read_memory_permitted(&mut self, _address: &<C as Composition>::SmtExpression, _length: u32) -> bool {
        true
    }

    fn read_memory_permitted_const(&mut self, _address: u64, _length: u32) -> bool {
        true
    }

    fn write_memory_permitted(&mut self, _address: &<C as Composition>::SmtExpression, _length: u32) -> bool {
        true
    }

    fn write_memory_permitted_const(&mut self, _address: u64, _length: u32) -> bool {
        true
    }

    fn read_register_permitted(&mut self, _register: &str) -> bool {
        true
    }

    fn write_register_permitted(&mut self, _register: &str) -> bool {
        true
    }
}
