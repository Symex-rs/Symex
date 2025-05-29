//! Holds the state in general assembly execution.

use std::collections::VecDeque;

use anyhow::Context as _;
use general_assembly::prelude::Condition;
use gimli::{EndianSlice, RunTimeEndian};
use hashbrown::HashMap;

use super::{
    extension::ieee754::FpState,
    hooks::{HookContainer, PCHook, Reader, ResultOrHook, Writer},
    instruction::Instruction,
    ResultOrTerminate,
};
use crate::{
    arch::{SupportedArchitecture, TryAsMut, InterfaceRegister},
    debug,
    extract,
    logging::Logger,
    project::{
        self,
        dwarf_helper::{DebugData, LineMap, DAP},
        ProjectError,
    },
    smt::{ProgramMemory, SmtExpr, SmtMap, SmtSolver},
    trace,
    Composition,
    GAError,
    InternalError,
    Result,
};

pub enum HookOrInstruction<'a, C: Composition> {
    PcHook(&'a PCHook<C>),
    Instruction(Instruction<C>),
}

#[derive(Clone, Debug)]
pub struct ContinueInsideInstruction<C: Composition> {
    pub instruction: Instruction<C>,
    pub context: crate::executor::Context<C>,
}

#[derive(Clone, Debug)]
pub struct GAState<C: Composition> {
    pub memory: C::Memory,
    pub user_state: C::StateContainer,
    pub constraints: C::SMT,
    pub hooks: HookContainer<C>,
    pub count_cycles: bool,
    pub last_instruction: Option<Instruction<C>>,
    pub last_pc: u64,
    pub continue_in_instruction: Option<ContinueInsideInstruction<C>>,
    pub current_instruction: Option<Instruction<C>>,
    pub any_counter: u64,
    pub architecture: SupportedArchitecture<C::ArchitectureOverride>,
    instruction_counter: usize,
    has_jumped: bool,
    pub instruction_conditions: VecDeque<Condition>,
    pub instruction_had_condition: bool,
    pub fp_state: FpState<C>,
    pub line_lookup: LineMap,
    debug_data: Option<DebugData>,
}

impl<C: Composition> GAState<C> {
    /// Create a new state.
    pub fn new(
        ctx: C::SMT,
        constraints: C::SMT,
        project: <C::Memory as SmtMap>::ProgramMemory,
        hooks: HookContainer<C>,
        end_address: u64,
        start_address: u64,
        state: C::StateContainer,
        architecture: SupportedArchitecture<C::ArchitectureOverride>,
        line_lookup: LineMap,
        debug_data: DebugData,
    ) -> std::result::Result<Self, GAError> {
        let pc_reg = start_address;
        debug!("Found function at addr: {:#X}.", pc_reg);
        let ptr_size = project.get_ptr_size();

        let sp_reg = match project.get_symbol_address("_stack_start") {
            Some(a) => Ok(a),
            None => Err(ProjectError::UnableToParseElf("start of stack not found".to_owned())),
        }?;
        debug!("Found stack start at addr: {:#X}.", sp_reg);

        let endianness = project.get_endianness();
        let initial_sp = ctx.from_u64(sp_reg, ptr_size as u32);
        let mut memory = C::Memory::new(ctx.clone(), project, ptr_size, endianness, initial_sp, &state)?;
        let pc_expr = ctx.from_u64(pc_reg, ptr_size as u32);
        memory.set_register("PC", pc_expr)?;

        let sp_expr = ctx.from_u64(sp_reg, ptr_size as u32);
        memory.set_register("SP", sp_expr)?;

        // Set the link register to max value to detect when returning from a function.
        let end_pc_expr = ctx.from_u64(end_address, ptr_size as u32);
        let register_name = architecture.get_register_name(InterfaceRegister::ReturnAddress);
        memory.set_register(&register_name.to_owned(), end_pc_expr)?;
        let mut ret = Self {
            constraints,
            memory,
            hooks,
            user_state: state,
            count_cycles: true,
            last_instruction: None,
            last_pc: 0,
            continue_in_instruction: None,
            current_instruction: None,
            instruction_counter: 0,
            has_jumped: false,
            instruction_conditions: VecDeque::new(),
            any_counter: 0,
            architecture,
            fp_state: FpState::new(),
            instruction_had_condition: false,
            line_lookup,
            debug_data: Some(debug_data),
        };

        ret.architecture.initiate_state()(&mut ret);
        Ok(ret)
    }

    pub fn label_new_symbolic(&mut self, start: &str) -> String {
        let ret = format!("{start}_{}", self.any_counter);
        self.any_counter += 1;
        ret
    }

    pub fn reset_has_jumped(&mut self) {
        self.has_jumped = false;
    }

    pub fn set_has_jumped(&mut self) {
        self.has_jumped = true;
    }

    /// Indicates if the last executed instruction was a conditional branch that
    /// branched.
    pub fn get_has_jumped(&self) -> bool {
        self.has_jumped
    }

    /// Increments the instruction counter by one.
    pub fn increment_instruction_count(&mut self) {
        self.instruction_counter += 1;
    }

    /// Gets the current instruction count
    pub fn get_instruction_count(&self) -> usize {
        self.instruction_counter
    }

    /// Gets the last instruction that was executed.
    pub fn get_last_instruction(&self) -> Option<Instruction<C>> {
        self.last_instruction.clone()
    }

    /// Checks if the execution is currently inside of a conditional block.
    pub fn get_in_conditional_block(&self) -> bool {
        !self.instruction_conditions.is_empty()
    }

    /// Gets the currecnt cycle count
    pub fn get_cycle_count(&mut self) -> u64 {
        self.memory.get_cycle_count()
    }

    /// Sets the cycle count of the device.
    pub fn set_cycle_count(&mut self, value: u64) {
        self.memory.set_cycle_count(value);
    }

    /// Increment the cycle counter with the cycle count of the last
    /// instruction.
    pub fn increment_cycle_count(&mut self) {
        // Do nothing if cycles should not be counted
        if !self.count_cycles {
            return;
        }

        let cycles = match &self.last_instruction {
            Some(i) => match i.max_cycle {
                super::instruction::CycleCount::Value(v) => v,
                super::instruction::CycleCount::Function(f) => f(self),
            },
            None => 0,
        };
        trace!("Incrementing cycles: {}, for {:?}", cycles, self.last_instruction);
        self.memory.increment_cycle_count(cycles as u64);
    }

    /// Update the last instruction that was executed.
    pub fn set_last_instruction(&mut self, instruction: Instruction<C>) {
        self.last_instruction = Some(instruction);
    }

    pub fn add_instruction_conditions(&mut self, conditions: &Vec<Condition>) {
        for condition in conditions {
            self.instruction_conditions.push_back(condition.to_owned());
        }
    }

    pub fn replace_instruction_conditions(&mut self, conditions: &Vec<Condition>) {
        self.instruction_conditions.clear();
        for condition in conditions {
            self.instruction_conditions.push_back(condition.to_owned());
        }
    }

    pub fn get_next_instruction_condition_expression(&mut self) -> Option<C::SmtExpression> {
        // TODO add error handling
        self.instruction_had_condition = !self.instruction_conditions.is_empty();
        self.instruction_conditions.pop_front().map(|condition| self.get_expr(&condition).unwrap())
    }

    /// Create a state used for testing.
    pub fn create_test_state(
        project: <C::Memory as SmtMap>::ProgramMemory,
        ctx: C::SMT,
        constraints: C::SMT,
        start_pc: u64,
        start_stack: u64,
        hooks: HookContainer<C>,
        state: C::StateContainer,
        architecture: SupportedArchitecture<C::ArchitectureOverride>,
    ) -> Self {
        let pc_reg = start_pc;
        //let ptr_size = project.get_ptr_size();

        let sp_reg = start_stack;
        debug!("Found stack start at addr: {:#X}.", sp_reg);
        let end = project.get_endianness();
        let initial_sp = ctx.from_u64(start_stack, 32);

        let memory = C::Memory::new(ctx, project, 32, end, initial_sp, &state).unwrap();
        let mut registers = HashMap::new();
        let pc_expr = memory.from_u64(pc_reg, 32);
        registers.insert("PC".to_owned(), pc_expr);

        let sp_expr = memory.from_u64(sp_reg, 32);
        registers.insert("SP".to_owned(), sp_expr);

        let mut ret = GAState {
            constraints,
            memory,
            hooks,
            user_state: state,
            count_cycles: true,
            last_instruction: None,
            last_pc: 0,
            continue_in_instruction: None,
            current_instruction: None,
            instruction_counter: 0,
            has_jumped: false,
            instruction_conditions: VecDeque::new(),
            any_counter: 0,
            architecture,
            fp_state: FpState::new(),
            instruction_had_condition: false,
            line_lookup: LineMap::empty(),
            debug_data: None,
        };
        ret.architecture.initiate_state()(&mut ret);

        ret
    }

    /// Set a value to a register.
    pub fn set_register(&mut self, register: impl ToString, expr: C::SmtExpression) -> Result<()> {
        // crude solution should probably change
        if &register.to_string() == "PC" {
            return self
                .hooks
                .writer(&mut self.memory)
                .write_pc(expr.get_constant().ok_or(GAError::NonDeterministicPC)? as u32)
                .map_err(|e| GAError::SmtMemoryError(e).into());
        }
        match self.hooks.writer(&mut self.memory).write_register(&register.to_string(), &expr) {
            ResultOrHook::Hook(hook) => hook(self, expr)?,
            ResultOrHook::Hooks(hooks) => {
                for hook in hooks {
                    hook(self, expr.clone())?;
                }
            }
            ResultOrHook::Result(Err(e)) => return Err(GAError::SmtMemoryError(e).into()),
            _ => {}
        }
        Ok(())
    }

    /// Get the value stored at a register.
    pub fn get_register(&mut self, register: impl ToString) -> Result<C::SmtExpression> {
        // crude solution should probably change
        if &register.to_string() == "PC" {
            return self.hooks.reader(&mut self.memory).read_pc().map_err(|e| GAError::SmtMemoryError(e).into());
        }
        match self.hooks.reader(&mut self.memory).read_register(&register.to_string()) {
            ResultOrHook::Hook(hook) => hook(self),
            ResultOrHook::Hooks(_hooks) => todo!("Handle multiple hooks on read"),
            ResultOrHook::Result(Err(e)) => Err(GAError::SmtMemoryError(e).into()),
            ResultOrHook::Result(o) => Ok(o?),
            _ => todo!("Handle end failure from register."),
        }
    }

    /// Set the value of a flag.
    pub fn set_flag(&mut self, flag: impl ToString, expr: C::SmtExpression) -> Result<()> {
        match self.hooks.writer(&mut self.memory).write_flag(&flag.to_string(), &expr) {
            ResultOrHook::Hook(hook) => hook(self, expr.clone())?,
            ResultOrHook::Hooks(hooks) => {
                for hook in hooks {
                    hook(self, expr.clone())?;
                }
            }
            ResultOrHook::Result(Err(e)) => return Err(GAError::SmtMemoryError(e).into()),
            _ => {}
        }
        trace!("flag {} set to {:?}", flag.to_string(), expr);
        Ok(())
    }

    /// Get the value of a flag.
    pub fn get_flag(&mut self, flag: impl ToString) -> Result<C::SmtExpression> {
        match self.hooks.reader(&mut self.memory).read_flag(&flag.to_string()) {
            ResultOrHook::Hook(hook) => hook(self),
            ResultOrHook::Hooks(_hooks) => todo!("Handle multiple hooks on read"),
            ResultOrHook::Result(Err(e)) => Err(GAError::SmtMemoryError(e).into()),
            ResultOrHook::Result(o) => Ok(o?),
            _ => todo!("Handle end failure from register."),
        }
    }

    /// Get the expression for a condition based on the current flag values.
    pub fn get_expr(&mut self, condition: &Condition) -> Result<C::SmtExpression> {
        Ok(match condition {
            Condition::EQ => self.get_flag("Z".to_owned()).unwrap(),
            Condition::NE => self.get_flag("Z".to_owned()).unwrap().not(),
            Condition::CS => self.get_flag("C".to_owned()).unwrap(),
            Condition::CC => self.get_flag("C".to_owned()).unwrap().not(),
            Condition::MI => self.get_flag("N".to_owned()).unwrap(),
            Condition::PL => self.get_flag("N".to_owned()).unwrap().not(),
            Condition::VS => self.get_flag("V".to_owned()).unwrap(),
            Condition::VC => self.get_flag("V".to_owned()).unwrap().not(),
            Condition::HI => {
                let c = self.get_flag("C".to_owned()).unwrap();
                let nz = self.get_flag("Z".to_owned()).unwrap().not();
                c.and(&nz)
            }
            Condition::LS => {
                let nc = self.get_flag("C".to_owned()).unwrap().not();
                let z = self.get_flag("Z".to_owned()).unwrap();
                nc.or(&z)
            }
            Condition::GE => {
                let n = self.get_flag("N".to_owned()).unwrap();
                let v = self.get_flag("V".to_owned()).unwrap();
                n._eq(&v)
                // n.xor(&v).not()
            }
            Condition::LT => {
                let n = self.get_flag("N".to_owned()).unwrap();
                let v = self.get_flag("V".to_owned()).unwrap();
                n._ne(&v)
            }
            Condition::GT => {
                let z = self.get_flag("Z".to_owned()).unwrap();
                let n = self.get_flag("N".to_owned()).unwrap();
                let v = self.get_flag("V".to_owned()).unwrap();
                z.not().and(&n._eq(&v))
            }
            Condition::LE => {
                let z = self.get_flag("Z".to_owned()).unwrap();
                let n = self.get_flag("N".to_owned()).unwrap();
                let v = self.get_flag("V".to_owned()).unwrap();
                z.or(&n._ne(&v))
            }
            Condition::None => self.memory.from_bool(true),
        })
    }

    /// Get the next instruction based on the address in the PC register.
    pub fn get_next_instruction(&mut self, logger: &mut C::Logger) -> ResultOrTerminate<HookOrInstruction<'_, C>> {
        let pc = match self.memory.get_pc().map(|val| val.get_constant().ok_or(GAError::NonDeterministicPC)) {
            Ok(Ok(val)) => val,
            Ok(Err(err)) => return ResultOrTerminate::Result(Err(err).context("While reading instruction")),
            Err(err) => return ResultOrTerminate::Result(Err(err).context("While reading instruction")),
            // Err(Ok(err)) => return ResultOrTerminate::Result(Err(crate::GAError::InternalError(InternalError::InvalidErrorCombination))),
        } & !(0b1); // Not applicable for all architectures TODO: Fix this.;
        logger.update_delimiter(pc);
        if let Some(conditions) = self.hooks.get_preconditions(&pc) {
            // println!("Running preconditions @ {pc:#x}");
            let conditions = conditions.clone();

            for condition in conditions {
                extract!(Ok(condition(self)), context: "While running precondition");
                let new_pc = self.memory.get_pc().map(|val| val.get_constant().map(|el| el & (!0b1))).ok().flatten(); // Not applicable for all architectures TODO: Fix
                                                                                                                      // this.;
                assert!(new_pc == Some(pc), "Pre-condition altered program counter at {pc:#x}");
            }
        }
        ResultOrTerminate::Result(match self.hooks.get_pc_hooks(pc as u32) {
            ResultOrHook::Hook(hook) => Ok(HookOrInstruction::PcHook(hook)),
            ResultOrHook::Hooks(_) => todo!("Handle multiple hooks on a single address"),
            ResultOrHook::Result(pc) => Ok(HookOrInstruction::Instruction({
                //println!("PC {pc:#x}");
                extract!(Ok(ResultOrTerminate::Result(
                    match self.instruction_from_array_ptr(&extract!(Ok(ResultOrTerminate::Result(match self.memory.get_from_instruction_memory(pc.into()) {
                        Ok(val) => Ok(val),
                        Err(e) => Err(e).context("While reading instruction"),
                    })))) {
                        Ok(val) => Ok(val),
                        Err(e) => Err(e).context("While reading instruction"),
                    }
                )))
            })),
            _ => todo!("Handle out of bounds reads for program memory reads"),
        })
    }

    #[doc(hidden)]
    /// Get the next instruction based on the address in the PC register.
    ///
    /// This function ignores the hooks.
    pub fn get_next_instruction_raw(&self) -> Result<Instruction<C>> {
        let pc = self.memory.get_pc().map(|val| val.get_constant().ok_or(GAError::NonDeterministicPC))?? & !(0b1); // Not applicable for all architectures TODO: Fix this.;
        Ok(self.instruction_from_array_ptr(&self.memory.get_from_instruction_memory(pc)?)?)
    }

    //fn write_word_from_memory_no_static(
    //    &mut self,s
    //    address: &C::SmtExpression,
    //    value: C::SmtExpression,
    //) -> Result<()> {
    //    Ok(self.memory.set(address, value)?)
    //}

    /// Read a word form memory. Will respect the endianness of the project.
    pub fn read_word_from_memory(&mut self, address: &C::SmtExpression) -> ResultOrTerminate<C::SmtExpression> {
        self.memory.get(address, self.memory.get_word_size())
    }

    /// Write a word to memory. Will respect the endianness of the project.
    pub fn write_word_to_memory(&mut self, address: &C::SmtExpression, value: C::SmtExpression) -> Result<()> {
        Ok(self.memory.set(address, value)?)
    }

    pub fn instruction_from_array_ptr(&self, data: &[u8]) -> project::Result<Instruction<C>> {
        self.architecture.translate(data, self).map_err(|el| el.into())
    }

    pub fn reader<'a>(&'a mut self) -> Reader<'a, C> {
        self.hooks.reader(&mut self.memory)
    }

    pub fn writer<'a>(&'a mut self) -> Writer<'a, C> {
        self.hooks.writer(&mut self.memory)
    }

    pub fn debug_string_new_pc(&self) -> String {
        let pc = self.memory.get_pc().expect("Valid program counter").get_constant().expect("Constant program counter") & (!0b1);
        let line = self.line_lookup.lookup(pc);
        match line {
            Some(line) => format!("PC : {pc:#x} -> {line}"),
            None => format!("PC: {pc:#x}"),
        }
    }

    pub fn debug_string_address(&self, address: u64) -> String {
        let pc = address & (!0b1);
        let line = self.line_lookup.lookup(pc);
        match line {
            Some(line) => format!("PC : {pc:#x} -> {line}"),
            None => format!("PC: {pc:#x}"),
        }
    }

    pub fn debug_string(&mut self) -> String {
        let pc = self.last_pc & (!0b1);
        let line = self.line_lookup.lookup(pc);
        let ret = match line {
            Some(line) => format!("PC : {pc:#x} -> {line}"),
            None => format!("PC: {pc:#x}"),
        };
        ret
    }

    pub fn debug_string_fork(&mut self) -> String {
        let pc = self.last_pc & (!0b1);
        let line = self.line_lookup.lookup(pc);
        let ret = match line {
            Some(line) => format!("PC : {pc:#x} -> {line}"),
            None => format!("PC: {pc:#x}"),
        };

        println!("ret");
        ret
    }

    pub fn get_back_trace(&mut self, constraints: &[C::SmtExpression]) -> Option<rust_debug::call_stack::StackFrame<EndianSlice<'static, RunTimeEndian>>> {
        if !self.constraints.is_sat_with_constraints(constraints).ok()? {
            return None;
        }
        let bt = self.debug_data.as_ref().map(|el| {
            el.produce_backtrace::<_, C::ArchitectureOverride, _>(
                &mut DAP {
                    mem: &mut self.memory,
                    constraints,
                },
                &self.architecture,
            )
        });
        bt.flatten()
    }

    /// Tries to convert the contained architecture to the target type.
    ///
    /// If the type is incorrect it returns
    /// [GAError::InvalidArchitectureRequested]
    pub fn try_as_architecture<T>(&mut self) -> crate::Result<&mut T>
    where
        SupportedArchitecture<C::ArchitectureOverride>: TryAsMut<T>,
    {
        self.architecture.try_mut()
    }
}
