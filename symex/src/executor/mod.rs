//! General assembly executor

use general_assembly::{
    condition::Comparison,
    prelude::{DataWord, Operand, Operation},
    shift::Shift,
};
use hashbrown::HashMap;
use hooks::PCHook;
use instruction::Instruction;
use state::{ContinueInsideInstruction, GAState, HookOrInstruction};
use vm::VM;

use crate::{
    debug,
    logging::Logger,
    path_selection::Path,
    smt::{ProgramMemory, SmtExpr, SmtMap, SmtSolver, SolverError},
    trace,
    Composition,
    Result,
};

pub mod hooks;
pub mod instruction;
pub mod state;
pub mod vm;

pub struct GAExecutor<'vm, C: Composition> {
    pub vm: &'vm mut VM<C>,
    pub state: GAState<C>,
    pub project: <C::Memory as SmtMap>::ProgramMemory,
    //current_instruction: Option<Instruction>,
    current_operation_index: usize,
}

pub enum PathResult<C: Composition> {
    Success(Option<C::SmtExpression>),
    Failure(&'static str),
    AssumptionUnsat,
    Suppress,
}

pub(crate) struct AddWithCarryResult<E: SmtExpr> {
    pub(crate) carry_out: E,
    pub(crate) overflow: E,
    pub(crate) result: E,
}

pub enum ResultOrTerminate<V> {
    Result(crate::Result<V>),
    Failure(String),
}

#[cfg(test)]
impl<V> ResultOrTerminate<V> {
    pub fn expect<T: core::fmt::Display>(self, id: T) -> V {
        match self {
            Self::Result(Ok(val)) => val,
            _ => panic!("{}", id),
        }
    }

    pub fn ok(self) -> Option<V> {
        if let ResultOrTerminate::Result(Ok(val)) = self {
            return Some(val);
        }
        panic!()
    }

    pub fn unwrap(self) -> V {
        if let ResultOrTerminate::Result(Ok(val)) = self {
            return val;
        }
        panic!()
    }
    //pub fn unwrap<T: ToString>(self) -> V {
    //    match self {
    //        //Self::Result(Ok(val)) => val,
    //        _ => panic!("{}", id),
    //    }
    //}
}

macro_rules! extract {
    (Ok($tokens:expr_2021)) => {
        match $tokens.into() {
            ResultOrTerminate::Result(Ok(r)) => r,
            ResultOrTerminate::Result(Err(r)) => return ResultOrTerminate::Result(Err(r)),
            ResultOrTerminate::Failure(e) => return ResultOrTerminate::Failure(e),
        }
    };
    ($tokens:expr_2021) => {
        match $tokens {
            ResultOrTerminate::Result(r) => r,
            e => return e,
        }
    };
}

impl<T> From<Result<T>> for ResultOrTerminate<T> {
    fn from(value: Result<T>) -> Self {
        Self::Result(value)
    }
}

impl<'vm, C: Composition> GAExecutor<'vm, C> {
    /// Construct an executor from a state.
    pub fn from_state(state: GAState<C>, vm: &'vm mut VM<C>, project: <C::Memory as SmtMap>::ProgramMemory) -> Self {
        Self {
            vm,
            state,
            project,
            //current_instruction: None,
            current_operation_index: 0,
        }
    }

    pub fn resume_execution(&mut self, logger: &mut C::Logger) -> Result<PathResult<C>> {
        let possible_continue = self.state.continue_in_instruction.to_owned();

        if let Some(i) = possible_continue {
            match self.continue_executing_instruction(&i, logger) {
                ResultOrTerminate::Failure(f) => return Ok(PathResult::Failure(f.leak())),
                ResultOrTerminate::Result(r) => r?,
            };
            self.state.continue_in_instruction = None;
            self.state.set_last_instruction(i.instruction);
        }

        loop {
            let instruction = match self.state.get_next_instruction(logger)? {
                HookOrInstruction::Instruction(v) => v,
                HookOrInstruction::PcHook(hook) => match hook {
                    PCHook::Continue => {
                        debug!("Continuing");
                        let lr = self.state.get_register("LR".to_owned()).unwrap();
                        self.state.set_register("PC".to_owned(), lr)?;
                        continue;
                    }
                    PCHook::EndSuccess => {
                        debug!("Symbolic execution ended successfully");
                        self.state.increment_cycle_count();
                        return Ok(PathResult::Success(None));
                    }
                    PCHook::EndFailure(reason) => {
                        debug!("Symbolic execution ended unsuccessfully");
                        let data = *reason;
                        self.state.increment_cycle_count();
                        return Ok(PathResult::Failure(data));
                    }
                    PCHook::Suppress => {
                        logger.warn("Suppressing path");
                        self.state.increment_cycle_count();
                        return Ok(PathResult::Suppress);
                    }
                    PCHook::Intrinsic(f) => {
                        f(&mut self.state)?;

                        // Set last instruction to empty to no count instruction twice
                        self.state.last_instruction = None;
                        continue;
                    }
                },
            };
            //logger.update_delimiter(self.state.last_pc);

            // Add cycles to cycle count
            self.state.increment_cycle_count();

            trace!("executing instruction: {:?}", instruction);
            match self.execute_instruction(&instruction, logger) {
                ResultOrTerminate::Failure(f) => return Ok(PathResult::Failure(f.leak())),
                ResultOrTerminate::Result(r) => r?,
            }

            self.state.set_last_instruction(instruction);
        }
    }

    pub fn resume_execution_test(&mut self, instructions: usize, logger: &mut C::Logger) -> Result<PathResult<C>> {
        let possible_continue = self.state.continue_in_instruction.to_owned();

        if let Some(i) = possible_continue {
            match self.continue_executing_instruction(&i, logger) {
                ResultOrTerminate::Failure(f) => return Ok(PathResult::Failure(f.leak())),
                ResultOrTerminate::Result(r) => r?,
            };
            self.state.continue_in_instruction = None;
            self.state.set_last_instruction(i.instruction);
        }

        for _idx in 0..instructions {
            let instruction = match self.state.get_next_instruction(logger)? {
                HookOrInstruction::Instruction(v) => v,
                HookOrInstruction::PcHook(hook) => match hook {
                    PCHook::Continue => {
                        debug!("Continuing");
                        let lr = self.state.get_register("LR".to_owned()).unwrap();
                        self.state.set_register("PC".to_owned(), lr)?;
                        continue;
                    }
                    PCHook::EndSuccess => {
                        debug!("Symbolic execution ended successfully");
                        self.state.increment_cycle_count();
                        return Ok(PathResult::Success(None));
                    }
                    PCHook::EndFailure(reason) => {
                        debug!("Symbolic execution ended unsuccessfully");
                        let data = *reason;
                        self.state.increment_cycle_count();
                        return Ok(PathResult::Failure(data));
                    }
                    PCHook::Suppress => {
                        logger.warn("Suppressing path");
                        self.state.increment_cycle_count();
                        return Ok(PathResult::Suppress);
                    }
                    PCHook::Intrinsic(f) => {
                        f(&mut self.state)?;

                        // Set last instruction to empty to no count instruction twice
                        self.state.last_instruction = None;
                        continue;
                    }
                },
            };
            //logger.update_delimiter(self.state.last_pc);

            // Add cycles to cycle count
            self.state.increment_cycle_count();

            trace!("executing instruction: {:?}", instruction);
            match self.execute_instruction(&instruction, logger) {
                ResultOrTerminate::Failure(f) => return Ok(PathResult::Failure(f.leak())),
                ResultOrTerminate::Result(r) => r?,
            }

            self.state.set_last_instruction(instruction);
        }
        return Ok(PathResult::Suppress);
    }

    // Fork execution. Will create a new path with `constraint`.
    fn fork(&mut self, constraint: C::SmtExpression, logger: &mut C::Logger, msg: &'static str) -> Result<()> {
        trace!("Save backtracking path: constraint={:?}", constraint);
        let forked_state = self.state.clone();
        let pc = self.state.last_pc & ((u64::MAX >> 1) << 1);
        let mut new_logger = logger.fork();
        new_logger.warn(format!("{pc:#x} {msg}"));
        let path = Path::new(forked_state, Some(constraint), pc, new_logger);

        self.vm.paths.save_path(path);
        Ok(())
    }

    /// Creates smt expression from a dataword.
    pub(crate) fn get_dexpr_from_dataword(&mut self, data: DataWord) -> C::SmtExpression {
        match data {
            DataWord::Word64(v) => self.state.memory.from_u64(v, 64),
            DataWord::Word32(v) => self.state.memory.from_u64(v as u64, 32),
            DataWord::Word16(v) => self.state.memory.from_u64(v as u64, 16),
            DataWord::Word8(v) => self.state.memory.from_u64(v as u64, 8),
        }
    }

    /// Retrieves a smt expression representing value stored at `address` in
    /// memory.
    fn get_memory(&mut self, address: u64, bits: u32) -> ResultOrTerminate<C::SmtExpression> {
        trace!("Getting memory addr: {:?}", address);
        let addr = self.state.memory.from_u64(address, self.project.get_ptr_size() as usize);
        ResultOrTerminate::Result(match self.state.reader().read_memory(addr, bits as usize) {
            hooks::ResultOrHook::Hook(hook) => hook(&mut self.state, address),
            hooks::ResultOrHook::Hooks(hooks) => {
                if hooks.len() == 1 {
                    return ResultOrTerminate::Result(hooks[0](&mut self.state, address));
                }
                todo!("Handle multiple hooks.");
                //for hook in hooks {
                //    hook(&mut self.state, address)?;
                //}
            }
            hooks::ResultOrHook::Result(result) => result.map_err(|e| e.into()),
            hooks::ResultOrHook::EndFailure(e) => return ResultOrTerminate::Failure(e),
        })
    }

    /// Sets the memory at `address` to `data`.
    fn set_memory(&mut self, data: C::SmtExpression, address: u64, bits: u32) -> ResultOrTerminate<()> {
        trace!("Setting memory addr: {:?}", address);
        let addr = self.state.memory.from_u64(address, self.project.get_ptr_size() as usize);
        ResultOrTerminate::Result(match self.state.writer().write_memory(addr, data.resize_unsigned(bits)) {
            hooks::ResultOrHook::Hook(hook) => hook(&mut self.state, data, address),
            hooks::ResultOrHook::Hooks(hooks) => {
                if hooks.len() == 1 {
                    return ResultOrTerminate::Result(hooks[0](&mut self.state, data, address));
                }
                todo!("Handle multiple hooks (write).");
                //for hook in hooks {
                //    hook(&mut self.state, address)?;
                //}
            }
            hooks::ResultOrHook::Result(result) => result.map_err(|e| e.into()),
            hooks::ResultOrHook::EndFailure(e) => return ResultOrTerminate::Failure(e),
        })
    }

    /// Get the smt expression for a operand.
    pub(crate) fn get_operand_value(&mut self, operand: &Operand, local: &HashMap<String, C::SmtExpression>, logger: &mut C::Logger) -> ResultOrTerminate<C::SmtExpression> {
        let ret = match operand {
            Operand::Register(name) => self.state.get_register(name.to_owned()),
            Operand::Immediate(v) => Ok(self.get_dexpr_from_dataword(v.to_owned())),
            Operand::Address(address, width) => {
                let address = self.get_dexpr_from_dataword(*address);
                let address = extract!(Ok(self.resolve_address(address, local, logger)));
                extract!(self.get_memory(address, *width))
            }
            Operand::AddressWithOffset {
                address: _,
                offset_reg: _,
                width: _,
            } => todo!(),
            Operand::Local(k) => Ok((local.get(k).unwrap()).to_owned()),
            Operand::AddressInLocal(local_name, width) => {
                let address = extract!(Ok(self.get_operand_value(&Operand::Local(local_name.to_owned()), local, logger)));
                let address = extract!(Ok(self.resolve_address(address, local, logger)));
                extract!(self.get_memory(address, *width))
            }
            Operand::Flag(f) => {
                let value = extract!(Ok(self.state.get_flag(f.clone())));
                Ok(value.resize_unsigned(self.project.get_word_size() as u32))
            }
        };
        if let Ok(ret) = &ret {
            if let Some(c) = ret.get_constant() {
                trace!("Operand {operand:?} = {c}");
                let _c = c;
            }
        }

        ResultOrTerminate::Result(ret)
    }

    /// Sets what the operand represents to `value`.
    pub(crate) fn set_operand_value(
        &mut self,
        operand: &Operand,
        value: C::SmtExpression,
        local: &mut HashMap<String, C::SmtExpression>,
        logger: &mut C::Logger,
    ) -> ResultOrTerminate<()> {
        match operand {
            Operand::Register(v) => {
                trace!("Setting register {} to {:?}", v, value);
                let _ = extract!(self.state.set_register(v.to_owned(), value).into());
            }
            Operand::Immediate(_) => panic!(), // Not prohibited change to error later
            Operand::AddressInLocal(local_name, width) => {
                let address = extract!(Ok(self.get_operand_value(&Operand::Local(local_name.to_owned()), local, logger)));
                let address = extract!(Ok(self.resolve_address(address, local, logger)));
                let _ = extract!(Ok(self.set_memory(value.simplify(), address, *width)));
            }
            Operand::Address(address, width) => {
                let address = self.get_dexpr_from_dataword(*address);
                let address = extract!(Ok(self.resolve_address(address, local, logger)));
                extract!(Ok(self.set_memory(value.simplify(), address, *width)));
            }
            Operand::AddressWithOffset {
                address: _,
                offset_reg: _,
                width: _,
            } => todo!(),
            Operand::Local(k) => {
                local.insert(k.to_owned(), value);
            }
            Operand::Flag(f) => {
                // TODO!
                //
                // Might be a good thing to throw an error here if the value is not 0 or 1.
                extract!(Ok(self.state.set_flag(f.clone(), value.resize_unsigned(1).simplify())));
            }
        }
        ResultOrTerminate::Result(Ok(()))
    }

    fn resolve_address(&mut self, address: C::SmtExpression, local: &HashMap<String, C::SmtExpression>, logger: &mut C::Logger) -> Result<u64> {
        match &address.get_constant() {
            Some(addr) => Ok(*addr),
            None => {
                debug!("Address {:?} non deterministic!", address);
                // Find all possible addresses
                let addresses = self.state.constraints.get_values(&address, 255)?;

                let addresses = match addresses {
                    crate::smt::Solutions::Exactly(a) => Ok(a),
                    // NOTE: We should likely not break here but allow for a configurable number
                    // paths.
                    crate::smt::Solutions::AtLeast(_) => Err(SolverError::TooManySolutions),
                }?;

                if addresses.len() == 1 {
                    return Ok(addresses[0].get_constant().unwrap());
                }

                if addresses.is_empty() {
                    return Err(SolverError::Unsat.into());
                }

                // Create paths for all but the first address
                for addr in &addresses[1..] {
                    if self.current_operation_index < self.state.current_instruction.as_ref().unwrap().operations.len() - 1 {
                        self.state.continue_in_instruction = Some(ContinueInsideInstruction {
                            instruction: self.state.current_instruction.as_ref().unwrap().to_owned(),
                            index: self.current_operation_index,
                            local: local.clone(),
                        })
                    }

                    let constraint = address.eq(addr);
                    self.fork(constraint, logger, "Forking due to non concrete address")?;
                }

                // assert first address and return concrete
                let concrete_address = &addresses[0];
                self.state.constraints.assert(&address.eq(concrete_address));
                Ok(concrete_address.get_constant().unwrap())
            }
        }
    }

    fn continue_executing_instruction(&mut self, inst_to_continue: &ContinueInsideInstruction<C>, logger: &mut C::Logger) -> ResultOrTerminate<()> {
        let mut local = inst_to_continue.local.to_owned();
        self.state.current_instruction = Some(inst_to_continue.instruction.to_owned());
        for i in inst_to_continue.index..inst_to_continue.instruction.operations.len() {
            let operation = &inst_to_continue.instruction.operations[i];
            self.current_operation_index = i;
            extract!(Ok(self.execute_operation(operation, &mut local, logger)));
        }
        ResultOrTerminate::Result(Ok(()))
    }

    /// Execute a single instruction.
    pub(crate) fn execute_instruction(&mut self, i: &Instruction<C>, logger: &mut C::Logger) -> ResultOrTerminate<()> {
        // update last pc
        let new_pc = extract!(Ok(self.state.get_register("PC".to_owned())));
        self.state.last_pc = new_pc.get_constant().unwrap();
        logger.update_delimiter(self.state.last_pc);

        // Always increment pc before executing the operations
        extract!(Ok(self.state.set_register(
            "PC".to_owned(),
            new_pc.add(&self.state.memory.from_u64((i.instruction_size / 8) as u64, self.project.get_ptr_size() as usize,)),
        )));
        let new_pc = extract!(Ok(self.state.get_register("PC".to_owned())));
        logger.update_delimiter(new_pc.get_constant().unwrap());

        // reset has branched before execution of instruction.
        self.state.reset_has_jumped();

        // increment instruction count before execution
        // so that forked path count this instruction
        self.state.increment_instruction_count();

        self.state.current_instruction = Some(i.to_owned());

        // check if we should actually execute the instruction
        let should_run = match self.state.get_next_instruction_condition_expression() {
            Some(c) => match c.get_constant_bool() {
                Some(constant_c) => constant_c,
                None => {
                    let true_possible = extract!(Ok(self.state.constraints.is_sat_with_constraint(&c).map_err(|e| e.into())));
                    let false_possible = extract!(Ok(self.state.constraints.is_sat_with_constraint(&c.not()).map_err(|e| e.into())));

                    if true_possible && false_possible {
                        extract!(Ok(self.fork(c.not(), logger, "Forking due to conditional execution, both options are possible")));
                        self.state.constraints.assert(&c);
                    }

                    true_possible
                }
            },
            None => true,
        };

        if should_run {
            // initiate local variable storage
            let mut local: HashMap<String, _> = HashMap::new();
            for (n, operation) in i.operations.iter().enumerate() {
                self.current_operation_index = n;
                extract!(Ok(self.execute_operation(operation, &mut local, logger)));
            }
        }

        ResultOrTerminate::Result(Ok(()))
    }

    /// Execute a single operation or all operations contained inside an
    /// operation.
    pub(crate) fn execute_operation(&mut self, operation: &Operation, local: &mut HashMap<String, C::SmtExpression>, logger: &mut C::Logger) -> ResultOrTerminate<()> {
        trace!(
            "PC: {:#x} -> Executing operation: {:?}",
            self.state.memory.get_pc().unwrap().get_constant().unwrap(),
            operation
        );
        match operation {
            Operation::Nop => (), // nop so do nothing
            Operation::Move { destination, source } => {
                let value = extract!(Ok(self.get_operand_value(source, local, logger)));
                extract!(Ok(self.set_operand_value(destination, value.clone(), local, logger)));
            }
            Operation::Add { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.add(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::SAdd {
                destination,
                operand1,
                operand2,
                signed,
            } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = match signed {
                    true => op1.sadds(&op2),
                    false => op1.uadds(&op2),
                };
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Sub { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.sub(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::SSub {
                destination,
                operand1,
                operand2,
                signed,
            } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = match signed {
                    true => op1.ssubs(&op2),
                    false => op1.usubs(&op2),
                };
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Mul { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.mul(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::UDiv { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.udiv(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::SDiv { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.sdiv(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::And { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.and(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Or { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.or(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Xor { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let result = op1.xor(&op2);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Not { destination, operand } => {
                let op = extract!(Ok(self.get_operand_value(operand, local, logger)));

                let result = op.not();
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Shift {
                destination,
                operand,
                shift_n,
                shift_t,
            } => {
                let value = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let shift_amount = extract!(Ok(self.get_operand_value(shift_n, local, logger)));
                let result = match shift_t {
                    Shift::Lsl | Shift::Lsr | Shift::Asr => value.shift(&shift_amount, shift_t.clone()),
                    Shift::Rrx => {
                        let ret = value
                            .and(&shift_amount.sub(&self.state.memory.from_u64(1, 32)))
                            .shift(&self.state.memory.from_u64(1, 32), Shift::Lsr)
                            .simplify();
                        ret.or(&self
                            .state
                            // Set the carry bit right above the last bit
                            .get_flag("C".to_owned())
                            .unwrap()
                            .shift(&shift_amount.add(&self.state.memory.from_u64(1, 32)), Shift::Lsl))
                    }
                    Shift::Ror => {
                        let word_size = self.state.memory.from_u64(self.project.get_word_size() as u64, self.project.get_word_size() as usize);
                        value.shift(&shift_amount, Shift::Lsr).or(&value.shift(&word_size.sub(&shift_amount), Shift::Lsr))
                    }
                };
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Sl { destination, operand, shift } => {
                let value = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let shift_amount = extract!(Ok(self.get_operand_value(shift, local, logger)));
                let result = value.shift(&shift_amount, Shift::Lsl);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Srl { destination, operand, shift } => {
                let value = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let shift_amount = extract!(Ok(self.get_operand_value(shift, local, logger)));
                let result = value.shift(&shift_amount, Shift::Lsr);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Sra { destination, operand, shift } => {
                let value = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let shift_amount = extract!(Ok(self.get_operand_value(shift, local, logger)));
                let result = value.shift(&shift_amount, Shift::Asr);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Sror { destination, operand, shift } => {
                let word_size = self.state.memory.from_u64(self.project.get_word_size() as u64, self.project.get_word_size() as usize);
                let value = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let shift = extract!(Ok(self.get_operand_value(shift, local, logger))).srem(&word_size);
                let result = value.shift(&shift, Shift::Lsr).or(&value.shift(&word_size.sub(&shift), Shift::Lsl));
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::ConditionalJump { destination, condition } => {
                let dest_value = extract!(Ok(self.get_operand_value(destination, local, logger)));
                let c = extract!(Ok(self.state.get_expr(condition))).simplify();
                trace!("conditional expr: {:?}", c);
                // if constant just jump
                if let Some(constant_c) = c.get_constant_bool() {
                    if constant_c {
                        self.state.set_has_jumped();
                        let destination = dest_value;
                        extract!(Ok(self.state.set_register("PC".to_owned(), destination)));
                    }
                    return ResultOrTerminate::Result(Ok(()));
                }

                let true_possible = extract!(Ok(self.state.constraints.is_sat_with_constraint(&c).map_err(|e| e.into())));
                let false_possible = extract!(Ok(self.state.constraints.is_sat_with_constraint(&c.not()).map_err(|e| e.into())));
                trace!("true possible: {} false possible: {}", true_possible, false_possible);

                let destination: C::SmtExpression = extract!(Ok(match (true_possible, false_possible) {
                    (true, true) => {
                        if self.current_operation_index < (self.state.current_instruction.as_ref().unwrap().operations.len() - 1) {
                            self.state.continue_in_instruction = Some(ContinueInsideInstruction {
                                instruction: self.state.current_instruction.as_ref().unwrap().to_owned(),
                                index: self.current_operation_index + 1,
                                local: local.to_owned(),
                            });
                        }
                        extract!(Ok(self.fork(c.not(), logger, "Forking paths due to conditional branch")));
                        self.state.constraints.assert(&c);
                        self.state.set_has_jumped();
                        Ok(dest_value)
                    }
                    (true, false) => {
                        self.state.set_has_jumped();
                        Ok(dest_value)
                    }
                    (false, true) => Ok(extract!(Ok(self.state.get_register("PC".to_owned())))), /* safe to assume PC exist */
                    (false, false) => Err(SolverError::Unsat),
                }
                .map_err(|e| e.into())));

                extract!(Ok(self.state.set_register("PC".to_owned(), destination)));
            }
            Operation::ConditionalExecution { conditions } => {
                //self.state.add_instruction_conditions(conditions);
                self.state.replace_instruction_conditions(conditions);
            }
            Operation::SetNFlag(operand) => {
                let value = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let shift = self.state.memory.from_u64((self.project.get_word_size() - 1) as u64, 32);
                let result = value.shift(&shift, Shift::Lsr).resize_unsigned(1);
                extract!(Ok(self.state.set_flag("N".to_owned(), result)));
            }
            Operation::SetZFlag(operand) => {
                let value = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let result = value.eq(&self.state.memory.from_u64(0, self.project.get_word_size() as usize));
                extract!(Ok(self.state.set_flag("Z".to_owned(), result)));
            }
            Operation::SetCFlag { operand1, operand2, sub, carry } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let one = self.state.memory.from_u64(1, self.project.get_word_size() as usize);

                let result = match (sub, carry) {
                    (true, true) => {
                        // I do not now if this part is used in any ISA but it is here for
                        // completeness.
                        let carry_in = extract!(Ok(self.state.get_flag("C".to_owned())));
                        let op2 = op2.not();

                        // Check for carry on twos complement of op2
                        // Fixes edge-case op2 = 0.
                        let c2 = op2.uaddo(&one);

                        add_with_carry(&op1, &op2.add(&one), &carry_in, self.project.get_word_size()).carry_out.or(&c2)
                    }
                    (true, false) => {
                        let lhs = op1;
                        let rhs = op2.not();
                        trace!("SetCFlag: computatins done, add_with_cary next");
                        add_with_carry(&lhs, &rhs, &one, self.project.get_word_size()).carry_out
                    }
                    (false, true) => {
                        let carry_in = self.state.get_flag("C".to_owned()).unwrap();
                        add_with_carry(&op1, &op2, &carry_in, self.project.get_word_size()).carry_out
                    }
                    (false, false) => op1.uaddo(&op2),
                };

                extract!(Ok(self.state.set_flag("C".to_owned(), result)));
            }
            Operation::SetVFlag { operand1, operand2, sub, carry } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let one = self.state.memory.from_u64(1, self.project.get_word_size() as usize);

                let result = match (sub, carry) {
                    (true, true) => {
                        // slightly wrong at op2 = 0
                        let carry_in = self.state.get_flag("C".to_owned()).unwrap();
                        let op2 = op2.not().add(&one);
                        add_with_carry(&op1, &op2, &carry_in, self.project.get_word_size()).overflow
                    }
                    (true, false) => add_with_carry(&op1, &op2.not(), &one, self.project.get_word_size()).overflow,
                    (false, true) => {
                        let carry_in = self.state.get_flag("C".to_owned()).unwrap();
                        add_with_carry(&op1, &op2, &carry_in, self.project.get_word_size()).overflow
                    }
                    (false, false) => op1.saddo(&op2),
                };

                extract!(Ok(self.state.set_flag("V".to_owned(), result)));
            }
            Operation::ForEach { operands: _, operations: _ } => {
                todo!()
            }
            Operation::ZeroExtend {
                destination,
                operand,
                bits,
                target_bits,
            } => {
                trace!("Running zero extend");
                let op = extract!(Ok(self.get_operand_value(operand, local, logger)));
                trace!("Op {op:?}");
                let valid_bits = op.resize_unsigned(*bits);
                trace!("ValidBits {valid_bits:?}");
                let result = valid_bits.zero_ext(*target_bits);
                trace!("Result {result:?}");
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::SignExtend {
                destination,
                operand,
                sign_bit,
                target_size,
            } => {
                let op = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let valid_bits = op.resize_unsigned(*sign_bit);
                let result = valid_bits.sign_ext(*target_size);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Resize { destination, operand, bits } => {
                let op = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let result = op.resize_unsigned(*bits);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::Adc { destination, operand1, operand2 } => {
                let op1 = extract!(Ok(self.get_operand_value(operand1, local, logger)));
                let op2 = extract!(Ok(self.get_operand_value(operand2, local, logger)));
                let carry = self.state.get_flag("C".to_owned()).unwrap().zero_ext(self.project.get_word_size() as u32);
                let result = add_with_carry(&op1, &op2, &carry, self.project.get_word_size()).result;
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            // These need to be tested are way to complex to be trusted
            Operation::SetCFlagShiftLeft { operand, shift } => {
                let op = extract!(Ok(self.get_operand_value(operand, local, logger))).zero_ext(1 + self.project.get_word_size() as u32);
                trace!("Getting worked");
                let shift = extract!(Ok(self.get_operand_value(shift, local, logger))).zero_ext(1 + self.project.get_word_size() as u32);
                trace!("Getting2 worked");
                let result = op.shift(&shift, Shift::Lsl);
                trace!("Shift ");
                let carry = result
                    .shift(
                        &self.state.memory.from_u64(self.project.get_word_size() as u64, self.project.get_word_size() as usize + 1),
                        Shift::Lsr,
                    )
                    .resize_unsigned(1);
                trace!("Shift ");
                extract!(Ok(self.state.set_flag("C".to_owned(), carry)));
                trace!("set");
            }
            Operation::SetCFlagSrl { operand, shift } => {
                let op = extract!(Ok(self.get_operand_value(operand, local, logger)))
                    .zero_ext(1 + self.project.get_word_size() as u32)
                    .shift(&self.state.memory.from_u64(1, 1 + self.project.get_word_size() as usize), Shift::Lsl);
                let shift = extract!(Ok(self.get_operand_value(shift, local, logger))).zero_ext(1 + self.project.get_word_size() as u32);
                let result = op.shift(&shift, Shift::Lsr);
                let carry = result.resize_unsigned(1);
                extract!(Ok(self.state.set_flag("C".to_owned(), carry)));
            }
            Operation::SetCFlagSra { operand, shift } => {
                let op = extract!(Ok(self.get_operand_value(operand, local, logger)))
                    .zero_ext(1 + self.project.get_word_size() as u32)
                    .shift(&self.state.memory.from_u64(1, 1 + self.project.get_word_size() as usize), Shift::Lsl);
                let shift = extract!(Ok(self.get_operand_value(shift, local, logger))).zero_ext(1 + self.project.get_word_size() as u32);
                let result = op.shift(&shift, Shift::Asr);
                let carry = result.resize_unsigned(1);
                extract!(Ok(self.state.set_flag("C".to_owned(), carry)));
            }
            Operation::SetCFlagRor(operand) => {
                // this is right for armv6-m but may be wrong for other architectures
                let result = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let word_size_minus_one = self.state.memory.from_u64(self.project.get_word_size() as u64 - 1, self.project.get_word_size() as usize);
                // result = srl(op, shift) OR sll(op, word_size - shift)
                let c = result.shift(&word_size_minus_one, Shift::Lsr).resize_unsigned(1);
                extract!(Ok(self.state.set_flag("C".to_owned(), c)));
            }
            Operation::CountOnes { destination, operand } => {
                let operand = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let result = count_ones(&operand, &self.state, self.project.get_word_size() as usize);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::CountZeroes { destination, operand } => {
                let operand = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let result = count_zeroes(&operand, &self.state, self.project.get_word_size() as usize);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::CountLeadingOnes { destination, operand } => {
                let operand = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let result = count_leading_ones(&operand, &self.state, self.project.get_word_size() as usize);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::CountLeadingZeroes { destination, operand } => {
                let operand = extract!(Ok(self.get_operand_value(operand, local, logger)));
                let result = count_leading_zeroes(&operand, &self.state, self.project.get_word_size() as usize);
                extract!(Ok(self.set_operand_value(destination, result, local, logger)));
            }
            Operation::BitFieldExtract {
                destination,
                operand,
                start_bit,
                stop_bit,
            } => {
                assert!(start_bit <= stop_bit, "Tried to extract from {start_bit} until {stop_bit}");
                trace!("Running bitfieldextract");
                let operand = extract!(Ok(self.get_operand_value(operand, local, logger)));
                trace!("Got operand {operand:?}");
                let mask: u64 = if start_bit == stop_bit {
                    1
                } else {
                    // This seems a bit strange, but if we want bit 0 -> 2 we should extract 0b111
                    // = 1 << 3 - 1 => 1 << (2 - 0 + 1) - 1
                    (1 << (*stop_bit - *start_bit + 1)) - 1
                };
                trace!("Masking {}", mask);

                let operand = operand
                    .shift(&self.state.memory.from_u64(*start_bit as u64, operand.len() as usize), Shift::Lsr)
                    .and(&self.state.memory.from_u64(mask, operand.len() as usize))
                    .simplify();
                extract!(Ok(self.set_operand_value(destination, operand, local, logger)));
            }
            Operation::Ite {
                lhs,
                rhs,
                operation,
                then,
                otherwise,
            } => {
                let lhs = extract!(Ok(self.get_operand_value(lhs, local, logger)));
                let rhs = extract!(Ok(self.get_operand_value(rhs, local, logger)));
                let result = match operation {
                    Comparison::Eq => lhs.eq(&rhs),
                    Comparison::UGt => lhs.ugt(&rhs),
                    Comparison::ULt => lhs.ult(&rhs),
                    Comparison::UGeq => lhs.ugte(&rhs),
                    Comparison::ULeq => lhs.ulte(&rhs),
                    Comparison::SGt => lhs.sgt(&rhs),
                    Comparison::SLt => lhs.slt(&rhs),
                    Comparison::SGeq => lhs.sgte(&rhs),
                    Comparison::SLeq => lhs.slte(&rhs),
                    Comparison::Neq => lhs.eq(&rhs).not(),
                };

                let true_possible = extract!(Ok(self.state.constraints.is_sat_with_constraint(&result).map_err(|e| e.into())));
                let false_possible = extract!(Ok(self.state.constraints.is_sat_with_constraint(&result.not()).map_err(|e| e.into())));
                match (true_possible, false_possible) {
                    (true, false) => {
                        for operation in then {
                            let _ = extract!(Ok(self.execute_operation(operation, local, logger)));
                        }
                    }
                    (false, true) => {
                        for operation in otherwise {
                            let _ = extract!(Ok(self.execute_operation(operation, local, logger)));
                        }
                    }
                    (true, true) => {
                        if self.current_operation_index < (self.state.current_instruction.as_ref().unwrap().operations.len()) {
                            self.state.continue_in_instruction = Some(ContinueInsideInstruction {
                                instruction: self.state.current_instruction.as_ref().unwrap().to_owned(),
                                // We want to re-run the same instruction.
                                index: self.current_operation_index,
                                local: local.to_owned(),
                            });
                        }
                        extract!(Ok(self.fork(
                            result.eq(&self.state.memory.from_bool(false)),
                            logger,
                            "Forking as both paths in ITE instruction is possible"
                        )));
                        self.state.constraints.assert(&result.eq(&self.state.memory.from_bool(true)));
                        for operation in then {
                            let _ = extract!(Ok(self.execute_operation(operation, local, logger)));
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Operation::Abort { error } => return ResultOrTerminate::Failure(error.to_string()),
        }

        ResultOrTerminate::Result(Ok(()))
    }
}

pub(crate) fn count_ones<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: usize) -> C::SmtExpression {
    let mut count = ctx.memory.from_u64(0, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in 0..word_size {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask);
        count = count.add(&to_add);
    }
    count
}

pub(crate) fn count_zeroes<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: usize) -> C::SmtExpression {
    let input = input.not();
    let mut count = ctx.memory.from_u64(0, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in 0..word_size {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask);
        count = count.add(&to_add);
    }
    count
}

pub(crate) fn count_leading_ones<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: usize) -> C::SmtExpression {
    let mut count = ctx.memory.from_u64(0, word_size);
    let mut stop_count_mask = ctx.memory.from_u64(1, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in (0..word_size).rev() {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask).and(&stop_count_mask);
        stop_count_mask = to_add.clone();
        count = count.add(&to_add);
    }
    count
}

pub(crate) fn count_leading_zeroes<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: usize) -> C::SmtExpression {
    let input = input.not();
    let mut count = ctx.memory.from_u64(0, word_size);
    let mut stop_count_mask = ctx.memory.from_u64(1, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in (0..word_size).rev() {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask).and(&stop_count_mask);
        stop_count_mask = to_add.clone();
        count = count.add(&to_add);
    }
    count
}

/// Does an add with carry and returns result, carry out and overflow like a
/// hardware adder.
pub(crate) fn add_with_carry<E: SmtExpr>(op1: &E, op2: &E, carry_in: &E, word_size: usize) -> AddWithCarryResult<E> {
    let carry_in = carry_in.resize_unsigned(1);
    let c1 = op2.uaddo(&carry_in.zero_ext(word_size as u32));
    let op2 = op2.add(&carry_in.zero_ext(word_size as u32));
    let result = op1.add(&op2);
    let carry = op1.uaddo(&op2).or(&c1);
    let overflow = op1.saddo(&op2);
    AddWithCarryResult {
        carry_out: carry,
        overflow,
        result,
    }
}

#[cfg(test)]
mod test {

    use std::u32;

    use general_assembly::{
        condition::Condition,
        operand::{DataWord, Operand},
        operation::Operation,
    };
    use hashbrown::HashMap;
    use transpiler::pseudo;

    use super::{state::GAState, vm::VM};
    use crate::{
        arch::{arm::v6::ArmV6M, Architecture},
        defaults::bitwuzla::DefaultCompositionNoLogger,
        executor::{
            add_with_carry,
            count_leading_ones,
            count_leading_zeroes,
            count_ones,
            count_zeroes,
            hooks::HookContainer,
            instruction::{CycleCount, Instruction},
            GAExecutor,
        },
        logging::NoLogger,
        project::Project,
        smt::{
            //smt_boolector::{Boolector, BoolectorExpr},
            SmtExpr,
            SmtMap,
            SmtSolver,
        },
        Endianness,
        WordSize,
    };

    #[test]
    fn test_count_ones_concrete() {
        let ctx = crate::smt::bitwuzla::Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx,
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(ArmV6M::new()),
        );
        let num1 = state.memory.from_u64(1, 32);
        let num32 = state.memory.from_u64(32, 32);
        let numff = state.memory.from_u64(0xff, 32);
        let result = count_ones(&num1, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result = count_ones(&num32, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result = count_ones(&numff, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 8);
    }

    #[test]
    fn test_count_ones_symbolic() {
        let ctx = crate::smt::bitwuzla::Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(ArmV6M::new()),
        );
        let any_u32 = ctx.unconstrained(32, "any1");
        let num_0x100 = ctx.from_u64(0x100, 32);
        let num_8 = ctx.from_u64(8, 32);
        ctx.assert(&any_u32.ult(&num_0x100));
        let result = count_ones(&any_u32, &state, 32);
        let result_below_or_equal_8 = result.ulte(&num_8);
        let result_above_8 = result.ugt(&num_8);
        let can_be_below_or_equal_8 = ctx.is_sat_with_constraint(&result_below_or_equal_8).unwrap();
        let can_be_above_8 = ctx.is_sat_with_constraint(&result_above_8).unwrap();
        assert!(can_be_below_or_equal_8);
        assert!(!can_be_above_8);
    }

    #[test]
    fn test_count_zeroes_concrete() {
        let ctx = crate::smt::bitwuzla::Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(ArmV6M::new()),
        );
        let num1 = state.memory.from_u64(!1, 32);
        let num32 = state.memory.from_u64(!32, 32);
        let numff = state.memory.from_u64(!0xff, 32);
        let result = count_zeroes(&num1, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result = count_zeroes(&num32, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result = count_zeroes(&numff, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 8);
    }

    #[test]
    fn test_count_leading_ones_concrete() {
        let ctx = crate::smt::bitwuzla::Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(ArmV6M::new()),
        );
        let input = state.memory.from_u64(0b1000_0000, 8);
        let result = count_leading_ones(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 1);
        let input = state.memory.from_u64(0b1100_0000, 8);
        let result = count_leading_ones(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 2);
        let input = state.memory.from_u64(0b1110_0011, 8);
        let result = count_leading_ones(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 3);
    }

    #[test]
    fn test_count_leading_zeroes_concrete() {
        let ctx = crate::smt::bitwuzla::Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(ArmV6M::new()),
        );
        let input = state.memory.from_u64(!0b1000_0000, 8);
        let result = count_leading_zeroes(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 1);
        let input = state.memory.from_u64(!0b1100_0000, 8);
        let result = count_leading_zeroes(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 2);
        let input = state.memory.from_u64(!0b1110_0011, 8);
        let result = count_leading_zeroes(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 3);
    }

    #[test]
    fn test_add_with_carry() {
        let ctx = crate::smt::bitwuzla::Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(ArmV6M::new()),
        );
        let one_bool = state.memory.from_bool(true);
        let zero_bool = state.memory.from_bool(false);
        let zero = state.memory.from_u64(0, 32);
        let num42 = state.memory.from_u64(42, 32);
        let num16 = state.memory.from_u64(16, 32);
        let umax = state.memory.from_u64(u32::MAX as u64, 32);
        let smin = state.memory.from_u64(i32::MIN as u64, 32);
        let smax = state.memory.from_u64(i32::MAX as u64, 32);

        // simple add
        let result = add_with_carry(&num42, &num16, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 58);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // simple sub
        let result = add_with_carry(&num42, &num16.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 26);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // signed sub negative result
        let result = add_with_carry(&num16, &num42.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), (-26i32 as u32) as u64);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // unsigned overflow
        let result = add_with_carry(&umax, &num16, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 15 as u64);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // signed overflow
        let result = add_with_carry(&smax, &num16, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 2147483663);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(result.overflow.get_constant_bool().unwrap());

        // signed underflow
        let result = add_with_carry(&smin, &num16.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 2147483632);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(result.overflow.get_constant_bool().unwrap());

        // zero add
        let result = add_with_carry(&num16, &zero, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 16);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // zero sub
        let result = add_with_carry(&num16, &zero.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 16);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());
    }

    fn setup_test_vm() -> VM<DefaultCompositionNoLogger> {
        let ctx = crate::smt::bitwuzla::Bitwuzla::new();
        let project_global = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project: &'static Project = Box::leak(project_global);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(ArmV6M::new()),
        );
        VM::new_test_vm(project, state, NoLogger).unwrap()
    }

    #[test]
    fn test_move() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let mut local = HashMap::new();
        let operand_r0 = Operand::Register("R0".to_owned());

        // move imm into reg
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0 = executor.get_operand_value(&operand_r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42);

        // move reg to local
        let local_r0 = Operand::Local("R0".to_owned());
        let operation = Operation::Move {
            destination: local_r0.clone(),
            source: operand_r0.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0 = executor.get_operand_value(&local_r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42);

        // Move immediate to local memory addr
        let imm = Operand::Immediate(DataWord::Word32(23));
        let memory_op = Operand::AddressInLocal("R0".to_owned(), 32);
        let operation = Operation::Move {
            destination: memory_op.clone(),
            source: imm.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let dexpr_addr = executor.get_dexpr_from_dataword(DataWord::Word32(42));
        let in_memory_value = executor.state.read_word_from_memory(&dexpr_addr).unwrap().get_constant().unwrap();

        assert_eq!(in_memory_value, 23);

        // Move from memory to a local
        let operation = Operation::Move {
            destination: local_r0.clone(),
            source: memory_op.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let local_value = executor.get_operand_value(&local_r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(local_value, 23);
    }

    #[test]
    fn test_add() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let mut local = HashMap::new();

        let r0 = Operand::Register("R0".to_owned());
        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_umax = Operand::Immediate(DataWord::Word32(u32::MAX));
        let imm_16 = Operand::Immediate(DataWord::Word32(16));
        let imm_minus70 = Operand::Immediate(DataWord::Word32(-70i32 as u32));

        // test simple add
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 58);

        // Test add with same operand and destination
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: r0.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 74);

        // Test add with negative number
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus70.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, (-28i32 as u32) as u64);

        // Test add overflow
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_umax.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 41);
    }

    #[test]
    fn test_adc() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let mut local = HashMap::new();

        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_12 = Operand::Immediate(DataWord::Word32(12));
        let imm_umax = Operand::Immediate(DataWord::Word32(u32::MAX));
        let r0 = Operand::Register("R0".to_owned());

        let true_dexpr = executor.state.memory.from_bool(true);
        let false_dexpr = executor.state.memory.from_bool(false);

        // test normal add
        executor.state.set_flag("C".to_owned(), false_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 54);

        // test add with overflow
        executor.state.set_flag("C".to_owned(), false_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_umax.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 11);

        // test add with carry in
        executor.state.set_flag("C".to_owned(), true_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 55);
    }

    #[test]
    fn test_sub() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let mut local = HashMap::new();

        let r0 = Operand::Register("R0".to_owned());
        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_imin = Operand::Immediate(DataWord::Word32(i32::MIN as u32));
        let imm_16 = Operand::Immediate(DataWord::Word32(16));
        let imm_minus70 = Operand::Immediate(DataWord::Word32(-70i32 as u32));

        // Test simple sub
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 26);

        // Test sub with same operand and destination
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: r0.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 10);

        // Test sub with negative number
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus70.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 112);

        // Test sub underflow
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_imin.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, ((i32::MIN) as u32 + 42) as u64);
    }

    #[test]
    fn test_mul() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let mut local = HashMap::new();

        let r0 = Operand::Register("R0".to_owned());
        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_minus_42 = Operand::Immediate(DataWord::Word32(-42i32 as u32));
        let imm_16 = Operand::Immediate(DataWord::Word32(16));
        let imm_minus_16 = Operand::Immediate(DataWord::Word32(-16i32 as u32));

        // simple multiplication
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 672);

        // multiplication right minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value as u32, -672i32 as u32);

        // multiplication left minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_minus_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value as u32, -672i32 as u32);

        // multiplication both minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_minus_42.clone(),
            operand2: imm_minus_16.clone(),
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 672);
    }

    #[test]
    fn test_set_v_flag() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let mut local = HashMap::new();

        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_12 = Operand::Immediate(DataWord::Word32(12));
        let imm_imin = Operand::Immediate(DataWord::Word32(i32::MIN as u32));
        let imm_imax = Operand::Immediate(DataWord::Word32(i32::MAX as u32));

        // no overflow
        let operation = Operation::SetVFlag {
            operand1: imm_42.clone(),
            operand2: imm_12.clone(),
            sub: true,
            carry: false,
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(!v_flag);

        // overflow
        let operation = Operation::SetVFlag {
            operand1: imm_imax.clone(),
            operand2: imm_12.clone(),
            sub: false,
            carry: false,
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(v_flag);

        // underflow
        let operation = Operation::SetVFlag {
            operand1: imm_imin.clone(),
            operand2: imm_12.clone(),
            sub: true,
            carry: false,
        };
        executor.execute_operation(&operation, &mut local, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(v_flag);
    }

    #[test]
    fn test_conditional_execution() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let imm_0 = Operand::Immediate(DataWord::Word32(0));
        let imm_1 = Operand::Immediate(DataWord::Word32(1));
        let local = HashMap::new();
        let r0 = Operand::Register("R0".to_owned());

        let program1 = vec![
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::SetZFlag(imm_0.clone())],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::ConditionalExecution {
                    conditions: vec![Condition::EQ, Condition::NE],
                }],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::Move {
                    destination: r0.clone(),
                    source: imm_1,
                }],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::Move {
                    destination: r0.clone(),
                    source: imm_0,
                }],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
        ];

        for p in program1 {
            executor.execute_instruction(&p, &mut crate::logging::NoLogger).ok();
        }

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).ok().unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 1);
    }

    #[test]
    fn test_ite() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let imm_0 = Operand::Immediate(DataWord::Word32(0));
        let imm_1 = Operand::Immediate(DataWord::Word32(1));
        let local = HashMap::new();
        let r0 = Operand::Register("R0".to_owned());
        let program1 = vec![Instruction {
            instruction_size: 32,
            operations: pseudo!([
                Ite(
                    imm_0 == r0,
                    {
                        r0 = imm_1;
                        Ite(
                            imm_0 != r0,
                            {
                                r0 = imm_0;
                            },
                            {
                            }
                        );
                    },
                    {
                        r0 = imm_1;
                    }
                );
            ]),
            max_cycle: CycleCount::Value(0),
            memory_access: false,
        }];

        for p in program1.clone() {
            executor.execute_instruction(&p, &mut crate::logging::NoLogger).ok();
        }
        assert!(executor.state.constraints.ctx == executor.state.memory.ram.ctx);

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).ok().unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 0);

        if let Some(path) = executor.vm.paths.get_path() {
            let mut path = path.clone();
            let mut executor = GAExecutor::from_state(path.state, executor.vm, project);
            assert!(executor.state.constraints.ctx == executor.state.memory.ram.ctx);

            for constraint in path.constraints.clone() {
                println!("Asserting {constraint:?}");
                executor.state.constraints.assert(&constraint);
            }

            executor.resume_execution_test(0, &mut path.logger).unwrap();

            let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).ok().unwrap().get_constant().unwrap();
            assert_eq!(r0_value, 1);
        }

        panic!()
    }
}
