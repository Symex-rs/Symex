use anyhow::Context;
use general_assembly::extension::ieee754::{Operand, OperandStorage, OperandType, Operations, RoundingMode};
use hashbrown::HashMap;

use crate::{
    executor::{hooks::ResultOrHook, GAExecutor, ResultOrTerminate},
    extract,
    memory::MemoryError,
    smt::{SmtExpr, SmtFPExpr, SmtMap, SmtSolver},
    Composition,
    GAError,
    InternalError,
};

/// The state required to perform floating point operations.
#[derive(Clone, Debug)]
pub struct FpState {
    pub rounding_mode: RoundingMode,
}

impl FpState {
    /// Creates a new instance of FP state.
    pub fn new() -> Self {
        Self {
            rounding_mode: RoundingMode::TiesTowardZero,
        }
    }
}

impl<'vm, C: Composition, FP> GAExecutor<'vm, C>
// TODO: These must be moved.
where
    C::SMT: SmtSolver<FpExpression = FP>,
    C: Composition<SmtFPExpression = FP>,
    FP: SmtFPExpr<Expression = C::SmtExpression>,
{
    pub fn get_fp_operand_value(&mut self, operand: Operand, destination_ty: OperandType, rm: RoundingMode, logger: &mut C::Logger) -> ResultOrTerminate<FP> {
        match operand.value {
            OperandStorage::Local(id) => {
                //self.state.hooks.read_fp_register(operand,logger.ty, id, , memory)
                match self.context.fp_locals.get(&id) {
                    Some(value) => ResultOrTerminate::Result(Ok(value.clone())),
                    None => ResultOrTerminate::Result(crate::Result::Err(GAError::MemoryError(MemoryError::TriedToReadLocalBeforeAssign(id.clone())).into())),
                }
            }
            OperandStorage::Address(address) => {
                let address = extract!(Ok(self.get_operand_value(&address, logger)));
                let read = match self.state.reader().read_memory(address.clone(), operand.ty.size()) {
                    crate::executor::hooks::ResultOrHook::Hook(hook) => match hook(&mut self.state, address) {
                        Ok(val) => val,
                        Err(e) => return ResultOrTerminate::Result(Err(e)),
                    },
                    ResultOrHook::Hooks(_) => todo!("How do we handle multiple hooks."),
                    ResultOrHook::Result(Ok(val)) => val,
                    ResultOrHook::Result(Err(r)) => return ResultOrTerminate::Result(Err(r).context("While looking up an address for floating point arithmetic")),
                    ResultOrHook::EndFailure(e) => return ResultOrTerminate::Failure(format!("{e} @ {}", self.state.debug_string())),
                };
                let res = read.to_fp(operand.ty, destination_ty, rm, true);
                ResultOrTerminate::Result(res)
            }
            OperandStorage::Register { id, ty } => {
                let hook = self.state.hooks.reader(&mut self.state.memory).read_fp_register(&id, ty, destination_ty, rm, true);

                match hook {
                    ResultOrHook::Hook(hook) => ResultOrTerminate::Result(hook(&mut self.state)),
                    ResultOrHook::EndFailure(e) => ResultOrTerminate::Failure(e),
                    ResultOrHook::Hooks(_) => todo!("Handle multiple hooks"),
                    ResultOrHook::Result(Ok(e)) => ResultOrTerminate::Result(Ok(e)),
                    ResultOrHook::Result(Err(e)) => ResultOrTerminate::Result(Err(e).context("While resolving register value")),
                }
            }
            OperandStorage::Immediate { value, ty } => ResultOrTerminate::Result(self.state.memory.from_f64(value, rm, ty)),
            OperandStorage::CoreRegister { id, ty, signed: signed_outer } => {
                let (size, signed) = if let OperandType::Integral { size, signed } = ty {
                    (size, signed)
                } else {
                    (ty.size(), true)
                };
                if signed != signed_outer {
                    return ResultOrTerminate::Result(Err(crate::InternalError::TypeError).context("While reading a core-register, mismatch in sign bits"));
                }
                let bv_value = extract!(Ok(self.get_operand_value(&general_assembly::operand::Operand::Register(id), logger)), context: "While retrieving a floating point value from a core-register");
                let bv_value = bv_value.resize_unsigned(size);

                ResultOrTerminate::Result(
                    bv_value
                        .to_fp(operand.ty, destination_ty, rm, signed)
                        .context("While retrieving a floating point value from a core-register"),
                )
            }
            OperandStorage::CoreOperand { operand, ty, signed } => {
                let val = extract!(Ok(self.get_operand_value(&operand, logger)));
                let (size, signed) = if let OperandType::Integral { size, signed } = ty {
                    (size, signed)
                } else {
                    (ty.size(), signed)
                };
                let val = val.resize_unsigned(size);
                ResultOrTerminate::Result(
                    val.to_fp(ty, destination_ty, rm, signed)
                        .context("While retrieving a floating point value from a core-operand"),
                )
            }
        }
    }

    fn set_fp_operand_value(&mut self, operand: Operand, value: FP, logger: &mut C::Logger, rm: RoundingMode) -> ResultOrTerminate<()> {
        match operand.value {
            OperandStorage::Local(id) => {
                //self.state.hooks.read_fp_register(operand,logger.ty, id, , memory)
                self.context.fp_locals.insert(id, value);
                ResultOrTerminate::Result(Ok(()))
            }
            OperandStorage::Address(address) => {
                let value = match value.to_bv(rm, true) {
                    Ok(val) => val,
                    Err(e) => return ResultOrTerminate::Result(Err(e).context("Tried to resolve as a bitvector")),
                };
                let address = extract!(Ok(self.get_operand_value(&address, logger)));
                match self.state.hooks.writer(&mut self.state.memory).write_memory(address.clone(), value.clone()) {
                    ResultOrHook::Hook(hook) => ResultOrTerminate::Result(hook(&mut self.state, address, value).context("While writing a floating point value to an address")),
                    ResultOrHook::Hooks(_) => todo!(),
                    ResultOrHook::EndFailure(e) => ResultOrTerminate::Failure(format!("{e} @ {}", self.state.debug_string())),
                    ResultOrHook::Result(Ok(v)) => ResultOrTerminate::Result(Ok(v)),
                    ResultOrHook::Result(Err(e)) => {
                        ResultOrTerminate::Result(Err(e).context(format!("While writing a floating point value to an address @ {}", self.state.debug_string())))
                    }
                }
            }
            OperandStorage::Register { id, ty } => {
                if ty != value.ty() {
                    return ResultOrTerminate::Result(
                        Err(crate::GAError::InternalError(InternalError::TypeError)).context(format!("While writing {ty:?} to {:?} register", value.ty())),
                    );
                }
                let hook = self.state.hooks.writer(&mut self.state.memory).write_fp_register(&id, &value, rm, true);

                match hook {
                    ResultOrHook::Hook(hook) => ResultOrTerminate::Result(hook(&mut self.state, value)),
                    ResultOrHook::EndFailure(e) => ResultOrTerminate::Failure(e),
                    ResultOrHook::Hooks(_) => todo!("Handle multiple hooks"),
                    ResultOrHook::Result(Ok(e)) => ResultOrTerminate::Result(Ok(e)),
                    ResultOrHook::Result(Err(e)) => ResultOrTerminate::Result(Err(e).context("While resolving register value")),
                }
            }
            // NOTE: This is now explicitly prohibited as this does not affect the program memory,
            // it only affects an intermediate value. A write to program memory however, is not
            // explicitly prohibited.
            OperandStorage::Immediate { value: _, ty: _ } => ResultOrTerminate::Result(Err(crate::MemoryError::TriedToAssignToImmediateField).context("FP store")),
            OperandStorage::CoreRegister { id, ty: _, signed } => {
                let value = match value.to_bv(rm, signed) {
                    Ok(val) => val,
                    Err(e) => return ResultOrTerminate::Result(Err(e).context("While writing a fp value to a core-register")),
                };
                self.set_operand_value(&general_assembly::operand::Operand::Register(id), value, logger)
            }
            OperandStorage::CoreOperand { operand, ty: _, signed } => {
                let value = match value.to_bv(rm, signed) {
                    Ok(val) => val,
                    Err(e) => return ResultOrTerminate::Result(Err(e).context("While writing a fp value to a core-operand")),
                };
                self.set_operand_value(&operand, value, logger)
            }
        }
    }

    fn rm(&self, rm: Option<RoundingMode>) -> RoundingMode {
        rm.unwrap_or(self.state.fp_state.rounding_mode.clone())
    }

    // TODO: Look in to reducing the clones here.
    pub fn execute_ieee754(&mut self, op: Operations, logger: &mut C::Logger) -> ResultOrTerminate<()> {
        match op {
            Operations::RoundToInt { source, destination, rounding } => {
                let value = extract!(Ok(self.get_fp_operand_value(source.clone(), source.ty.clone(), self.rm(None), logger)));
                crate::debug!("RoundToInt operand value {:?}", value);
                let value = match value.round_to_integral(self.rm(rounding.clone())) {
                    Ok(val) => val,
                    Err(e) => return ResultOrTerminate::Result(Err(e)),
                };
                crate::debug!("RoundToInt rounded value {:?}", value);

                self.set_fp_operand_value(destination, value, logger, self.rm(rounding))
            }
            Operations::NextUp { source: _, destination: _ } => todo!("Is this needed?"),
            Operations::NextDown { source: _, destination: _ } => todo!("Is this needed?"),
            Operations::Remainder {
                nominator,
                denominator,
                destination,
            } => {
                let nominator = extract!(Ok(self.get_fp_operand_value(nominator.clone(), nominator.ty.clone(), self.rm(None), logger)));
                let denominator = extract!(Ok(self.get_fp_operand_value(denominator.clone(), denominator.ty.clone(), self.rm(None), logger)));
                let res = match nominator.remainder(&denominator, self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res)),
                };

                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::Addition { lhs, rhs, destination } => {
                let lhs = extract!(Ok(self.get_fp_operand_value(lhs.clone(), lhs.ty.clone(), self.rm(None), logger)));
                let rhs = extract!(Ok(self.get_fp_operand_value(rhs.clone(), rhs.ty.clone(), self.rm(None), logger)));
                let res = match lhs.add(&rhs, self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res)),
                };

                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::Subtraction { lhs, rhs, destination } => {
                let lhs = extract!(Ok(self.get_fp_operand_value(lhs.clone(), lhs.ty.clone(), self.rm(None), logger)));
                let rhs = extract!(Ok(self.get_fp_operand_value(rhs.clone(), rhs.ty.clone(), self.rm(None), logger)));
                let res = match lhs.sub(&rhs, self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res)),
                };

                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::Multiplication { lhs, rhs, destination } => {
                let lhs = extract!(Ok(self.get_fp_operand_value(lhs.clone(), lhs.ty.clone(), self.rm(None), logger)));
                let rhs = extract!(Ok(self.get_fp_operand_value(rhs.clone(), rhs.ty.clone(), self.rm(None), logger)));
                let res = match lhs.mul(&rhs, self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res)),
                };

                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::Division {
                nominator,
                denominator,
                destination,
            } => {
                let nominator = extract!(Ok(self.get_fp_operand_value(nominator.clone(), nominator.ty.clone(), self.rm(None), logger)));
                let denominator = extract!(Ok(self.get_fp_operand_value(denominator.clone(), denominator.ty.clone(), self.rm(None), logger)));
                let res = match nominator.div(&denominator, self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res).context("Floating point division")),
                };

                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::Sqrt { operand, destination } => {
                let operand = extract!(Ok(self.get_fp_operand_value(operand.clone(),operand.ty.clone(),self.rm(None),logger)), context: "FP sqrt");
                let res = match operand.sqrt(self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res).context("Floating point sqrt")),
                };
                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::FusedMultiplication { lhs, rhs, add, destination } => {
                let lhs = extract!(Ok(self.get_fp_operand_value(lhs.clone(),lhs.ty.clone(),self.rm(None),logger)), context: "FP fused multiply and accumulate, lhs");
                let rhs = extract!(Ok(self.get_fp_operand_value(rhs.clone(),rhs.ty.clone(),self.rm(None),logger)), context: "FP fused multiply and accumulate, rhs");
                let add = extract!(Ok(self.get_fp_operand_value(add.clone(),add.ty.clone(),self.rm(None),logger)), context: "FP fused multiply and accumulate, add");
                let res = match lhs.fused_multiply(&rhs, &add, self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res).context("Floating point fused multiply and accumulate")),
                };
                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::ConvertFromInt { operand, destination } => {
                let operand = extract!(Ok(self.get_fp_operand_value(operand.clone(),destination.ty.clone(),self.rm(None),logger)), context: "Convert from int, operand");
                self.set_fp_operand_value(destination, operand, logger, self.rm(None))
            }
            Operations::Copy { source, destination } => {
                let value = extract!(Ok(self.get_fp_operand_value(source.clone(),source.ty.clone(),self.rm(None),logger)), context: "FP copy");
                self.set_fp_operand_value(destination, value, logger, self.rm(None))
            }
            Operations::Negate { source, destination } => {
                let operand = extract!(Ok(self.get_fp_operand_value(source.clone(),source.ty.clone(),self.rm(None),logger)), context: "FP neg");
                let res = match operand.neg(self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res).context("Floating point negate")),
                };
                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::Abs { operand, destination } => {
                let operand = extract!(Ok(self.get_fp_operand_value(operand.clone(),operand.ty.clone(),self.rm(None),logger)), context: "FP abs");
                let res = match operand.abs(self.rm(None)) {
                    Ok(value) => value,
                    Err(res) => return ResultOrTerminate::Result(Err(res).context("Floating point absolute value")),
                };
                self.set_fp_operand_value(destination, res, logger, self.rm(None))
            }
            Operations::CopySign {
                source: _,
                sign_source: _,
                destination: _,
            } => todo!(),
            Operations::Compare {
                lhs,
                rhs,
                operation,
                destination,
                signal,
            } => {
                if signal {
                    todo!("Determine what signal should represent")
                }
                let lhs = extract!(Ok(self.get_fp_operand_value(lhs.clone(),lhs.ty.clone(),self.rm(None),logger)), context: "FP compare, lhs");
                let rhs = extract!(Ok(self.get_fp_operand_value(rhs.clone(),rhs.ty.clone(),self.rm(None),logger)), context: "FP compare, rhs");
                let res = match lhs.compare(&rhs, operation, self.rm(None)) {
                    Ok(val) => val,
                    Err(e) => return ResultOrTerminate::Result(Err(e).context("Floating point compare")),
                };
                self.set_operand_value(&destination, res, logger)
            }
            Operations::NonComputational { operand, operation, destination } => {
                let operand = extract!(Ok(self.get_fp_operand_value(operand.clone(),operand.ty.clone(),self.rm(None),logger)),context: "FP non computational");
                let res = match operand.check_meta(operation, self.rm(None)) {
                    Ok(val) => val,
                    Err(e) => return ResultOrTerminate::Result(Err(e).context("Floating point non computational")),
                };

                self.set_operand_value(&destination, res, logger)
            }
            Operations::TotalOrder { lhs: _, rhs: _, abs: _ } => todo!(),
            Operations::Convert { source, destination, rounding } => {
                let source_val = extract!(Ok(self.get_fp_operand_value(source, destination.ty.clone(), self.rm(rounding.clone()), logger)));
                self.set_fp_operand_value(destination, source_val, logger, self.rm(rounding))
            }
        }
    }
}

impl std::fmt::Display for FpState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { rounding_mode } = self;
        write!(f, "Rounding mode : {rounding_mode}\r\n")?;

        write!(f, "\r\n")
    }
}
