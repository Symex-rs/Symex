use std::fmt::{Debug, Display};

use boolector::SolverResult;
use general_assembly::{prelude::DataWord, shift::Shift};

use crate::{memory::MemoryError as MemoryFileError, Endianness, GAError};

pub mod bitwuzla;
//pub mod deterministic;
pub mod smt_boolector;

pub type DExpr = smt_boolector::BoolectorExpr;
pub type DSolver = smt_boolector::BoolectorIncrementalSolver;
pub type DContext = smt_boolector::BoolectorSolverContext;
pub type DArray = smt_boolector::BoolectorArray;

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum SolverError {
    /// The set of constraints added to the solution are unsatisfiable.
    #[error("Unsat")]
    Unsat,

    /// Unknown error passed along from the SMT solver used.
    #[error("Unknown")]
    Unknown,

    /// Exceeded the passed maximum number of solutions.
    #[error("Exceeded number of solutions")]
    TooManySolutions,
}

#[derive(Debug)]
pub enum Solutions<E> {
    Exactly(Vec<E>),
    AtLeast(Vec<E>),
}

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum MemoryError {
    #[error("Memory file encountered error")]
    MemoryFileError(MemoryFileError),

    #[error("Program counter is non deterministic.")]
    PcNonDetmerinistic,
}

pub trait ProgramMemory: Debug + Clone {
    #[must_use]
    /// Writes a data-word to program memory.
    fn set(&self, address: u64, dataword: DataWord) -> Result<(), MemoryError>;

    #[must_use]
    /// Gets a data-word from program memory.
    fn get(&self, address: u64, bits: u32) -> Result<DataWord, MemoryError>;

    #[must_use]
    /// Gets a word from program memory without converting it to a rust
    /// number.
    fn get_raw_word(&self, address: u64) -> Result<&[u8], MemoryError>;

    #[must_use]
    /// Returns true if the address is contained in the program memory.
    fn address_in_range(&self, address: u64) -> bool;

    #[must_use]
    /// Returns the endianness used in the program memory.
    ///
    /// This is assumed to reflect the underlying architecture endianness.
    fn get_endianness(&self) -> Endianness;

    #[must_use]
    /// Returns the address of a specific symbol if it exists.
    fn get_symbol_address(&self, symbol: &str) -> Option<u64>;

    #[must_use]
    /// Returns the pointer size of the system.
    fn get_ptr_size(&self) -> usize;

    #[must_use]
    /// Returns the word size of the system.
    fn get_word_size(&self) -> usize {
        self.get_ptr_size()
    }

    #[must_use]
    fn get_entry_point_names(&self) -> Vec<String>;
}
pub trait SmtMap: Debug + Clone + Display {
    type Expression: SmtExpr;
    type SMT: SmtSolver<Expression = Self::Expression>;
    type ProgramMemory: ProgramMemory;

    #[must_use]
    fn new(smt: Self::SMT, project: Self::ProgramMemory, word_size: usize, endianness: Endianness, initial_sp: Self::Expression) -> Result<Self, GAError>;

    #[must_use]
    fn get(&self, idx: &Self::Expression, size: usize) -> Result<Self::Expression, MemoryError>;

    #[must_use]
    fn get_word(&self, idx: &Self::Expression) -> Result<Self::Expression, MemoryError> {
        self.get(idx, self.get_word_size() as usize)
    }
    #[must_use]
    fn set(&mut self, idx: &Self::Expression, value: Self::Expression) -> Result<(), MemoryError>;

    #[must_use]
    fn get_flag(&mut self, idx: &str) -> Result<Self::Expression, MemoryError>;

    #[must_use]
    fn set_flag(&mut self, idx: &str, value: Self::Expression) -> Result<(), MemoryError>;

    #[must_use]
    fn get_register(&mut self, idx: &str) -> Result<Self::Expression, MemoryError>;

    #[must_use]
    fn set_register(&mut self, idx: &str, value: Self::Expression) -> Result<(), MemoryError>;

    // NOTE: Might be a poor assumption that the word size for PC is 32 bit.
    #[must_use]
    fn get_pc(&self) -> Result<Self::Expression, MemoryError>;

    #[must_use]
    fn set_pc(&mut self, value: u32) -> Result<(), MemoryError>;

    #[must_use]
    fn from_u64(&self, value: u64, size: usize) -> Self::Expression;

    #[must_use]
    fn from_bool(&self, value: bool) -> Self::Expression;

    #[must_use]
    fn unconstrained(&mut self, name: &str, size: usize) -> Self::Expression;

    #[must_use]
    fn unconstrained_unnamed(&mut self, size: usize) -> Self::Expression;

    #[must_use]
    /// Returns the pointer size of the system.
    fn get_ptr_size(&self) -> usize;

    #[must_use]
    /// Returns the lowest stack pointer (_stack_start) and the latest stack
    /// pointer write.
    fn get_stack(&mut self) -> (Self::Expression, Self::Expression);

    #[must_use]
    /// Returns the word size of the system.
    fn get_word_size(&self) -> usize {
        self.get_ptr_size()
    }

    #[must_use]
    fn get_from_instruction_memory(&self, address: u64) -> crate::Result<&[u8]>;
}

/// Defines a type that can be used as an SMT solver.
pub trait SmtSolver: Debug + Clone {
    type Expression: SmtExpr;
    type Memory: SmtMap<SMT = Self, Expression = Self::Expression>;

    #[must_use]
    fn new() -> Self;

    #[must_use]
    /// Creates a new unconstrained value of size `size` with the label `name`.
    fn unconstrained(&self, size: u32, name: &str) -> Self::Expression;

    #[must_use]
    /// Create a new expression set equal to `1` of size `bits`.
    fn one(&self, bits: u32) -> Self::Expression;

    #[must_use]
    /// Create a new expression set to zero of size `size`.
    fn zero(&self, size: u32) -> Self::Expression;

    #[must_use]
    /// Create a new expression from a boolean value.
    fn from_bool(&self, value: bool) -> Self::Expression;

    #[must_use]
    /// Create a new expression from an `u64` value of size `size`.
    fn from_u64(&self, value: u64, size: u32) -> Self::Expression;

    #[must_use]
    /// Create an expression of size `bits` from a binary string.
    fn from_binary_string(&self, bits: &str) -> Self::Expression;

    #[must_use]
    /// Creates an expression of size `size` containing the maximum unsigned
    /// value.
    fn unsigned_max(&self, size: u32) -> Self::Expression;

    #[must_use]
    /// Create an expression of size `size` containing the maximum signed value.
    fn signed_max(&self, size: u32) -> Self::Expression;

    #[must_use]
    /// Create an expression of size `bits` containing the minimum signed value.
    fn signed_min(&self, size: u32) -> Self::Expression;

    #[allow(clippy::unused_self)]
    fn check_sat_result(&self, sat_result: SolverResult) -> Result<bool, SolverError> {
        match sat_result {
            SolverResult::Sat => Ok(true),
            SolverResult::Unsat => Ok(false),
            SolverResult::Unknown => Err(SolverError::Unknown),
        }
    }

    fn get_value(&self, expr: &Self::Expression) -> Result<Self::Expression, SolverError>;

    /// Pushes a constraint to the queue.
    fn push(&self);

    /// Removes the latest requirement from the queue.
    fn pop(&self);

    /// Solve for the current solver state, and returns if the result is
    /// satisfiable.
    ///
    /// All asserts and assumes are implicitly combined with a boolean and.
    /// Returns true or false, and [`SolverError::Unknown`] if the result
    /// cannot be determined.
    fn is_sat(&self) -> Result<bool, SolverError>;

    /// Solve for the solver state with the assumption of the passed constraint.
    fn is_sat_with_constraint(&self, constraint: &Self::Expression) -> Result<bool, SolverError>;

    /// Solve for the solver state with the assumption of the passed
    /// constraints.
    fn is_sat_with_constraints(&self, constraints: &[Self::Expression]) -> Result<bool, SolverError>;

    #[allow(clippy::unused_self)]
    /// Add the constraint to the solver.
    ///
    /// The passed constraint will be implicitly combined with the current state
    /// in a boolean `and`. Asserted constraints cannot be removed.
    fn assert(&self, constraint: &Self::Expression);

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to `upper_bound`, the returned
    /// [`Solutions`] has variants for if the number of solution exceeds the
    /// upper bound.
    fn get_values(&self, expr: &Self::Expression, upper_bound: usize) -> Result<Solutions<Self::Expression>, SolverError>;

    /// Returns `true` if `lhs` and `rhs` must be equal under the current
    /// constraints.
    fn must_be_equal(&self, lhs: &Self::Expression, rhs: &Self::Expression) -> Result<bool, SolverError>;

    /// Check if `lhs` and `rhs` can be equal under the current constraints.
    fn can_equal(&self, lhs: &Self::Expression, rhs: &Self::Expression) -> Result<bool, SolverError>;

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to a maximum of `upper_bound`. If more
    /// solutions are available the error [`SolverError::TooManySolutions`]
    /// is returned.
    fn get_solutions(&self, expr: &Self::Expression, upper_bound: usize) -> Result<Solutions<Self::Expression>, SolverError>;
}

pub trait SmtExpr: Debug + Clone {
    /// Returns the bit width of the [Expression].
    fn len(&self) -> u32;

    /// Zero-extend the current [Expression] to the passed bit width and return
    /// the resulting [Expression].
    fn zero_ext(&self, width: u32) -> Self;

    /// Sign-extend the current [Expression] to the passed bit width and return
    /// the resulting [Expression].
    fn sign_ext(&self, width: u32) -> Self;

    fn resize_unsigned(&self, width: u32) -> Self;

    /// [Expression] equality check. Both [Expression]s must have the same bit
    /// width, the result is returned as an [Expression] of width `1`.
    fn eq(&self, other: &Self) -> Self;

    /// [Expression] inequality check. Both [Expression]s must have the same bit
    /// width, the result is returned as an [Expression] of width `1`.
    fn ne(&self, other: &Self) -> Self;

    /// [Expression] unsigned greater than. Both [Expression]s must have the
    /// same bit width, the result is returned as an [Expression] of width
    /// `1`.
    fn ugt(&self, other: &Self) -> Self;

    /// [Expression] unsigned greater than or equal. Both [Expression]s must
    /// have the same bit width, the result is returned as an [Expression]
    /// of width `1`.
    fn ugte(&self, other: &Self) -> Self;

    /// [Expression] unsigned less than. Both [Expression]s must have the same
    /// bit width, the result is returned as an [Expression] of width `1`.
    fn ult(&self, other: &Self) -> Self;

    /// [Expression] unsigned less than or equal. Both [Expression]s must have
    /// the same bit width, the result is returned as an [Expression] of
    /// width `1`.
    fn ulte(&self, other: &Self) -> Self;

    /// [Expression] signed greater than. Both [Expression]s must have the same
    /// bit width, the result is returned as an [Expression] of width `1`.
    fn sgt(&self, other: &Self) -> Self;

    /// [Expression] signed greater or equal than. Both [Expression]s must have
    /// the same bit width, the result is returned as an [Expression] of
    /// width `1`.
    fn sgte(&self, other: &Self) -> Self;

    /// [Expression] signed less than. Both [Expression]s must have the same bit
    /// width, the result is returned as an [Expression] of width `1`.
    fn slt(&self, other: &Self) -> Self;

    /// [Expression] signed less than or equal. Both [Expression]s must have the
    /// same bit width, the result is returned as an [Expression] of width
    /// `1`.
    fn slte(&self, other: &Self) -> Self;

    fn add(&self, other: &Self) -> Self;

    fn sub(&self, other: &Self) -> Self;

    fn mul(&self, other: &Self) -> Self;

    fn udiv(&self, other: &Self) -> Self;

    fn sdiv(&self, other: &Self) -> Self;

    fn urem(&self, other: &Self) -> Self;

    fn srem(&self, other: &Self) -> Self;

    fn not(&self) -> Self;

    fn and(&self, other: &Self) -> Self;

    fn or(&self, other: &Self) -> Self;

    fn xor(&self, other: &Self) -> Self;

    fn shift(&self, steps: &Self, direction: Shift) -> Self;

    fn ite(&self, then_bv: &Self, else_bv: &Self) -> Self;

    fn concat(&self, other: &Self) -> Self;

    fn slice(&self, low: u32, high: u32) -> Self;

    fn uaddo(&self, other: &Self) -> Self;

    fn saddo(&self, other: &Self) -> Self;

    fn usubo(&self, other: &Self) -> Self;

    fn ssubo(&self, other: &Self) -> Self;

    fn umulo(&self, other: &Self) -> Self;

    fn smulo(&self, other: &Self) -> Self;

    fn simplify(self) -> Self;

    fn get_constant(&self) -> Option<u64>;

    fn get_identifier(&self) -> Option<String>;

    fn get_constant_bool(&self) -> Option<bool>;

    fn to_binary_string(&self) -> String;

    fn replace_part(&self, start_idx: u32, replace_with: Self) -> Self;

    /// Saturated unsigned addition. Adds `self` with `other` and if the result
    /// overflows the maximum value is returned.
    ///
    /// Requires that `self` and `other` have the same width.
    fn uadds(&self, other: &Self) -> Self;

    /// Saturated signed addition. Adds `self` with `other` and if the result
    /// overflows either the maximum or minimum value is returned, depending
    /// on the sign bit of `self`.
    ///
    /// Requires that `self` and `other` have the same width.
    fn sadds(&self, other: &Self) -> Self;

    /// Saturated unsigned subtraction.
    ///
    /// Subtracts `self` with `other` and if the result overflows it is clamped
    /// to zero, since the values are unsigned it can never go below the
    /// minimum value.
    fn usubs(&self, other: &Self) -> Self;

    /// Saturated signed subtraction.
    ///
    /// Subtracts `self` with `other` with the result clamped between the
    /// largest and smallest value allowed by the bit-width.
    fn ssubs(&self, other: &Self) -> Self;
    /// Pushes a constraint to the queue.
    fn push(&self);

    /// Removes the latest requirement from the queue.
    fn pop(&self);
}
