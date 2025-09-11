use std::fmt::{Debug, Display};

use general_assembly::{
    extension::ieee754::{OperandType, RoundingMode},
    shift::Shift,
};
use hashbrown::HashMap;

use crate::{
    arch::{ArchitectureOverride, SupportedArchitecture},
    executor::ResultOrTerminate,
    memory::MemoryError as MemoryFileError,
    project::dwarf_helper::SubProgramMap,
    Endianness,
    UserStateContainer,
};

#[cfg(feature = "bitwuzla")]
pub mod bitwuzla;
#[cfg(feature = "z3")]
pub mod z3;
//pub mod deterministic;
#[cfg(feature = "boolector")]
pub mod smt_boolector;

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

    #[error("Typically denotes logic errors in the glue layer. {0}")]
    /// A generic error that occurs when the glue layer fails.
    Generic(String),
}

#[derive(Debug)]
pub enum Solutions<E> {
    Exactly(Vec<E>),
    AtLeast(Vec<E>),
}

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum MemoryError {
    #[error("Memory file encountered error {0}")]
    MemoryFileError(MemoryFileError),

    #[error("Program counter is non deterministic.")]
    PcNonDetmerinistic,
}

pub trait ProgramMemory: Debug + Clone {
    /// Writes a data-word to program memory.
    fn set<Expr: SmtExpr, Ctx: Context<Expr = Expr>>(
        &self,
        address: u64,
        dataword: Expr,
        writes: &mut HashMap<u64, Expr>,
        ctx: &mut Ctx,
    ) -> std::result::Result<(), crate::smt::MemoryError>;

    /// Gets a data-word from program memory.
    fn get<Expr: SmtExpr, Ctx: Context<Expr = Expr>>(&self, address: u64, bits: u32, writes: &HashMap<u64, Expr>, ctx: &Ctx) -> std::result::Result<Expr, crate::smt::MemoryError>;

    /// Gets a word from program memory without converting it to a rust
    /// number.
    fn get_raw_word(&self, address: u64) -> Result<Vec<u8>, MemoryError>;

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
    fn get_ptr_size(&self) -> u32;

    #[must_use]
    /// Returns the word size of the system.
    fn get_word_size(&self) -> u32 {
        self.get_ptr_size()
    }

    #[must_use]
    /// Returns the availiable sub programs.
    fn borrow_symtab(&self) -> &SubProgramMap;

    #[must_use]
    fn get_entry_point_names(&self) -> Vec<String>;

    /// Determines if the address is in range of the program memory.
    fn out_of_bounds<Map: SmtMap>(&self, addr: &Map::Expression, memory: &Map) -> Map::Expression;

    fn out_of_bounds_const(&self, addr: u64) -> bool;

    fn regions(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        Vec::new().into_iter()
    }
}
pub trait SmtMap: Debug + Clone + Display {
    type Expression: SmtExpr<FPExpression = <Self::SMT as SmtSolver>::FpExpression>;
    type SMT: SmtSolver<Expression = Self::Expression>;
    type ProgramMemory: ProgramMemory;
    type StateContainer: UserStateContainer;

    fn new<O: ArchitectureOverride>(
        smt: Self::SMT,
        program_memory: Self::ProgramMemory,
        endianness: Endianness,
        initial_sp: Self::Expression,
        _state: &Self::StateContainer,
        arch: &SupportedArchitecture<O>,
    ) -> Result<Self, crate::GAError>;

    fn get(&mut self, idx: &Self::Expression, size: u32) -> ResultOrTerminate<Self::Expression>;

    fn get_from_const_address(&mut self, idx: u64, size: u32) -> ResultOrTerminate<Self::Expression> {
        self.get(&self.from_u64(idx, self.get_ptr_size()), size)
    }

    fn get_word(&mut self, idx: &Self::Expression) -> ResultOrTerminate<Self::Expression> {
        self.get(idx, self.get_word_size())
    }

    /// Writes a symbolic value to the given address.
    fn set(&mut self, idx: &Self::Expression, value: Self::Expression) -> Result<(), MemoryError>;

    /// Bypasses all of the checks that the memory abstraction might make.
    fn set_raw(&mut self, idx: &Self::Expression, value: Self::Expression) -> Result<(), MemoryError> {
        self.set(idx, value)
    }

    /// Writes to a constant address.
    fn set_to_const_address(&mut self, idx: u64, value: Self::Expression) -> Result<(), MemoryError> {
        self.set(&self.from_u64(idx, self.get_ptr_size()), value)
    }

    /// Retrieves a particular flag from memory.
    ///
    /// If the target flag does not exist the memory map is expected to
    /// introduce a new symbolic value for this register.
    fn get_flag(&mut self, idx: &str) -> Result<Self::Expression, MemoryError>;

    /// Sets the value of the given flag.
    fn set_flag(&mut self, idx: &str, value: Self::Expression) -> Result<(), MemoryError>;

    /// Gets the given register.from memory.
    ///
    /// If the target register does not exist the memory map is expected to
    /// introduce a new symbolic value for this register.
    fn get_register(&mut self, idx: &str) -> Result<Self::Expression, MemoryError>;

    fn get_registers(&mut self) -> HashMap<String, Self::Expression>;

    fn set_register(&mut self, idx: &str, value: Self::Expression) -> Result<(), MemoryError>;

    fn set_fp_register(&mut self, idx: &str, value: <Self::SMT as SmtSolver>::FpExpression, rm: RoundingMode, signed: bool) -> Result<(), MemoryError> {
        self.set_register(idx, value.to_bv(rm, signed).expect("Float conversion to be valid"))
    }

    fn get_fp_register(
        &mut self,
        idx: &str,
        source_ty: OperandType,
        dest_ty: OperandType,
        rm: RoundingMode,
        signed: bool,
    ) -> Result<<Self::SMT as SmtSolver>::FpExpression, MemoryError> {
        let reg = self.get_register(idx)?;
        Ok(reg.to_fp(source_ty, dest_ty, rm, signed).expect("Floatingpoint conversion to be valid"))
    }

    // NOTE: Might be a poor assumption that the word size for PC is 32 bit.
    fn get_pc(&self) -> Result<Self::Expression, MemoryError>;

    fn set_pc(&mut self, value: u32) -> Result<(), MemoryError>;

    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    fn from_u64(&self, value: u64, size: u32) -> Self::Expression;

    #[allow(clippy::wrong_self_convention)]
    /// Create a new expression from an `u64` value of size `size`.
    fn from_f64(&mut self, _value: f64, rm: RoundingMode, ty: OperandType) -> crate::Result<<Self::SMT as SmtSolver>::FpExpression> {
        let size = match ty {
            OperandType::Binary16 => 16,
            OperandType::Binary32 => 32,
            OperandType::Binary64 => 64,
            OperandType::Binary128 => 128,
            OperandType::Integral { size, signed: _ } => size,
        };
        let ret: Self::Expression = self.unconstrained_unnamed(size);
        ret.to_fp(OperandType::Integral { size, signed: true }, ty, rm, true)
    }

    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    fn from_bool(&self, value: bool) -> Self::Expression;

    #[must_use]
    fn unconstrained(&mut self, name: &str, size: u32) -> Self::Expression;

    #[must_use]
    fn unconstrained_unnamed(&mut self, size: u32) -> Self::Expression;

    #[must_use]
    /// Creates a new unconstrained value of size `size` with the label `name`.
    fn unconstrained_fp(&mut self, ty: OperandType, name: &str) -> <Self::SMT as SmtSolver>::FpExpression;

    #[must_use]
    /// Creates a new unconstrained value of size `size` with the label `name`.
    fn unconstrained_fp_unnamed(&mut self, ty: OperandType) -> <Self::SMT as SmtSolver>::FpExpression;

    #[must_use]
    /// Returns the pointer size of the system.
    fn get_ptr_size(&self) -> u32;

    #[must_use]
    /// Returns the lowest stack pointer (`\_stack\_start`) and the latest stack
    /// pointer write.
    fn get_stack(&mut self) -> (Self::Expression, Self::Expression);

    #[must_use]
    /// Returns the word size of the system.
    fn get_word_size(&self) -> u32 {
        self.get_ptr_size()
    }

    fn get_from_instruction_memory(&self, address: u64) -> crate::Result<Vec<u8>>;

    /// Clears all named variables.
    ///
    /// This does not remove them from the SMT solver, it merely resets the
    /// logging output.
    fn clear_named_variables(&mut self);

    /// Returns the underlying program memory.
    fn program_memory(&self) -> &Self::ProgramMemory;

    /// Dispatches the internal temporal hooks.
    fn dispatch_temporal_hooks(&mut self) {}

    #[must_use]
    fn is_sat(&self) -> bool;

    fn with_model_gen<R, F: FnOnce() -> R>(&self, f: F) -> R;

    /// Gets the currecnt cycle count
    fn get_cycle_count(&mut self) -> u64;

    /// Sets the cycle count of the device.
    fn set_cycle_count(&mut self, value: u64);

    /// Increments the cyclec count of the device
    fn increment_cycle_count(&mut self, value: u64) {
        let value = self.get_cycle_count() + value;
        self.set_cycle_count(value);
    }

    /// Determines if the address is in range of the program memory.
    fn out_of_bounds(&self, addr: &Self::Expression) -> Self::Expression {
        self.program_memory().out_of_bounds(addr, self)
    }

    fn out_of_bounds_const(&self, addr: u64) -> bool {
        self.program_memory().out_of_bounds_const(addr)
    }

    fn regions(&self) -> impl Iterator<Item = (u64, u64)> {
        Vec::new().into_iter()
    }
}

/// Defines a type that can be used as an SMT solver.
pub trait SmtSolver: Debug + Clone {
    type Expression: SmtExpr<FPExpression = Self::FpExpression>;
    type FpExpression: SmtFPExpr<Expression = Self::Expression>;

    #[must_use]
    fn new() -> Self;

    #[must_use]
    /// Creates a new unconstrained value of size `size` with the label `name`.
    fn unconstrained(&self, size: u32, name: &str) -> Self::Expression;

    #[must_use]
    /// Creates a new unconstrained value of size `size` with the label `name`.
    fn unconstrained_fp(&self, ty: OperandType, name: &str) -> Self::FpExpression;

    #[must_use]
    /// Creates a new unconstrained value of size `size` with the label `name`.
    fn unconstrained_fp_unnamed(&self, ty: OperandType) -> Self::FpExpression;

    #[must_use]
    /// Create a new expression set equal to `1` of size `bits`.
    fn one(&self, bits: u32) -> Self::Expression;

    #[must_use]
    /// Create a new expression set to zero of size `size`.
    fn zero(&self, size: u32) -> Self::Expression;

    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    /// Create a new expression from a boolean value.
    fn from_bool(&self, value: bool) -> Self::Expression;

    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    /// Create a new expression from an `u64` value of size `size`.
    fn from_u64(&self, value: u64, size: u32) -> Self::Expression;

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
    fn get_values(&self, expr: &Self::Expression, upper_bound: u32) -> Result<Solutions<Self::Expression>, SolverError>;

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to a maximum of `upper_bound`. If more
    /// solutions are available the error [`SolverError::TooManySolutions`]
    /// is returned.
    fn get_solutions(&self, expr: &Self::Expression, upper_bound: u32) -> Result<Solutions<Self::Expression>, SolverError>;
}

impl<E> SmtFPExpr for (E, OperandType)
where
    E: SmtExpr<FPExpression = Self>,
{
    type Expression = E;

    fn any(&self, ty: OperandType) -> crate::Result<Self> {
        let size = ty.size();

        Ok((self.0.any(size), ty))
    }

    fn ty(&self) -> OperandType {
        self.1.clone()
    }

    fn convert_from_bv(bv: Self::Expression, _rm: RoundingMode, _source_ty: OperandType, dest_ty: OperandType, _signed: bool) -> crate::Result<Self> {
        let size = dest_ty.size();
        Ok((bv.any(size), dest_ty))
    }

    fn compare(&self, _other: &Self, _cmp: general_assembly::extension::ieee754::ComparisonMode, _rm: RoundingMode) -> crate::Result<Self::Expression> {
        crate::Result::Ok(self.0.any(1))
    }

    fn check_meta(&self, _op: general_assembly::extension::ieee754::NonComputational, _rm: RoundingMode) -> crate::Result<Self::Expression> {
        crate::Result::Ok(self.0.any(1))
    }

    fn get_const(&self) -> Option<f64> {
        None
    }
}

#[allow(unused_variables)]
pub trait SmtFPExpr: Debug + Clone {
    type Expression: SmtExpr<FPExpression = Self>;

    fn any(&self, ty: OperandType) -> crate::Result<Self>;
    fn get_const(&self) -> Option<f64>;
    fn ty(&self) -> OperandType;

    /// Converts from a bv.
    ///
    /// ty represents the target type of the conversion.
    fn convert_from_bv(bv: Self::Expression, rm: RoundingMode, source_ty: OperandType, dest_ty: OperandType, signed: bool) -> crate::Result<Self>;

    fn round_to_integral(&self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn add(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn sub(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn div(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn remainder(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn mul(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn fused_multiply(&self, mul: &Self, add: &Self, rm: RoundingMode) -> crate::Result<Self> {
        self.mul(mul, rm.clone())?.add(add, rm)
    }

    fn neg(&self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn abs(&self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    fn sqrt(&self, rm: RoundingMode) -> crate::Result<Self> {
        self.any(self.ty())
    }

    /// Converts to a bitvector representation of a ieee754 value to a bitvector
    /// without rounding.
    ///
    /// This can be seen as a pure pointer cast.
    fn to_bv(&self, rm: RoundingMode, signed: bool) -> crate::Result<Self::Expression> {
        Self::Expression::from_fp(self, rm, signed)
    }

    fn compare(&self, other: &Self, cmp: general_assembly::extension::ieee754::ComparisonMode, rm: RoundingMode) -> crate::Result<Self::Expression>;

    /// Checks whether or not a non computational ieee query on the floating
    /// point value evaluates to true.
    fn check_meta(&self, op: general_assembly::extension::ieee754::NonComputational, rm: RoundingMode) -> crate::Result<Self::Expression>;
}

#[allow(dead_code)]
pub trait SmtExpr: Debug + Clone {
    type FPExpression: SmtFPExpr<Expression = Self>;
    /// Returns the bit width of the [`SmtExpr`].
    fn size(&self) -> u32;

    #[must_use]
    fn any(&self, width: u32) -> Self;

    /// Converts a bitvector to a floating point representation.
    fn to_fp(&self, source_ty: OperandType, ty: OperandType, rm: RoundingMode, signed: bool) -> crate::Result<Self::FPExpression> {
        Self::FPExpression::convert_from_bv(self.clone(), rm, source_ty, ty, signed)
    }

    #[allow(clippy::wrong_self_convention)]
    fn from_fp(_fp: &Self::FPExpression, rm: RoundingMode, signed: bool) -> crate::Result<Self>;

    /// Zero-extend the current [`SmtExpr`] to the passed bit width and return
    /// the resulting [`SmtExpr`].
    #[must_use]
    fn zero_ext(&self, width: u32) -> Self;

    /// Sign-extend the current [`SmtExpr`] to the passed bit width and return
    /// the resulting [`SmtExpr`].
    #[must_use]
    fn sign_ext(&self, width: u32) -> Self;

    #[must_use]
    fn resize_unsigned(&self, width: u32) -> Self;

    /// [`SmtExpr`] equality check. Both [`SmtExpr`]s must have the same bit
    /// width, the result is returned as an [`SmtExpr`] of width `1`.
    #[must_use]
    fn _eq(&self, other: &Self) -> Self;

    /// [`SmtExpr`] inequality check. Both [`SmtExpr`]s must have the same bit
    /// width, the result is returned as an [`SmtExpr`] of width `1`.
    #[must_use]
    fn _ne(&self, other: &Self) -> Self;

    /// [`SmtExpr`] unsigned greater than. Both [`SmtExpr`]s must have the
    /// same bit width, the result is returned as an [`SmtExpr`] of width
    /// `1`.
    #[must_use]
    fn ugt(&self, other: &Self) -> Self;

    /// [`SmtExpr`] unsigned greater than or equal. Both [`SmtExpr`]s must
    /// have the same bit width, the result is returned as an [`SmtExpr`]
    /// of width `1`.
    #[must_use]
    fn ugte(&self, other: &Self) -> Self;

    /// [`SmtExpr`] unsigned less than. Both [`SmtExpr`]s must have the same
    /// bit width, the result is returned as an [`SmtExpr`] of width `1`.
    #[must_use]
    fn ult(&self, other: &Self) -> Self;

    /// [`SmtExpr`] unsigned less than or equal. Both [`SmtExpr`]s must have
    /// the same bit width, the result is returned as an [`SmtExpr`] of
    /// width `1`.
    #[must_use]
    fn ulte(&self, other: &Self) -> Self;

    /// [`SmtExpr`] signed greater than. Both [`SmtExpr`]s must have the same
    /// bit width, the result is returned as an [`SmtExpr`] of width `1`.
    #[must_use]
    fn sgt(&self, other: &Self) -> Self;

    /// [`SmtExpr`] signed greater or equal than. Both [`SmtExpr`]s must have
    /// the same bit width, the result is returned as an [`SmtExpr`] of
    /// width `1`.
    #[must_use]
    fn sgte(&self, other: &Self) -> Self;

    /// [`SmtExpr`] signed less than. Both [`SmtExpr`]s must have the same bit
    /// width, the result is returned as an [`SmtExpr`] of width `1`.
    #[must_use]
    fn slt(&self, other: &Self) -> Self;

    /// [`SmtExpr`] signed less than or equal. Both [`SmtExpr`]s must have the
    /// same bit width, the result is returned as an [`SmtExpr`] of width
    /// `1`.
    #[must_use]
    fn slte(&self, other: &Self) -> Self;

    #[must_use]
    fn add(&self, other: &Self) -> Self;

    #[must_use]
    fn sub(&self, other: &Self) -> Self;

    #[must_use]
    fn mul(&self, other: &Self) -> Self;

    #[must_use]
    fn udiv(&self, other: &Self) -> Self;

    #[must_use]
    fn sdiv(&self, other: &Self) -> Self;

    #[must_use]
    fn urem(&self, other: &Self) -> Self;

    #[must_use]
    fn srem(&self, other: &Self) -> Self;

    #[must_use]
    fn not(&self) -> Self;

    #[must_use]
    fn and(&self, other: &Self) -> Self;

    #[must_use]
    fn or(&self, other: &Self) -> Self;

    #[must_use]
    fn xor(&self, other: &Self) -> Self;

    #[must_use]
    fn shift(&self, steps: &Self, direction: Shift) -> Self;

    #[must_use]
    fn ite(&self, then_bv: &Self, else_bv: &Self) -> Self;

    #[must_use]
    fn concat(&self, other: &Self) -> Self;

    #[must_use]
    fn slice(&self, low: u32, high: u32) -> Self;

    #[must_use]
    fn uaddo(&self, other: &Self) -> Self;

    #[must_use]
    fn saddo(&self, other: &Self) -> Self;

    #[must_use]
    fn usubo(&self, other: &Self) -> Self;

    #[must_use]
    fn ssubo(&self, other: &Self) -> Self;

    #[must_use]
    fn umulo(&self, other: &Self) -> Self;

    #[must_use]
    fn smulo(&self, other: &Self) -> Self;

    #[must_use]
    fn simplify(self) -> Self;

    #[must_use]
    fn get_constant(&self) -> Option<u64>;

    #[must_use]
    fn get_a_solution(&self, e: &[Self]) -> Option<u64>;

    #[must_use]
    fn get_identifier(&self) -> Option<String>;

    #[must_use]
    fn get_constant_bool(&self) -> Option<bool>;

    #[must_use]
    fn to_binary_string(&self) -> String;

    #[must_use]
    fn replace_part(&self, start_idx: u32, replace_with: Self) -> Self;

    /// Saturated unsigned addition. Adds `self` with `other` and if the result
    /// overflows the maximum value is returned.
    ///
    /// Requires that `self` and `other` have the same width.
    #[must_use]
    fn uadds(&self, other: &Self) -> Self;

    /// Saturated signed addition. Adds `self` with `other` and if the result
    /// overflows either the maximum or minimum value is returned, depending
    /// on the sign bit of `self`.
    ///
    /// Requires that `self` and `other` have the same width.
    #[must_use]
    fn sadds(&self, other: &Self) -> Self;

    /// Saturated unsigned subtraction.
    ///
    /// Subtracts `self` with `other` and if the result overflows it is clamped
    /// to zero, since the values are unsigned it can never go below the
    /// minimum value.
    #[must_use]
    fn usubs(&self, other: &Self) -> Self;

    /// Saturated signed subtraction.
    ///
    /// Subtracts `self` with `other` with the result clamped between the
    /// largest and smallest value allowed by the bit-width.
    #[must_use]
    fn ssubs(&self, other: &Self) -> Self;

    /// Pushes a constraint to the queue.
    fn push(&self);

    /// Removes the latest requirement from the queue.
    fn pop(&self);
}

impl From<crate::memory::MemoryError> for crate::smt::MemoryError {
    fn from(value: crate::memory::MemoryError) -> Self {
        Self::MemoryFileError(value)
    }
}

pub trait Context {
    type Expr: SmtExpr;
    fn new_from_u64(&self, val: u64, bits: u32) -> Self::Expr;
}
impl<T: SmtMap> Context for T {
    type Expr = <Self as SmtMap>::Expression;

    fn new_from_u64(&self, val: u64, bits: u32) -> Self::Expr {
        <Self as SmtMap>::from_u64(&self, val, bits)
    }
}
