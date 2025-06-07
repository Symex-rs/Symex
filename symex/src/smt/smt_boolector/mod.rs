use std::{cmp::Ordering, pin::Pin, rc::Rc};

use bitwuzla::BVSolution;
use boolector::{
    option::{BtorOption, ModelGen, NumberFormat},
    Btor,
    SolverResult,
    BV,
};

mod expr;
mod solver;

// Re-exports.
pub use expr::BoolectorExpr;
pub mod memory;
use expr::Pinned;
use general_assembly::{extension::ieee754::OperandType, shift::Shift};
use memory::BoolectorMemory;
pub(super) use solver::BoolectorIncrementalSolver;

use super::{SmtExpr, SmtFPExpr, SmtSolver, Solutions, SolverError};

#[must_use]
pub type DExpr = BoolectorExpr;
#[must_use]
pub type DSolver = BoolectorIncrementalSolver;
#[must_use]
pub type DContext = BoolectorSolverContext;
#[must_use]
pub type DArray = BoolectorArray;

#[derive(Debug, Clone)]
pub struct Boolector {
    pub ctx: Pinned<Btor>,
}

impl Boolector {
    fn deep_clone(&self) -> Self {
        Self {
            ctx: Pinned(Rc::pin(self.ctx.0.duplicate())),
        }
    }
}

impl SmtSolver for Boolector {
    type Expression = BoolectorExpr;
    type FpExpression = (Self::Expression, OperandType);

    fn new() -> Self {
        let ctx = Rc::pin(Btor::new());

        ctx.set_opt(BtorOption::Incremental(true));
        ctx.set_opt(BtorOption::PrettyPrint(true));
        ctx.set_opt(BtorOption::VariableSubst(true));
        ctx.set_opt(BtorOption::EliminateSlices(true));
        ctx.set_opt(BtorOption::OutputNumberFormat(NumberFormat::Hexadecimal));

        Self { ctx: Pinned(ctx) }
    }

    fn one(&self, bits: u32) -> Self::Expression {
        self.inner_one(bits)
    }

    fn pop(&self) {
        self.inner_pop();
    }

    fn zero(&self, size: u32) -> Self::Expression {
        self.inner_zero(size)
    }

    fn unconstrained(&self, size: u32, name: &str) -> Self::Expression {
        self.inner_unconstrained(size, Some(name))
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        self.inner_from_bool(value)
    }

    fn from_u64(&self, value: u64, size: u32) -> Self::Expression {
        self.inner_from_u64(value, size)
    }

    fn unsigned_max(&self, size: u32) -> Self::Expression {
        self.inner_unsigned_max(size)
    }

    fn signed_max(&self, size: u32) -> Self::Expression {
        self.inner_signed_max(size)
    }

    fn signed_min(&self, size: u32) -> Self::Expression {
        self.inner_signed_min(size)
    }

    fn push(&self) {
        self.inner_push();
    }

    fn is_sat(&self) -> Result<bool, super::SolverError> {
        self.inner_is_sat()
    }

    fn is_sat_with_constraint(&self, constraint: &Self::Expression) -> Result<bool, super::SolverError> {
        self.inner_is_sat_with_constraint(constraint)
    }

    fn is_sat_with_constraints(&self, constraints: &[Self::Expression]) -> Result<bool, super::SolverError> {
        self.inner_is_sat_with_constraints(constraints)
    }

    fn assert(&self, constraint: &Self::Expression) {
        self.inner_assert(constraint);
    }

    fn get_values(&self, expr: &Self::Expression, upper_bound: u32) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self.inner_get_values(expr, upper_bound)
    }

    fn get_solutions(&self, expr: &Self::Expression, upper_bound: u32) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self.inner_get_solutions(expr, upper_bound)
    }

    fn unconstrained_fp_unnamed(&self, ty: OperandType) -> Self::FpExpression {
        let bv = self.inner_unconstrained(ty.size(), None);
        (bv, ty)
    }

    fn unconstrained_fp(&self, ty: OperandType, name: &str) -> Self::FpExpression {
        let bv = self.inner_unconstrained(ty.size(), Some(name));
        (bv, ty)
    }
}

impl Boolector {
    const fn inner_check_sat_result(sat_result: SolverResult) -> Result<bool, SolverError> {
        match sat_result {
            SolverResult::Sat => Ok(true),
            SolverResult::Unsat => Ok(false),
            SolverResult::Unknown => Err(SolverError::Unknown),
        }
    }

    pub fn inner_get_value(&self, expr: &BoolectorExpr) -> Result<BoolectorExpr, SolverError> {
        let expr = expr.clone().simplify();
        if expr.get_constant().is_some() {
            return Ok(expr);
        }

        self.ctx.0.set_opt(BtorOption::ModelGen(ModelGen::All));

        let result = || {
            if self.is_sat()? {
                self.is_sat()?;
                let solution = expr.0.get_a_solution().disambiguate();
                let solution = solution.as_01x_str();

                let solution = BoolectorExpr(BV::from_binary_str(self.ctx.clone(), solution));
                Ok(solution)
            } else {
                Err(SolverError::Unsat)
            }
        };
        let result = result();

        self.ctx.0.set_opt(BtorOption::ModelGen(ModelGen::Disabled));

        result
    }

    pub fn inner_push(&self) {
        self.ctx.0.push(1);
    }

    pub fn inner_pop(&self) {
        self.ctx.0.pop(1);
    }

    /// Solve for the current solver state, and returns if the result is
    /// satisfiable.
    ///
    /// All asserts and assumes are implicitly combined with a boolean and.
    /// Returns true or false, and [`SolverError::Unknown`] if the result
    /// cannot be determined.
    pub fn inner_is_sat(&self) -> Result<bool, SolverError> {
        let sat_result = self.ctx.0.sat();
        self.check_sat_result(sat_result)
    }

    /// Solve for the solver state with the assumption of the passed constraint.
    pub fn inner_is_sat_with_constraint(&self, constraint: &BoolectorExpr) -> Result<bool, SolverError> {
        // Assume the constraint, will be forgotten after the next call to `is_sat`.
        constraint.0.assume();
        self.is_sat()
    }

    /// Solve for the solver state with the assumption of the passed
    /// constraints.
    pub fn inner_is_sat_with_constraints(&self, constraints: &[BoolectorExpr]) -> Result<bool, SolverError> {
        for constraint in constraints {
            constraint.0.assume();
        }
        self.is_sat()
    }

    #[allow(clippy::unused_self)]
    /// Add the constraint to the solver.
    ///
    /// The passed constraint will be implicitly combined with the current state
    /// in a boolean `and`. Asserted constraints cannot be removed.
    pub fn inner_assert(&self, constraint: &BoolectorExpr) {
        constraint.0.assert();
    }

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to `upper_bound`, the returned
    /// [`Solutions`] has variants for if the number of solution exceeds the
    /// upper bound.
    pub fn inner_get_values(&self, expr: &BoolectorExpr, upper_bound: u32) -> Result<Solutions<BoolectorExpr>, SolverError> {
        let expr = expr.clone().simplify();
        if expr.get_constant().is_some() {
            return Ok(Solutions::Exactly(vec![expr]));
        }

        // Setup before checking for solutions.
        self.push();
        self.ctx.0.set_opt(BtorOption::ModelGen(ModelGen::All));

        let result = self.get_solutions(&expr, upper_bound);

        // Restore solver to initial state.
        self.ctx.0.set_opt(BtorOption::ModelGen(ModelGen::Disabled));
        self.pop();

        result
    }

    /// Returns `true` if `lhs` and `rhs` must be equal under the currene?
    /// constraints.
    pub fn inner_must_be_equal(&self, lhs: &BoolectorExpr, rhs: &BoolectorExpr) -> Result<bool, SolverError> {
        // Add the constraint lhs != rhs and invert the results. The only way
        // for `lhs != rhs` to be `false` is that if they are equal.
        let constraint = lhs.ne(rhs);
        let result = self.is_sat_with_constraint(&constraint)?;
        Ok(!result)
    }

    /// Check if `lhs` and `rhs` can be equal under the current constraints.
    pub fn inner_can_equal(&self, lhs: &BoolectorExpr, rhs: &BoolectorExpr) -> Result<bool, SolverError> {
        self.is_sat_with_constraint(&lhs.eq(rhs))
    }

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to a maximum of `upper_bound`. If more
    /// solutions are available the error [`SolverError::TooManySolutions`]
    /// is returned.
    pub fn inner_get_solutions2(&self, expr: &BoolectorExpr, upper_bound: u32) -> Result<Vec<BoolectorExpr>, SolverError> {
        let result = self.get_values(expr, upper_bound)?;
        match result {
            Solutions::Exactly(solutions) => Ok(solutions),
            Solutions::AtLeast(_) => Err(SolverError::TooManySolutions),
        }
    }

    // TODO: Compare this against the other... Not sure why there are two.
    fn inner_get_solutions(&self, expr: &BoolectorExpr, upper_bound: u32) -> Result<Solutions<BoolectorExpr>, SolverError> {
        let mut solutions = Vec::new();

        self.ctx.0.set_opt(BtorOption::ModelGen(ModelGen::All));

        let result = || {
            while solutions.len() < upper_bound as usize && self.is_sat()? {
                // NOTE: Disambiguate call here is probably dangerous.
                let solution = expr.0.get_a_solution().disambiguate();
                let solution = solution.as_01x_str();
                let solution = BoolectorExpr(BV::from_binary_str(self.ctx.clone(), solution));

                // Constrain the next value to not be an already found solution.
                self.assert(&expr.ne(&solution));

                solutions.push(solution);
            }

            let exists_more_solutions = self.is_sat()?;
            if exists_more_solutions {
                return Ok(Solutions::AtLeast(solutions));
            }
            Ok(Solutions::Exactly(solutions))
        };
        let result = result();

        self.ctx.0.set_opt(BtorOption::ModelGen(ModelGen::Disabled));

        result
    }

    #[must_use]
    /// Create a new uninitialized expression of size `bits`.
    pub fn inner_unconstrained(&self, bits: u32, name: Option<&str>) -> BoolectorExpr {
        BoolectorExpr(BV::new(self.ctx.clone(), bits, name))
    }

    #[must_use]
    /// Create a new expression set equal to `1` of size `bits`.
    pub fn inner_one(&self, bits: u32) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_u64(self.ctx.clone(), 1, bits))
    }

    #[must_use]
    /// Create a new expression set to zero of size `bits`.
    pub fn inner_zero(&self, bits: u32) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::zero(self.ctx.clone(), bits))
    }

    #[must_use]
    /// Create a new expression from a boolean value.
    pub fn inner_from_bool(&self, value: bool) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_bool(self.ctx.clone(), value))
    }

    #[must_use]
    /// Create a new expression from an `u64` value of size `bits`.
    pub fn inner_from_u64(&self, value: u64, bits: u32) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_u64(self.ctx.clone(), value, bits))
    }

    #[must_use]
    /// Create an expression of size `bits` from a binary string.
    pub fn inner_from_binary_string(&self, bits: &str) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_binary_str(self.ctx.clone(), bits))
    }

    #[must_use]
    /// Creates an expression of size `bits` containing the maximum unsigned
    /// value.
    pub fn inner_unsigned_max(&self, bits: u32) -> BoolectorExpr {
        let mut s = String::new();
        s.reserve_exact(bits as usize);
        for _ in 0..bits {
            s.push('1');
        }
        self.inner_from_binary_string(&s)
    }

    #[must_use]
    /// Create an expression of size `bits` containing the maximum signed value.
    ///
    ///
    /// # Panics
    ///
    /// This function panics if the number of bits is zero.
    pub fn inner_signed_max(&self, bits: u32) -> BoolectorExpr {
        // Maximum value: 0111...1
        assert!(bits > 1);
        let mut s = String::from("0");
        s.reserve_exact(bits as usize);
        for _ in 0..bits - 1 {
            s.push('1');
        }
        self.inner_from_binary_string(&s)
    }

    #[must_use]
    /// Create an expression of size `bits` containing the minimum signed value.
    ///
    ///
    /// # Panics
    ///
    /// This function panics if the number of bits is zero.
    pub fn inner_signed_min(&self, bits: u32) -> BoolectorExpr {
        // Minimum value: 1000...0
        assert!(bits > 1);
        let mut s = String::from("1");
        s.reserve_exact(bits as usize);
        for _ in 0..bits - 1 {
            s.push('0');
        }
        self.inner_from_binary_string(&s)
    }
}

/// `BoolectorSolverContext` handles the creation of expressions.
///
/// Keeps track of all the created expressions and the internal SMT state.
#[derive(Debug, Clone)]
pub struct BoolectorSolverContext {
    pub ctx: Pinned<Btor>,
}

impl BoolectorSolverContext {
    #[must_use]
    /// Create a new uninitialized expression of size `bits`.
    pub fn unconstrained(&self, bits: u32, name: Option<&str>) -> BoolectorExpr {
        BoolectorExpr(BV::new(self.ctx.clone(), bits, name))
    }

    #[must_use]
    /// Create a new uninitialized expression of size `bits`.
    pub fn unconstrained_fp(&self, ty: OperandType, name: Option<&str>) -> (BoolectorExpr, OperandType) {
        (BoolectorExpr(BV::new(self.ctx.clone(), ty.size(), name)), ty)
    }

    #[must_use]
    /// Create a new expression set equal to `1` of size `bits`.
    pub fn one(&self, bits: u32) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_u64(self.ctx.clone(), 1, bits))
    }

    #[must_use]
    /// Create a new expression set to zero of size `bits`.
    pub fn zero(&self, bits: u32) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::zero(self.ctx.clone(), bits))
    }

    #[must_use]
    /// Create a new expression from a boolean value.
    pub fn from_bool(&self, value: bool) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_bool(self.ctx.clone(), value))
    }

    #[must_use]
    /// Create a new expression from an `u64` value of size `bits`.
    pub fn from_u64(&self, value: u64, bits: u32) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_u64(self.ctx.clone(), value, bits))
    }

    #[must_use]
    /// Create an expression of size `bits` from a binary string.
    pub fn from_binary_string(&self, bits: &str) -> BoolectorExpr {
        BoolectorExpr(boolector::BV::from_binary_str(self.ctx.clone(), bits))
    }

    #[must_use]
    /// Creates an expression of size `bits` containing the maximum unsigned
    /// value.
    pub fn unsigned_max(&self, bits: u32) -> BoolectorExpr {
        let mut s = String::new();
        s.reserve_exact(bits as usize);
        for _ in 0..bits {
            s.push('1');
        }
        self.from_binary_string(&s)
    }

    #[must_use]
    /// Create an expression of size `bits` containing the maximum signed value.
    ///
    ///
    /// # Panics
    ///
    /// This function panics if the number of bits is zero.
    pub fn signed_max(&self, bits: u32) -> BoolectorExpr {
        // Maximum value: 0111..1
        assert!(bits > 1);
        let mut s = String::from("0");
        s.reserve_exact(bits as usize);
        for _ in 0..bits - 1 {
            s.push('1');
        }
        self.from_binary_string(&s)
    }

    #[must_use]
    /// Create an expression of size `bits` containing the minimum signed value.
    ///
    ///
    /// # Panics
    ///
    /// This function panics if the number of bits is zero.
    pub fn signed_min(&self, bits: u32) -> BoolectorExpr {
        // Minimum value: 1000..0
        assert!(bits > 1);
        let mut s = String::from("1");
        s.reserve_exact(bits as usize);
        for _ in 0..bits - 1 {
            s.push('0');
        }
        self.from_binary_string(&s)
    }
}

impl BoolectorSolverContext {
    #[must_use]
    pub fn new() -> Self {
        let btor = Btor::new();
        let ctx = Rc::pin(btor);
        ctx.set_opt(BtorOption::Incremental(true));
        ctx.set_opt(BtorOption::PrettyPrint(true));
        ctx.set_opt(BtorOption::OutputNumberFormat(NumberFormat::Hexadecimal));

        Self { ctx: Pinned(ctx) }
    }
}

/// Symbolic array where both index and stored values are symbolic.
#[derive(Debug, Clone)]
pub struct BoolectorArray(pub(super) boolector::Array<Pinned<Btor>>);

impl BoolectorArray {
    #[must_use]
    #[allow(clippy::cast_possible_truncation)]
    /// Create a new array where index has size `index_size` and each element
    /// has size `element_size`.
    pub fn new(ctx: &BoolectorSolverContext, index_size: u32, element_size: u32, name: &str) -> Self {
        let memory = boolector::Array::new(ctx.ctx.clone(), index_size, element_size, Some(name));

        Self(memory)
    }

    #[must_use]
    /// Return value with specific index.
    pub fn read(&self, index: &BoolectorExpr) -> BoolectorExpr {
        BoolectorExpr(self.0.read(&index.0))
    }

    /// Write value to index.
    pub fn write(&mut self, index: &BoolectorExpr, value: &BoolectorExpr) {
        self.0 = self.0.write(&index.0, &value.0);
    }
}

impl SmtExpr for BoolectorExpr {
    type FPExpression = (Self, OperandType);

    fn any(&self, width: u32) -> Self {
        Self(BV::new(self.0.get_btor(), width, None))
    }

    /// Converts from a floating point value.
    fn from_fp(fp: &Self::FPExpression, rm: general_assembly::extension::ieee754::RoundingMode, signed: bool) -> crate::Result<Self> {
        Ok(fp.0.any(fp.1.size()))
    }

    /// Returns the bit width of the [`BoolectorExpr`].
    fn size(&self) -> u32 {
        self.0.get_width()
    }

    fn get_identifier(&self) -> Option<String> {
        Some(self.0.get_symbol()?.to_string())
    }

    /// Zero-extend the current [`BoolectorExpr`] to the passed bit width and
    /// return the resulting [`BoolectorExpr`].
    fn zero_ext(&self, width: u32) -> Self {
        assert!(self.len() <= width);
        match self.len().cmp(&width) {
            Ordering::Less => Self(self.0.uext(width - self.len())),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    /// Sign-extend the current [`BoolectorExpr`] to the passed bit width and
    /// return the resulting [`BoolectorExpr`].
    fn sign_ext(&self, width: u32) -> Self {
        assert!(self.len() <= width);
        match self.len().cmp(&width) {
            Ordering::Less => Self(self.0.sext(width - self.len())),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    fn resize_unsigned(&self, width: u32) -> Self {
        match self.len().cmp(&width) {
            Ordering::Equal => self.clone(),
            Ordering::Less => self.zero_ext(width),
            Ordering::Greater => self.slice(0, width - 1),
        }
    }

    /// [`BoolectorExpr`] equality check. Both [`BoolectorExpr`]s must have the
    /// same bit width, the result is returned as an [`BoolectorExpr`] of
    /// width `1`.
    fn _eq(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0._eq(&other.0))
    }

    /// [`BoolectorExpr`] inequality check. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    fn _ne(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0._ne(&other.0))
    }

    /// [`BoolectorExpr`] unsigned greater than. Both [`BoolectorExpr`]s must
    /// have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    fn ugt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ugt(&other.0))
    }

    /// [`BoolectorExpr`] unsigned greater than or equal. Both
    /// [`BoolectorExpr`]s must have the same bit width, the result is
    /// returned as an [`BoolectorExpr`] of width `1`.
    fn ugte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ugte(&other.0))
    }

    /// [`BoolectorExpr`] unsigned less than. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    fn ult(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ult(&other.0))
    }

    /// [`BoolectorExpr`] unsigned less than or equal. Both [`BoolectorExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    fn ulte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ulte(&other.0))
    }

    /// [`BoolectorExpr`] signed greater than. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    fn sgt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sgt(&other.0))
    }

    /// [`BoolectorExpr`] signed greater or equal than. Both [`BoolectorExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    fn sgte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sgte(&other.0))
    }

    /// [`BoolectorExpr`] signed less than. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    fn slt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.slt(&other.0))
    }

    /// [`BoolectorExpr`] signed less than or equal. Both [`BoolectorExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    fn slte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.slte(&other.0))
    }

    fn add(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.add(&other.0))
    }

    fn sub(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sub(&other.0))
    }

    fn mul(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.mul(&other.0))
    }

    fn udiv(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.udiv(&other.0))
    }

    fn sdiv(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sdiv(&other.0))
    }

    fn urem(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.urem(&other.0))
    }

    fn srem(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.srem(&other.0))
    }

    fn not(&self) -> Self {
        Self(self.0.not())
    }

    fn and(&self, other: &Self) -> Self {
        Self(self.0.and(&other.0))
    }

    fn or(&self, other: &Self) -> Self {
        Self(self.0.or(&other.0))
    }

    fn xor(&self, other: &Self) -> Self {
        Self(self.0.xor(&other.0))
    }

    /// Shift left logical
    fn shift(&self, steps: &Self, direction: general_assembly::prelude::Shift) -> Self {
        match direction {
            Shift::Lsl => self.sll(steps),
            Shift::Lsr => self.srl(steps),
            Shift::Asr => self.sra(steps),
            Shift::Rrx => todo!(),
            Shift::Ror => todo!(),
        }
    }

    fn ite(&self, then_bv: &Self, else_bv: &Self) -> Self {
        assert_eq!(self.len(), 1);
        Self(self.0.cond_bv(&then_bv.0, &else_bv.0))
    }

    fn concat(&self, other: &Self) -> Self {
        Self(self.0.concat(&other.0))
    }

    fn slice(&self, low: u32, high: u32) -> Self {
        assert!(low <= high);
        assert!(high <= self.len());
        Self(self.0.slice(high, low))
    }

    fn uaddo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.uaddo(&other.0))
    }

    fn saddo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.saddo(&other.0))
    }

    fn usubo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.usubo(&other.0))
    }

    fn ssubo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ssubo(&other.0))
    }

    fn umulo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.umulo(&other.0))
    }

    fn smulo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.smulo(&other.0))
    }

    fn simplify(self) -> Self {
        self
    }

    fn get_constant(&self) -> Option<u64> {
        self.0.as_binary_str().map(|value| u64::from_str_radix(&value, 2).unwrap())
    }

    fn get_a_solution(&self, constraints: &[Self]) -> Option<u64> {
        self.0.get_a_solution().as_u64()
    }

    fn get_constant_bool(&self) -> Option<bool> {
        assert_eq!(self.len(), 1);
        self.0.as_binary_str().map(|value| value != "0")
    }

    fn to_binary_string(&self) -> String {
        // TODO: Check if there's a better way to get the an underlying string.
        if self.len() <= 64 {
            let width = self.len() as usize;
            match self.get_constant() {
                Some(c) => format!("{:0width$b}", c),
                None => format!("Non constant"), // {} (Others possible)", self.0.get_a_solution().disambiguate().as_01x_str()),
            }
        } else {
            let upper = self.slice(64, self.len() - 1).to_binary_string();
            let lower = self.slice(0, 63).to_binary_string();
            format!("{}{}", upper, lower)
        }
    }

    fn replace_part(&self, start_idx: u32, replace_with: Self) -> Self {
        let end_idx = start_idx + replace_with.len();
        assert!(end_idx <= self.len());

        let value = if start_idx == 0 {
            replace_with
        } else {
            let prefix = self.slice(0, start_idx - 1);
            replace_with.concat(&prefix)
        };

        let value = if end_idx == self.len() {
            value
        } else {
            let suffix = self.slice(end_idx, self.len() - 1);
            suffix.concat(&value)
        };
        assert_eq!(value.len(), self.len());

        value
    }

    /// Saturated unsigned addition. Adds `self` with `other` and if the result
    /// overflows the maximum value is returned.
    ///
    /// Requires that `self` and `other` have the same width.
    fn uadds(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());

        let result = self.add(other).simplify();
        let overflow = self.uaddo(other).simplify();
        let saturated = self.get_ctx().unsigned_max(self.len());

        overflow.ite(&saturated, &result)
    }

    /// Saturated signed addition. Adds `self` with `other` and if the result
    /// overflows either the maximum or minimum value is returned, depending
    /// on the sign bit of `self`.
    ///
    /// Requires that `self` and `other` have the same width.
    fn sadds(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        let width = self.len();

        let result = self.add(other).simplify();
        let overflow = self.saddo(other).simplify();

        let min = self.get_ctx().signed_min(width);
        let max = self.get_ctx().signed_max(width);

        // Check the sign bit if max or min should be given on overflow.
        let is_negative = self.slice(self.len() - 1, self.len() - 1).simplify();

        overflow.ite(&is_negative.ite(&min, &max), &result).simplify()
    }

    /// Saturated unsigned subtraction.
    ///
    /// Subtracts `self` with `other` and if the result overflows it is clamped
    /// to zero, since the values are unsigned it can never go below the
    /// minimum value.
    fn usubs(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());

        let result = self.sub(other).simplify();
        let overflow = self.usubo(other).simplify();

        let zero = self.get_ctx().zero(self.len());
        overflow.ite(&zero, &result)
    }

    /// Saturated signed subtraction.
    ///
    /// Subtracts `self` with `other` with the result clamped between the
    /// largest and smallest value allowed by the bit-width.
    fn ssubs(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());

        let result = self.sub(other).simplify();
        let overflow = self.ssubo(other).simplify();

        let width = self.len();
        let min = self.get_ctx().signed_min(width);
        let max = self.get_ctx().signed_max(width);

        // Check the sign bit if max or min should be given on overflow.
        let is_negative = self.slice(self.len() - 1, self.len() - 1).simplify();

        overflow.ite(&is_negative.ite(&min, &max), &result).simplify()
    }

    fn pop(&self) {
        self.0.get_btor().0.pop(1);
    }

    fn push(&self) {
        self.0.get_btor().0.push(1);
    }
}
