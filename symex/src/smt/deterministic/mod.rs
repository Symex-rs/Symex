use std::{cmp::Ordering, fmt::Display, rc::Rc};

use bitwuzla::{Array, Btor, SolverResult, BV};

pub mod expr;

use expr::BitwuzlaExpr;
// Re-exports.
use general_assembly::{prelude::DataWord, shift::Shift};
use hashbrown::HashMap;

use super::{ProgramMemory, SmtExpr, SmtMap, SmtSolver, Solutions, SolverError};
use crate::{
    memory::{MemoryError, BITS_IN_BYTE},
    project::Project,
    warn,
    Endianness,
};

#[derive(Clone, Debug)]
pub struct Deterministic {}

impl SmtSolver for Deterministic {
    type Expression = u32;
    type Memory = DeterministicMemory;

    fn new() -> Self {
        //ctx.set_opt(BtorOption::Incremental(true));
        //ctx.set_opt(BtorOption::PrettyPrint(true));
        //ctx.set_opt(BtorOption::OutputNumberFormat(NumberFormat::Hexadecimal));

        Self {}
    }

    fn one(&self, bits: u32) -> Self::Expression {
        1
    }

    fn pop(&self) {}

    fn zero(&self, size: u32) -> Self::Expression {
        0
    }

    fn unconstrained(&self, size: u32, name: &str) -> Self::Expression {
        panic!("Cannot have unconstrained deterministic values.")
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        value as u32
    }

    fn from_u64(&self, value: u64, _size: u32) -> Self::Expression {
        value as u32
    }

    fn from_binary_string(&self, bits: &str) -> Self::Expression {
        bits.parse()
    }

    fn unsigned_max(&self, size: u32) -> Self::Expression {
        self._unsigned_max(size)
    }

    fn signed_max(&self, size: u32) -> Self::Expression {
        (1 << (size + 1)) - 1
    }

    fn signed_min(&self, size: u32) -> Self::Expression {
        self._signed_min(size)
    }

    fn get_value(&self, expr: &Self::Expression) -> Result<Self::Expression, super::SolverError> {
        self._get_value(expr)
    }

    fn push(&self) {
        self._push();
    }

    fn is_sat(&self) -> Result<bool, super::SolverError> {
        self._is_sat()
    }

    fn is_sat_with_constraint(&self, constraint: &Self::Expression) -> Result<bool, super::SolverError> {
        self._is_sat_with_constraint(constraint)
    }

    fn is_sat_with_constraints(&self, constraints: &[Self::Expression]) -> Result<bool, super::SolverError> {
        self._is_sat_with_constraints(constraints)
    }

    fn assert(&self, constraint: &Self::Expression) {
        self._assert(constraint);
    }

    fn get_values(&self, expr: &Self::Expression, upper_bound: usize) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self._get_values(expr, upper_bound)
    }

    fn must_be_equal(&self, lhs: &Self::Expression, rhs: &Self::Expression) -> Result<bool, super::SolverError> {
        self._must_be_equal(lhs, rhs)
    }

    fn can_equal(&self, lhs: &Self::Expression, rhs: &Self::Expression) -> Result<bool, super::SolverError> {
        self._can_equal(lhs, rhs)
    }

    fn get_solutions(&self, expr: &Self::Expression, upper_bound: usize) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self._get_solutions(expr, upper_bound)
    }
}

impl Bitwuzla {
    fn _check_sat_result(&self, sat_result: SolverResult) -> Result<bool, SolverError> {
        match sat_result {
            SolverResult::Sat => Ok(true),
            SolverResult::Unsat => Ok(false),
            SolverResult::Unknown => Err(SolverError::Unknown),
        }
    }

    pub fn _get_value(&self, expr: &BitwuzlaExpr) -> Result<BitwuzlaExpr, SolverError> {
        let expr = expr.clone().simplify();
        if expr.get_constant().is_some() {
            return Ok(expr.clone());
        }

        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::All));

        let result = || {
            if self.is_sat()? {
                self.is_sat()?;
                let solution = expr.0.get_a_solution().disambiguate();
                let solution = solution.as_01x_str();

                let solution = BitwuzlaExpr(BV::from_binary_str(self.ctx.clone(), solution));
                Ok(solution)
            } else {
                Err(SolverError::Unsat)
            }
        };
        let result = result();

        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::Disabled));

        result
    }

    pub fn _push(&self) {
        self.ctx.push(1);
    }

    pub fn _pop(&self) {
        self.ctx.pop(1);
    }

    /// Solve for the current solver state, and returns if the result is
    /// satisfiable.
    ///
    /// All asserts and assumes are implicitly combined with a boolean and.
    /// Returns true or false, and [`SolverError::Unknown`] if the result
    /// cannot be determined.
    pub fn _is_sat(&self) -> Result<bool, SolverError> {
        Ok(match self.ctx.sat() {
            SolverResult::Sat => true,
            SolverResult::Unsat => false,
            SolverResult::Unknown => false,
        })
    }

    /// Solve for the solver state with the assumption of the passed constraint.
    pub fn _is_sat_with_constraint(&self, constraint: &BitwuzlaExpr) -> Result<bool, SolverError> {
        // Assume the constraint, will be forgotten after the next call to `is_sat`.
        Ok(match self.ctx.check_sat_assuming(&[constraint.0.clone()]) {
            SolverResult::Sat => true,
            SolverResult::Unsat => false,
            SolverResult::Unknown => false,
        })
    }

    /// Solve for the solver state with the assumption of the passed
    /// constraints.
    pub fn _is_sat_with_constraints(&self, constraints: &[BitwuzlaExpr]) -> Result<bool, SolverError> {
        let mut constraints_new = Vec::with_capacity(constraints.len());
        for constraint in constraints {
            constraints_new.push(constraint.0.clone());
        }

        Ok(match self.ctx.check_sat_assuming(&constraints_new) {
            SolverResult::Sat => true,
            SolverResult::Unsat => false,
            SolverResult::Unknown => false,
        })
    }

    #[allow(clippy::unused_self)]
    /// Add the constraint to the solver.
    ///
    /// The passed constraint will be implicitly combined with the current state
    /// in a boolean `and`. Asserted constraints cannot be removed.
    pub fn _assert(&self, constraint: &BitwuzlaExpr) {
        constraint.0.assert();
    }

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to `upper_bound`, the returned
    /// [`Solutions`] has variants for if the number of solution exceeds the
    /// upper bound.
    pub fn _get_values(&self, expr: &BitwuzlaExpr, upper_bound: usize) -> Result<Solutions<BitwuzlaExpr>, SolverError> {
        let expr = expr.clone().simplify();
        if expr.get_constant().is_some() {
            return Ok(Solutions::Exactly(vec![expr]));
        }

        // Setup before checking for solutions.
        self.push();
        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::All));

        let result = self.get_solutions(&expr, upper_bound);

        // Restore solver to initial state.
        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::Disabled));
        self.pop();

        result
    }

    /// Returns `true` if `lhs` and `rhs` must be equal under the current
    /// constraints.
    pub fn _must_be_equal(&self, lhs: &BitwuzlaExpr, rhs: &BitwuzlaExpr) -> Result<bool, SolverError> {
        // Add the constraint lhs != rhs and invert the results. The only way
        // for `lhs != rhs` to be `false` is that if they are equal.
        let constraint = SmtExpr::ne(lhs, rhs);
        let result = self.is_sat_with_constraint(&constraint)?;
        Ok(!result)
    }

    /// Check if `lhs` and `rhs` can be equal under the current constraints.
    pub fn _can_equal(&self, lhs: &BitwuzlaExpr, rhs: &BitwuzlaExpr) -> Result<bool, SolverError> {
        self.is_sat_with_constraint(&SmtExpr::eq(lhs, rhs))
    }

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to a maximum of `upper_bound`. If more
    /// solutions are available the error [`SolverError::TooManySolutions`]
    /// is returned.
    pub fn _get_solutions2(&self, expr: &BitwuzlaExpr, upper_bound: usize) -> Result<Solutions<BitwuzlaExpr>, SolverError> {
        let result = self.get_values(expr, upper_bound)?;
        match result {
            Solutions::Exactly(solutions) => Ok(Solutions::Exactly(solutions)),
            Solutions::AtLeast(_) => Err(SolverError::TooManySolutions),
        }
    }

    // TODO: Compare this against the other... Not sure why there are two.
    fn _get_solutions(&self, expr: &BitwuzlaExpr, upper_bound: usize) -> Result<Solutions<BitwuzlaExpr>, SolverError> {
        let mut solutions = Vec::new();

        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::All));

        let result = || {
            while solutions.len() < upper_bound && self.is_sat()? {
                let solution = expr.0.get_a_solution().disambiguate();
                let solution = solution.as_01x_str();
                let solution = BitwuzlaExpr(BV::from_binary_str(self.ctx.clone(), solution));

                // Constrain the next value to not be an already found solution.
                self.assert(&SmtExpr::ne(&expr, &solution));

                solutions.push(solution);
            }

            let exists_more_solutions = self.is_sat()?;
            if exists_more_solutions {
                return Ok(Solutions::AtLeast(solutions));
            }
            Ok(Solutions::Exactly(solutions))
        };
        let result = result();

        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::Disabled));

        result
    }

    #[must_use]
    /// Create a new uninitialized expression of size `bits`.
    pub fn _unconstrained(&self, bits: u32, name: &str) -> BitwuzlaExpr {
        assert!(bits != 0, "Tried to create a 0 width unconstrained value");
        let ret = BitwuzlaExpr(BV::new(self.ctx.clone(), bits as u64, Some(name)));
        warn!("New unconstrained value {name} = {ret:?}");
        ret
    }

    #[must_use]
    /// Create a new expression set equal to `1` of size `bits`.
    pub fn _one(&self, bits: u32) -> BitwuzlaExpr {
        BitwuzlaExpr(BV::from_u64(self.ctx.clone(), 1, bits as u64))
    }

    #[must_use]
    /// Create a new expression set to zero of size `bits`.
    pub fn _zero(&self, bits: u32) -> BitwuzlaExpr {
        BitwuzlaExpr(BV::zero(self.ctx.clone(), bits as u64))
    }

    #[must_use]
    /// Create a new expression from a boolean value.
    pub fn _from_bool(&self, value: bool) -> BitwuzlaExpr {
        BitwuzlaExpr(BV::from_bool(self.ctx.clone(), value))
    }

    #[must_use]
    /// Create a new expression from an `u64` value of size `bits`.
    pub fn _from_u64(&self, value: u64, bits: u32) -> BitwuzlaExpr {
        BitwuzlaExpr(BV::from_u64(self.ctx.clone(), value, bits as u64))
    }

    #[must_use]
    /// Create an expression of size `bits` from a binary string.
    pub fn _from_binary_string(&self, bits: &str) -> BitwuzlaExpr {
        BitwuzlaExpr(BV::from_binary_str(self.ctx.clone(), bits))
    }

    #[must_use]
    /// Creates an expression of size `bits` containing the maximum unsigned
    /// value.
    pub fn _unsigned_max(&self, bits: u32) -> BitwuzlaExpr {
        let mut s = String::new();
        s.reserve_exact(bits as usize);
        for _ in 0..bits {
            s.push('1');
        }
        self._from_binary_string(&s)
    }

    #[must_use]
    /// Create an expression of size `bits` containing the maximum signed value.
    ///
    ///
    /// # Panics
    ///
    /// This function panics if the number of bits is zero.
    pub fn _signed_max(&self, bits: u32) -> BitwuzlaExpr {
        // Maximum value: 0111...1
        assert!(bits > 1);
        let mut s = String::from("0");
        s.reserve_exact(bits as usize);
        for _ in 0..bits - 1 {
            s.push('1');
        }
        self._from_binary_string(&s)
    }

    #[must_use]
    /// Create an expression of size `bits` containing the minimum signed value.
    ///
    ///
    /// # Panics
    ///
    /// This function panics if the number of bits is zero.
    pub fn _signed_min(&self, bits: u32) -> BitwuzlaExpr {
        // Minimum value: 1000..0
        assert!(bits > 1);
        let mut s = String::from("1");
        s.reserve_exact(bits as usize);
        for _ in 0..bits - 1 {
            s.push('0');
        }
        self._from_binary_string(&s)
    }
}

impl SmtExpr for BitwuzlaExpr {
    /// Returns the bit width of the [Expression].
    fn len(&self) -> u32 {
        self.0.get_width() as u32
    }

    /// Zero-extend the current [Expression] to the passed bit width and return
    /// the resulting [Expression].
    fn zero_ext(&self, width: u32) -> Self {
        assert!(self.len() <= width);
        match self.len().cmp(&width) {
            Ordering::Less => BitwuzlaExpr(self.0.uext(width as u64 - self.len() as u64)),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    /// Sign-extend the current [Expression] to the passed bit width and return
    /// the resulting [Expression].
    fn sign_ext(&self, width: u32) -> Self {
        assert!(self.len() <= width);
        match self.len().cmp(&width) {
            Ordering::Less => BitwuzlaExpr(self.0.sext(width as u64 - self.len() as u64)),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    fn resize_unsigned(&self, width: u32) -> Self {
        let ret = match self.len().cmp(&width) {
            Ordering::Equal => self.clone(),
            Ordering::Less => self.zero_ext(width),
            Ordering::Greater => self.slice(0, width - 1),
        };
        ret
    }

    /// [Expression] equality check. Both [Expression]s must have the same bit
    /// width, the result is returned as an [Expression] of width `1`.
    fn eq(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0._eq(&other.0).to_bv())
    }

    /// [Expression] inequality check. Both [Expression]s must have the same bit
    /// width, the result is returned as an [Expression] of width `1`.
    fn ne(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0._ne(&other.0).to_bv())
    }

    /// [Expression] unsigned greater than. Both [Expression]s must have the
    /// same bit width, the result is returned as an [Expression] of width
    /// `1`.
    fn ugt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ugt(&other.0).to_bv())
    }

    /// [Expression] unsigned greater than or equal. Both [Expression]s must
    /// have the same bit width, the result is returned as an [Expression]
    /// of width `1`.
    fn ugte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ugte(&other.0).to_bv())
    }

    /// [Expression] unsigned less than. Both [Expression]s must have the same
    /// bit width, the result is returned as an [Expression] of width `1`.
    fn ult(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ult(&other.0).to_bv())
    }

    /// [Expression] unsigned less than or equal. Both [Expression]s must have
    /// the same bit width, the result is returned as an [Expression] of
    /// width `1`.
    fn ulte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ulte(&other.0).to_bv())
    }

    /// [Expression] signed greater than. Both [Expression]s must have the same
    /// bit width, the result is returned as an [Expression] of width `1`.
    fn sgt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sgt(&other.0).to_bv())
    }

    /// [Expression] signed greater or equal than. Both [Expression]s must have
    /// the same bit width, the result is returned as an [Expression] of
    /// width `1`.
    fn sgte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sgte(&other.0).to_bv())
    }

    /// [Expression] signed less than. Both [Expression]s must have the same bit
    /// width, the result is returned as an [Expression] of width `1`.
    fn slt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.slt(&other.0).to_bv())
    }

    /// [Expression] signed less than or equal. Both [Expression]s must have the
    /// same bit width, the result is returned as an [Expression] of width
    /// `1`.
    fn slte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.slte(&other.0).to_bv())
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
        Self(self.0.cond_bv(&then_bv.0, &else_bv.0))
    }

    fn concat(&self, other: &Self) -> Self {
        Self(self.0.concat(&other.0))
    }

    fn slice(&self, low: u32, high: u32) -> Self {
        assert!(low <= high);
        assert!(high <= self.len());
        Self(self.0.slice(high as u64, low as u64))
    }

    fn uaddo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.uaddo(&other.0).to_bv())
    }

    fn saddo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.saddo(&other.0).to_bv())
    }

    fn usubo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.usubo(&other.0).to_bv())
    }

    fn ssubo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ssubo(&other.0).to_bv())
    }

    fn umulo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.umulo(&other.0).to_bv())
    }

    fn smulo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.smulo(&other.0).to_bv())
    }

    #[inline(always)]
    fn simplify(self) -> Self {
        //self.0.get_btor().simplify();
        //if let Some(c) = self.get_constant() {
        //    return Self(BV::from_u64(self.0.get_btor(), c, self.0.get_width()));
        //}
        self
    }

    fn get_constant(&self) -> Option<u64> {
        self.0.as_binary_str().as_ref().map(|word| u64::from_str_radix(word, 2).ok())?
        //match self.0.get_btor().sat() {
        //    SolverResult::Sat => {}
        //    _ => return None,
        //}
        //let sol = self.0.get_a_solution().deterministic()?;
        //
        //sol.as_u64()
    }

    fn get_identifier(&self) -> Option<String> {
        Some(self.0.get_symbol()?.to_string())
    }

    fn get_constant_bool(&self) -> Option<bool> {
        Some(self.0.as_binary_str()? == "1")

        //debug!("Trying to resolve {self:?} as boolean");
        //match self.0.get_btor().sat() {
        //    SolverResult::Sat => {}
        //    _ => return None,
        //}
        //let sol = self.0.get_a_solution().deterministic()?;
        //
        //sol.as_bool()
    }

    fn to_binary_string(&self) -> String {
        // TODO: Check if there's a better way to get the an underlying string.
        if self.len() <= 64 {
            let width = self.len() as usize;
            // If we for some reason get less binary digits, pad the start with zeroes.
            format!("{:0width$b}", self.get_constant().unwrap())
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
        let saturated = BitwuzlaExpr(BV::max_signed(self.get_ctx(), self.len() as u64));

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

        let min = BitwuzlaExpr(BV::min_signed(self.get_ctx(), width as u64));
        let max = BitwuzlaExpr(BV::max_signed(self.get_ctx(), width as u64));

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

        let zero = BitwuzlaExpr(BV::zero(self.get_ctx(), self.len() as u64));
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
        let min = BitwuzlaExpr(BV::min_signed(self.get_ctx(), width as u64));
        let max = BitwuzlaExpr(BV::max_signed(self.get_ctx(), width as u64));

        // Check the sign bit if max or min should be given on overflow.
        let is_negative = self.slice(self.len() - 1, self.len() - 1).simplify();

        overflow.ite(&is_negative.ite(&min, &max), &result).simplify()
    }

    fn pop(&self) {
        self.0.get_btor().pop(1);
    }

    fn push(&self) {
        self.0.get_btor().push(1);
    }
}

#[derive(Debug, Clone)]
pub struct ArrayMemory {
    /// Reference to the context so new symbols can be created.
    pub ctx: Rc<Btor>,

    /// Size of a pointer.
    ptr_size: u32,

    /// The actual memory. Stores all values written to memory.
    memory: Array<Rc<Btor>>,

    /// Memory endianness
    endianness: Endianness,
}

impl ArrayMemory {
    pub fn resolve_addresses(&self, addr: &BitwuzlaExpr, _upper_bound: usize) -> Result<Vec<BitwuzlaExpr>, MemoryError> {
        Ok(vec![addr.clone()])
    }

    pub fn read(&self, addr: &BitwuzlaExpr, bits: u32) -> Result<BitwuzlaExpr, MemoryError> {
        assert_eq!(addr.len(), self.ptr_size, "passed wrong sized address");

        let value = self.internal_read(addr, bits, self.ptr_size)?;
        Ok(value)
    }

    pub fn write(&mut self, addr: &BitwuzlaExpr, value: BitwuzlaExpr) -> Result<(), MemoryError> {
        assert_eq!(addr.len(), self.ptr_size, "passed wrong sized address");
        self.internal_write(addr, value, self.ptr_size)
    }

    /// Creates a new memory containing only uninitialized memory.
    pub fn new(ctx: Rc<bitwuzla::Bitwuzla>, ptr_size: u32, endianness: Endianness) -> Self {
        let memory = Array::new(ctx.clone(), ptr_size as u64, BITS_IN_BYTE as u64, Some("memory"));

        Self {
            ctx,
            ptr_size,
            memory,
            endianness,
        }
    }

    /// Reads an u8 from the given address.
    fn read_u8(&self, addr: &BitwuzlaExpr) -> BitwuzlaExpr {
        BitwuzlaExpr(self.memory.read(&addr.0))
    }

    /// Writes an u8 value to the given address.
    fn write_u8(&mut self, addr: &BitwuzlaExpr, val: BitwuzlaExpr) {
        let _ = self.ctx.simplify();
        self.memory = self.memory.write(&addr.0, &val.0);
    }

    /// Reads `bits` from `addr.
    ///
    /// If the number of bits are less than `BITS_IN_BYTE` then individual bits
    /// can be read, but if the number of bits exceed `BITS_IN_BYTE` then
    /// full bytes must be read.
    fn internal_read(&self, addr: &BitwuzlaExpr, bits: u32, ptr_size: u32) -> Result<BitwuzlaExpr, MemoryError> {
        let value = if bits < BITS_IN_BYTE {
            self.read_u8(addr).slice(bits - 1, 0)
        } else {
            // Ensure we only read full bytes now.
            assert_eq!(bits % BITS_IN_BYTE, 0, "Must read bytes, if bits >= 8");
            let num_bytes = bits / BITS_IN_BYTE;

            let mut bytes = Vec::new();

            for byte in 0..num_bytes {
                let offset = BitwuzlaExpr(BV::from_u64(self.ctx.clone(), byte as u64, ptr_size as u64));
                let read_addr = addr.add(&offset);
                let value = self.read_u8(&read_addr);
                bytes.push(value);
            }

            match self.endianness {
                Endianness::Little => bytes.into_iter().reduce(|acc, v| v.concat(&acc)).unwrap(),
                Endianness::Big => bytes.into_iter().rev().reduce(|acc, v| v.concat(&acc)).unwrap(),
            }
        };

        Ok(value)
    }

    fn internal_write(&mut self, addr: &BitwuzlaExpr, value: BitwuzlaExpr, ptr_size: u32) -> Result<(), MemoryError> {
        // Check if we should zero extend the value (if it less than 8-bits).
        let value = if value.len() < BITS_IN_BYTE { value.zero_ext(BITS_IN_BYTE) } else { value };

        // Ensure the value we write is a multiple of `BITS_IN_BYTE`.
        assert_eq!(value.len() % BITS_IN_BYTE, 0);

        let num_bytes = value.len() / BITS_IN_BYTE;
        for n in 0..num_bytes {
            let low_bit = n * BITS_IN_BYTE;
            let high_bit = (n + 1) * BITS_IN_BYTE - 1;
            let byte = value.slice(low_bit, high_bit);

            let offset = match self.endianness {
                Endianness::Little => BitwuzlaExpr(BV::from_u64(self.ctx.clone(), n as u64, ptr_size as u64)),
                Endianness::Big => BitwuzlaExpr(BV::from_u64(self.ctx.clone(), (num_bytes - 1 - n) as u64, ptr_size as u64)),
            };
            let addr = addr.add(&offset);
            self.write_u8(&addr, byte);
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct BitwuzlaMemory {
    ram: ArrayMemory,
    register_file: HashMap<String, BitwuzlaExpr>,
    flags: HashMap<String, BitwuzlaExpr>,
    variables: HashMap<String, BitwuzlaExpr>,
    program_memory: &'static Project,
    word_size: usize,
    pc: u64,
    initial_sp: BitwuzlaExpr,
}

impl SmtMap for BitwuzlaMemory {
    type Expression = BitwuzlaExpr;
    type ProgramMemory = &'static Project;
    type SMT = Bitwuzla;

    fn new(smt: Self::SMT, program_memory: &'static Project, word_size: usize, endianness: Endianness, initial_sp: Self::Expression) -> Result<Self, crate::GAError> {
        let ram = {
            let memory = Array::new(smt.ctx.clone(), word_size as u64, BITS_IN_BYTE as u64, Some("memory"));

            ArrayMemory {
                ctx: smt.ctx,
                ptr_size: word_size as u32,
                memory,
                endianness,
            }
        };
        Ok(Self {
            ram,
            register_file: HashMap::new(),
            flags: HashMap::new(),
            variables: HashMap::new(),
            program_memory,
            word_size,
            pc: 0,
            initial_sp,
        })
    }

    fn get(&self, idx: &Self::Expression, size: usize) -> Result<Self::Expression, crate::smt::MemoryError> {
        if let Some(address) = idx.get_constant() {
            if !self.program_memory.address_in_range(address) {
                let read = self.ram.read(idx, size as u32)?;

                return Ok(read);
            }
            return Ok(match self.program_memory.get(address, size as u32)? {
                DataWord::Word8(value) => self.from_u64(value as u64, 8),
                DataWord::Word16(value) => self.from_u64(value as u64, 16),
                DataWord::Word32(value) => self.from_u64(value as u64, 32),
                DataWord::Word64(value) => self.from_u64(value as u64, 64),
            });
        }
        Ok(self.ram.read(idx, size as u32)?)
    }

    fn set(&mut self, idx: &Self::Expression, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        let value = value.simplify();
        if let Some(address) = idx.get_constant() {
            if self.program_memory.address_in_range(address) {
                if let Some(_value) = value.get_constant() {
                    todo!("Handle static program memory writes");
                    //Return Ok(self.program_memory.set(address, value)?);
                }
                todo!("Handle non static program memory writes");
            }
        }
        self.ram.write(idx, value)?;
        Ok(())
    }

    fn get_pc(&self) -> Result<Self::Expression, crate::smt::MemoryError> {
        let ret = self.from_u64(self.pc, self.word_size);
        Ok(ret)
    }

    fn set_pc(&mut self, value: u32) -> Result<(), crate::smt::MemoryError> {
        self.pc = value as u64;
        Ok(())
    }

    fn set_flag(&mut self, idx: &str, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        self.flags.insert(idx.to_string(), value);
        Ok(())
    }

    fn get_flag(&mut self, idx: &str) -> Result<Self::Expression, crate::smt::MemoryError> {
        let ret = match self.flags.get(idx) {
            Some(val) => val.clone(),
            _ => {
                let ret = self.unconstrained(idx, 1);
                self.flags.insert(idx.to_owned(), ret.clone());
                ret
            }
        };
        Ok(ret)
    }

    fn set_register(&mut self, idx: &str, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        if idx == "PC" {
            return self.set_pc(match value.get_constant() {
                Some(val) => val as u32,
                None => return Err(crate::smt::MemoryError::PcNonDetmerinistic),
            });
        }
        let value = value.simplify();
        self.register_file.insert(idx.to_string(), value);
        Ok(())
    }

    fn get_register(&mut self, idx: &str) -> Result<Self::Expression, crate::smt::MemoryError> {
        if idx == "PC" {
            return self.get_pc();
        }
        let ret = match self.register_file.get(idx) {
            Some(val) => val.clone(),
            None => {
                let ret = self.unconstrained(idx, self.word_size);
                self.register_file.insert(idx.to_owned(), ret.clone());
                ret
            }
        };
        // Ensure that any read from the same register returns the
        //self.register_file.get(idx);
        Ok(ret)
    }

    fn from_u64(&self, value: u64, size: usize) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width value");
        BitwuzlaExpr(BV::from_u64(self.ram.ctx.clone(), value & ((1 << size) - 1), size as u64))
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        BitwuzlaExpr(BV::from_bool(self.ram.ctx.clone(), value))
    }

    fn unconstrained(&mut self, name: &str, size: usize) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width unconstrained value");
        let ret = BV::new(self.ram.ctx.clone(), size as u64, Some(name));
        let ret = BitwuzlaExpr(ret);
        ret.resize_unsigned(size as u32);
        self.variables.insert(name.to_string(), ret.clone());
        warn!("New unconstrained value {name} = {ret:?}");
        ret
    }

    fn get_ptr_size(&self) -> usize {
        self.program_memory.get_ptr_size() as usize
    }

    fn get_from_instruction_memory(&self, address: u64) -> crate::Result<&[u8]> {
        warn!("Reading instruction from memory");
        Ok(self.program_memory.get_raw_word(address)?)
    }

    fn get_stack(&mut self) -> (Self::Expression, Self::Expression) {
        // TODO: Make this more generic.
        (self.initial_sp.clone(), self.register_file.get("SP").expect("Could not get register SP").clone())
    }
}

//impl From<MemoryError> for crate::smt::MemoryError {
//    fn from(value: MemoryError) -> Self {
//        Self::MemoryFileError(value)
//
//}

impl Display for BitwuzlaMemory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\tVariables:\r\n")?;
        for (key, value) in (&self.variables).iter() {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => strip(format!("{:?}", value)),
            })?;
        }
        f.write_str("\tRegister file:\r\n")?;
        for (key, value) in (&self.register_file).iter() {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => strip(format!("{:?}", value)),
            })?;
        }
        f.write_str("\tFlags:\r\n")?;

        for (key, value) in (&self.flags).iter() {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => strip(format!("{:?}", value)),
            })?;
        }
        Ok(())
    }
}

fn strip(s: String) -> String {
    if 50 < s.len() {
        return "Large symbolic expression".to_string();
    }
    s
}

#[cfg(test)]
mod test_smt_expr {
    use crate::smt::{bitwuzla::Bitwuzla, SmtExpr, SmtSolver};

    fn smt() -> Bitwuzla {
        Bitwuzla::new()
    }

    #[test]
    fn test_add() {
        let smt = smt();
        let a = smt.from_u64(1, 32);
        let b = smt.from_u64(1, 32);
        assert!(a.add(&b).get_constant() == Some(2));

        let a = smt.from_u64(u32::MAX as u64, 32);
        let b = smt.from_u64(2, 32);
        let ret = a.add(&b).get_constant();
        println!("Ret {ret:?}");
        assert!(ret == Some(1));

        let a = smt.from_u64(u32::MAX as u64, 32);
        let b = smt.from_u64(u32::MAX as u64, 32);
        assert!(a.add(&b).get_constant() == Some(u32::MAX as u64 - 1));

        let a = smt.from_u64(u32::MAX as u64, 32);
        let b = smt.from_u64(u32::MAX as u64 - 2 as u64, 32);
        assert!(a.add(&b).get_constant() == Some(u32::MAX as u64 - 3));
    }

    #[test]
    fn test_add_sub() {
        let smt = smt();
        let a = smt.from_u64(1, 32);
        let b = smt.from_u64(1, 32);
        assert!(a.sub(&b).get_constant() == Some(0));

        let a = smt.from_u64(0, 32);
        let b = smt.from_u64(u32::MAX as u64, 32);
        let ret = a.sub(&b).get_constant();
        assert!(ret == Some(1));

        let a = smt.from_u64(u32::MAX as u64, 32);
        let b = smt.from_u64(u32::MAX as u64, 32);
        assert!(a.sub(&b).get_constant() == Some(0));

        let a = smt.from_u64(u32::MAX as u64, 32);
        let b = smt.from_u64(u32::MAX as u64 - 2 as u64, 32);
        assert!(a.sub(&b).get_constant() == Some(2));
    }

    #[test]
    fn test_len() {
        let smt = smt();
        let a = smt.from_u64(1, 32);
        assert!(a.len() == 32);
        let a = smt.unconstrained(64, "64");
        assert!(a.len() == 64);
        let a = smt.unconstrained(53, "53");
        assert!(a.len() == 53);
    }

    #[test]
    fn test_zero_ext() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        assert!(a.len() == 1);
        let a = a.zero_ext(32);
        assert!(a.len() == 32);
        assert!(a.get_constant() == Some(1));
        let a = smt.from_u64(2, 2);
        assert!(a.len() == 2);
        let a = a.zero_ext(32);
        assert!(a.len() == 32);
        assert!(a.get_constant() == Some(2));
    }

    #[test]
    fn test_sign_ext() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        assert!(a.len() == 1);
        let a = a.sign_ext(32);
        assert!(a.len() == 32);
        assert!(a.get_constant() == Some(u32::MAX as u64));
        let a = smt.from_u64(1, 2);
        assert!(a.len() == 2);
        let a = a.zero_ext(32);
        assert!(a.len() == 32);
        assert!(a.get_constant() == Some(1));
    }

    #[test]
    fn test_resize_unsigned() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        assert!(a.len() == 1);
        let a = a.resize_unsigned(32);
        assert!(a.len() == 32);
        assert!(a.get_constant() == Some(1));
        let a = smt.from_u64(2, 2);
        assert!(a.len() == 2);
        let a = a.resize_unsigned(32);
        assert!(a.len() == 32);
        assert!(a.get_constant() == Some(2));
        let a = smt.from_u64(2, 2);
        assert!(a.len() == 2);
        let a = a.resize_unsigned(1);
        assert!(a.len() == 1);
        assert!(a.get_constant() == Some(0));
        let a = a.resize_unsigned(2);
        assert!(a.len() == 2);
        assert!(a.get_constant() == Some(0));
    }

    #[test]
    fn test_eq() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::eq(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(0, 1);
        assert!(SmtExpr::eq(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::eq(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b011011010011, 32);
        assert!(SmtExpr::eq(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b101011010011, 32);
        assert!(SmtExpr::eq(&a, &b).get_constant() == Some(1));
    }

    #[test]
    fn test_ne() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::ne(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(0, 1);
        assert!(SmtExpr::ne(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::ne(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b011011010011, 32);
        assert!(SmtExpr::ne(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b101011010011, 32);
        assert!(SmtExpr::ne(&a, &b).get_constant() == Some(0));
    }

    #[test]
    fn test_ugt() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::ugt(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(0, 1);
        assert!(SmtExpr::ugt(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::ugt(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b011011010011, 32);
        assert!(SmtExpr::ugt(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b101011010011, 32);
        assert!(SmtExpr::ugt(&a, &b).get_constant() == Some(0));
    }

    #[test]
    fn test_ugte() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::ugte(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(0, 1);
        assert!(SmtExpr::ugte(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::ugte(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b011011010011, 32);
        assert!(SmtExpr::ugte(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b101011010011, 32);
        assert!(SmtExpr::ugte(&a, &b).get_constant() == Some(1));
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

    use crate::{
        arch::{arm::v6::ArmV6M, Architecture},
        defaults::bitwuzla::{DefaultComposition, DefaultCompositionNoLogger},
        executor::{
            add_with_carry,
            count_leading_ones,
            count_leading_zeroes,
            count_ones,
            count_zeroes,
            hooks::HookContainer,
            instruction::{CycleCount, Instruction},
            state::GAState,
            vm::VM,
            GAExecutor,
        },
        logging::NoLogger,
        project::Project,
        smt::{
            bitwuzla::{Bitwuzla, BitwuzlaExpr},
            SmtExpr,
            SmtMap,
            SmtSolver,
        },
        Endianness,
        WordSize,
    };

    #[test]
    fn test_count_ones_concrete() {
        let ctx = Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
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
        let result: BitwuzlaExpr = count_ones(&num1, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result: BitwuzlaExpr = count_ones(&num32, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result: BitwuzlaExpr = count_ones(&numff, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 8);
    }

    #[test]
    fn test_count_ones_symbolic() {
        let ctx = Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
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
        let ctx = Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
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
        let ctx = Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
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
        let ctx = Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
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
        let ctx = Bitwuzla::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
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
        let ctx = Bitwuzla::new();
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
        VM::new_test_vm(project, state).unwrap()
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
    fn test_add_vm() {
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
            executor.execute_instruction(&p, &mut NoLogger).ok();
        }

        let r0_value = executor.get_operand_value(&r0, &local, &mut NoLogger).ok().unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 1);
    }

    #[test]
    #[should_panic]
    fn test_any() {
        let bw = Bitwuzla::new();
        let a_word = bw.unconstrained(32, "a_word");
        a_word.get_constant().unwrap();
    }
}
