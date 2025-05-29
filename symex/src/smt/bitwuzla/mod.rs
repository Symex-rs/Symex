use std::{ffi::CStr, rc::Rc};

use bitwuzla::{option::ModelGen, SolverResult, BV};

pub mod expr;
pub mod fpexpr;
pub mod memory;

use expr::BitwuzlaExpr;
use memory::BitwuzlaMemory;

// Re-exports.
use super::{SmtExpr, SmtSolver, Solutions, SolverError};
use crate::warn;

#[derive(Clone, Debug)]
pub struct Bitwuzla {
    pub ctx: Rc<bitwuzla::Bitwuzla>,
}

unsafe extern "C" fn abort_callback(data: *const std::os::raw::c_char) {
    let data = CStr::from_ptr(data);
    match data.to_str() {
        Ok(val) => eprintln!("Bitwuzla failed internally with message {}", val),
        Err(_) => eprintln!("Bitwuzla failed internally with invalid cstring message"),
    }

    panic!("Bitwuzla internal error");
}

impl SmtSolver for Bitwuzla {
    type Expression = BitwuzlaExpr;
    type FpExpression = fpexpr::FpExpr;

    fn new() -> Self {
        //ctx.set_opt(BtorOption::Incremental(true));
        //ctx.set_opt(BtorOption::PrettyPrint(true));
        //ctx.set_opt(BtorOption::OutputNumberFormat(NumberFormat::Hexadecimal));
        let solver = bitwuzla::Bitwuzla::builder()
            // .logging(bitwuzla::option::LogLevel::Debug)
            // .verbosity(bitwuzla::option::Verbosity::Level3)
            .n_threads(24)
            .rewrite_level(bitwuzla::option::RewriteLevel::More)
            .model_gen(ModelGen::All)
            .set_abort_callback(abort_callback)
            .incremental(true)
            .build();
        Self { ctx: Rc::new(solver) }
    }

    fn one(&self, bits: u32) -> Self::Expression {
        self._one(bits)
    }

    fn pop(&self) {
        self._pop();
    }

    fn zero(&self, size: u32) -> Self::Expression {
        self._zero(size)
    }

    fn unconstrained(&self, size: u32, name: &str) -> Self::Expression {
        warn!("New unconstrained value {name}");
        self._unconstrained(size, name)
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        self._from_bool(value)
    }

    fn from_u64(&self, value: u64, size: u32) -> Self::Expression {
        self._from_u64(value, size)
    }

    fn from_binary_string(&self, bits: &str) -> Self::Expression {
        self._from_binary_string(bits)
    }

    fn unsigned_max(&self, size: u32) -> Self::Expression {
        self._unsigned_max(size)
    }

    fn signed_max(&self, size: u32) -> Self::Expression {
        self._signed_max(size)
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

    fn get_values(&self, expr: &Self::Expression, upper_bound: u32) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self._get_values(expr, upper_bound)
    }

    fn must_be_equal(&self, lhs: &Self::Expression, rhs: &Self::Expression) -> Result<bool, super::SolverError> {
        self._must_be_equal(lhs, rhs)
    }

    fn can_equal(&self, lhs: &Self::Expression, rhs: &Self::Expression) -> Result<bool, super::SolverError> {
        self._can_equal(lhs, rhs)
    }

    fn get_solutions(&self, expr: &Self::Expression, upper_bound: u32) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self._get_solutions(expr, upper_bound)
    }

    fn unconstrained_fp(&self, ty: general_assembly::extension::ieee754::OperandType, name: &str) -> Self::FpExpression {
        fpexpr::FpExpr::unconstrained(self.ctx.clone(), &ty, Some(name))
    }

    fn unconstrained_fp_unnamed(&self, ty: general_assembly::extension::ieee754::OperandType) -> Self::FpExpression {
        fpexpr::FpExpr::unconstrained(self.ctx.clone(), &ty, None)
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

                let solution = BitwuzlaExpr(BV::from_binary_str(self.ctx.clone(), &solution));
                Ok(solution)
            } else {
                Err(SolverError::Unsat)
            }
        };
        result()

        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::Disabled));
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
        BitwuzlaExpr::_ne(constraint, &self.from_u64(0, constraint.size())).0.assert();
    }

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to `upper_bound`, the returned
    /// [`Solutions`] has variants for if the number of solution exceeds the
    /// upper bound.
    pub fn _get_values(&self, expr: &BitwuzlaExpr, upper_bound: u32) -> Result<Solutions<BitwuzlaExpr>, SolverError> {
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
        let constraint = SmtExpr::_ne(lhs, rhs);
        let result = self.is_sat_with_constraint(&constraint)?;
        Ok(!result)
    }

    /// Check if `lhs` and `rhs` can be equal under the current constraints.
    pub fn _can_equal(&self, lhs: &BitwuzlaExpr, rhs: &BitwuzlaExpr) -> Result<bool, SolverError> {
        self.is_sat_with_constraint(&SmtExpr::_eq(lhs, rhs))
    }

    /// Find solutions to `expr`.
    ///
    /// Returns concrete solutions up to a maximum of `upper_bound`. If more
    /// solutions are available the error [`SolverError::TooManySolutions`]
    /// is returned.
    pub fn _get_solutions2(&self, expr: &BitwuzlaExpr, upper_bound: u32) -> Result<Solutions<BitwuzlaExpr>, SolverError> {
        let result = self.get_values(expr, upper_bound)?;
        match result {
            Solutions::Exactly(solutions) => Ok(Solutions::Exactly(solutions)),
            Solutions::AtLeast(_) => Err(SolverError::TooManySolutions),
        }
    }

    // TODO: Compare this against the other... Not sure why there are two.
    fn _get_solutions(&self, expr: &BitwuzlaExpr, upper_bound: u32) -> Result<Solutions<BitwuzlaExpr>, SolverError> {
        let mut solutions = Vec::new();

        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::All));

        let result = || {
            while solutions.len() < upper_bound as usize && self.is_sat()? {
                let solution = expr.0.get_a_solution().disambiguate();
                let solution = solution.as_01x_str();
                let solution = BitwuzlaExpr(BV::from_binary_str(self.ctx.clone(), &solution));

                // Constrain the next value to not be an already found solution.
                self.assert(&SmtExpr::_ne(expr, &solution));

                solutions.push(solution);
            }

            let exists_more_solutions = self.is_sat()?;
            if exists_more_solutions {
                return Ok(Solutions::AtLeast(solutions));
            }
            Ok(Solutions::Exactly(solutions))
        };
        result()

        //self.ctx.set_opt(BtorOption::ModelGen(ModelGen::Disabled));
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
        assert!(a.size() == 32);
        let a = smt.unconstrained(64, "64");
        assert!(a.size() == 64);
        let a = smt.unconstrained(53, "53");
        assert!(a.size() == 53);
    }

    #[test]
    fn test_zero_ext() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        assert!(a.size() == 1);
        let a = a.zero_ext(32);
        assert!(a.size() == 32);
        assert!(a.get_constant() == Some(1));
        let a = smt.from_u64(2, 2);
        assert!(a.size() == 2);
        let a = a.zero_ext(32);
        assert!(a.size() == 32);
        assert!(a.get_constant() == Some(2));
    }

    #[test]
    fn test_sign_ext() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        assert!(a.size() == 1);
        let a = a.sign_ext(32);
        assert!(a.size() == 32);
        assert!(a.get_constant() == Some(u32::MAX as u64));
        let a = smt.from_u64(1, 2);
        assert!(a.size() == 2);
        let a = a.zero_ext(32);
        assert!(a.size() == 32);
        assert!(a.get_constant() == Some(1));
    }

    #[test]
    fn test_resize_unsigned() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        assert!(a.size() == 1);
        let a = a.resize_unsigned(32);
        assert!(a.size() == 32);
        assert!(a.get_constant() == Some(1));
        let a = smt.from_u64(2, 2);
        assert!(a.size() == 2);
        let a = a.resize_unsigned(32);
        assert!(a.size() == 32);
        assert!(a.get_constant() == Some(2));
        let a = smt.from_u64(2, 2);
        assert!(a.size() == 2);
        let a = a.resize_unsigned(1);
        assert!(a.size() == 1);
        assert!(a.get_constant() == Some(0));
        let a = a.resize_unsigned(2);
        assert!(a.size() == 2);
        assert!(a.get_constant() == Some(0));
    }

    #[test]
    fn test_eq() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::_eq(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(0, 1);
        assert!(SmtExpr::_eq(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::_eq(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b011011010011, 32);
        assert!(SmtExpr::_eq(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b101011010011, 32);
        assert!(SmtExpr::_eq(&a, &b).get_constant() == Some(1));
    }

    #[test]
    fn test_ne() {
        let smt = smt();
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::_ne(&a, &b).get_constant() == Some(0));
        let a = smt.from_u64(1, 1);
        let b = smt.from_u64(0, 1);
        assert!(SmtExpr::_ne(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0, 1);
        let b = smt.from_u64(1, 1);
        assert!(SmtExpr::_ne(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b011011010011, 32);
        assert!(SmtExpr::_ne(&a, &b).get_constant() == Some(1));
        let a = smt.from_u64(0b101011010011, 32);
        let b = smt.from_u64(0b101011010011, 32);
        assert!(SmtExpr::_ne(&a, &b).get_constant() == Some(0));
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
        extension::ieee754::{self, RoundingMode},
        operand::{DataWord, Operand},
        operation::Operation,
    };
    use hashbrown::HashMap;

    use crate::{
        arch::{arm::v6::ArmV6M, Architecture, NoArchitectureOverride},
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
        initiation::NoArchOverride,
        logging::NoLogger,
        path_selection::PathSelector,
        project::Project,
        smt::{
            bitwuzla::{Bitwuzla, BitwuzlaExpr},
            SmtExpr,
            SmtFPExpr,
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
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
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
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
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
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
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
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
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
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
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
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
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
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        VM::new_test_vm(project, state, NoLogger).unwrap()
    }

    #[test]
    fn test_fp_div_un_even_ties_to_even_explicit() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesToEven),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 2);
    }

    #[test]
    fn test_fp_div_un_even_ties_to_even_system_level() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        executor.state.fp_state.rounding_mode = RoundingMode::TiesToEven;
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: None,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 2);
    }

    #[test]
    fn test_fp_div_mul() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(4)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR4".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });

        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Multiplication {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR4".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR5".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR5".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 6);
    }

    #[test]
    fn test_fp_non_computational() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(0)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsZero,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsInfinite,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsZero,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsInfinite,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);
    }

    #[test]
    fn test_fp_compare() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Equal,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Equal,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Greater,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Greater,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::NotGreater,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Less,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Less,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::LessOrEqual,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);
    }

    #[test]
    fn test_fp_load_store_address() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(144)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("Convert from int done");
        let operation = Operation::Ieee754(ieee754::Operations::Sqrt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Address(general_assembly::operand::Operand::Immediate(DataWord::Word32(0xdead_beef))),
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("sqrt done");

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Address(general_assembly::operand::Operand::Immediate(DataWord::Word32(0xdead_beef))),
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("Round to int done");

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 Result: {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 12)
    }

    #[test]
    fn test_fp_load_store_register() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());
        let operand_r1 = Operand::Register("R1".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(144)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Sqrt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Sqrt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                    signed: true,
                }, // ieee754::OperandStorage::Address(general_assembly::operand::Operand::Address(DataWord::Word32(120), 32)),,
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let r1 = executor.get_operand_value(&operand_r1, &mut NoLogger).unwrap();
        println!("R1 Result: {:?}, {:?}", r1, r1.get_constant());

        let fpreg = ieee754::Operand {
            ty: ieee754::OperandType::Binary32,
            value: ieee754::OperandStorage::Register {
                id: "FPR1".to_owned(),
                ty: ieee754::OperandType::Binary32,
            },
        };
        let fpreg = executor
            .get_fp_operand_value(fpreg, ieee754::OperandType::Binary32, RoundingMode::TiesTowardZero, &mut NoLogger)
            .unwrap();
        println!(
            "FPREG Result: {:?}, {:?}",
            fpreg,
            fpreg
                .round_to_integral(RoundingMode::TiesTowardZero)
                .expect("Roundable")
                .to_bv(RoundingMode::TiesTowardZero, true)
                .expect("Convertable")
                .get_constant()
        );

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                    signed: true,
                }, // ieee754::OperandStorage::Address(general_assembly::operand::Operand::Address(DataWord::Word32(120), 32)),
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 Result: {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 12)
    }

    #[test]
    fn test_fp_sqrt() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(144)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Sqrt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 12)
    }

    #[test]
    fn test_fp_fma() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());
        let operand_r1 = Operand::Register("R1".to_owned());
        let operand_r2 = Operand::Register("R2".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32((-99i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32((-100i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r2.clone(),
            source: Operand::Immediate(DataWord::Word32((100i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R2".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::FusedMultiplication {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            add: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), (99 * 100) + 100);
    }
    #[test]
    fn test_fp_abs() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32((-99i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Abs {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 99);

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32((112i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Abs {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 112)
    }

    #[test]
    fn test_fp_div_un_even() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(13)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, (42. as f32 / 12.).floor() as u64);
    }

    #[test]
    fn test_fp_mul() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(12)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Multiplication {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42 * 12);
    }

    #[test]
    fn test_fp_sub() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(12)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Subtraction {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42 - 12);
    }

    #[test]
    fn test_fp_add() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(12)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Addition {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42 + 12);
    }

    #[test]
    fn test_move() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // move imm into reg
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42);

        // move reg to local
        let local_r0 = Operand::Local("R0".to_owned());
        let operation = Operation::Move {
            destination: local_r0.clone(),
            source: operand_r0.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0 = executor.get_operand_value(&local_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42);

        // Move immediate to local memory addr
        let imm = Operand::Immediate(DataWord::Word32(23));
        let memory_op = Operand::AddressInLocal("R0".to_owned(), 32);
        let operation = Operation::Move {
            destination: memory_op.clone(),
            source: imm.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let dexpr_addr = executor.get_dexpr_from_dataword(DataWord::Word32(42));
        let in_memory_value = executor.state.read_word_from_memory(&dexpr_addr).unwrap().get_constant().unwrap();

        assert_eq!(in_memory_value, 23);

        // Move from memory to a local
        let operation = Operation::Move {
            destination: local_r0.clone(),
            source: memory_op.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let local_value = executor.get_operand_value(&local_r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(local_value, 23);
    }

    #[test]
    fn test_add_vm() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

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
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 58);

        // Test add with same operand and destination
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: r0.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 74);

        // Test add with negative number
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus70.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, (-28i32 as u32) as u64);

        // Test add overflow
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_umax.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 41);
    }

    #[test]
    fn test_adc() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

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

        executor.execute_operation(&operation, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 54);

        // test add with overflow
        executor.state.set_flag("C".to_owned(), false_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_umax.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 11);

        // test add with carry in
        executor.state.set_flag("C".to_owned(), true_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 55);
    }

    #[test]
    fn test_sub() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

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
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 26);

        // Test sub with same operand and destination
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: r0.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 10);

        // Test sub with negative number
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus70.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 112);

        // Test sub underflow
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_imin.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, ((i32::MIN) as u32 + 42) as u64);
    }

    #[test]
    fn test_mul() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

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
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 672);

        // multiplication right minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value as u32, -672i32 as u32);

        // multiplication left minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_minus_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value as u32, -672i32 as u32);

        // multiplication both minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_minus_42.clone(),
            operand2: imm_minus_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 672);
    }

    #[test]
    fn test_set_v_flag() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

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
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(!v_flag);

        // overflow
        let operation = Operation::SetVFlag {
            operand1: imm_imax.clone(),
            operand2: imm_12.clone(),
            sub: false,
            carry: false,
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(v_flag);

        // underflow
        let operation = Operation::SetVFlag {
            operand1: imm_imin.clone(),
            operand2: imm_12.clone(),
            sub: true,
            carry: false,
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

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

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).ok().unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 1);
    }

    #[test]
    #[should_panic]
    fn test_any() {
        let bw = Bitwuzla::new();
        let a_word = bw.unconstrained(32, "a_word");
        a_word.get_constant().unwrap();
    }

    #[test]
    fn test_simple_fp() {
        //let mut vm = setup_test_vm();
        //let i = i.local_into();
        //let f = f.local_into();
        //let project = vm.project;
        //let mut executor =
        // GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm,
        // project);
        //
        //pseudo!([
        //    let i = 0i32;
        //    Warn("vcvt to i",i_signed);
        //    let i2 = Resize(i_signed, f32);
        //    f = i2/base;
        //]);
        //assert_eq!(r0_value, 1);
    }
}
