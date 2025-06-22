#![allow(clippy::len_without_is_empty)]
use std::{borrow::Borrow, cmp::Ordering, pin::Pin, rc::Rc};

use boolector::{option::BtorOption, Btor, BV};

use super::BoolectorSolverContext;

#[repr(transparent)]
#[derive(Debug)]
pub struct Pinned<T>(pub(crate) Pin<Rc<T>>);

impl<T> Borrow<T> for Pinned<T> {
    fn borrow(&self) -> &T {
        self.0.borrow()
    }
}

impl<T> Clone for Pinned<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: PartialEq + Eq> PartialEq for Pinned<P> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<P: PartialEq + Eq> Eq for Pinned<P> {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolectorExpr(pub(crate) BV<Pinned<Btor>>);

impl BoolectorExpr {
    #[must_use]
    /// Returns the bit width of the [`BoolectorExpr`].
    pub fn len(&self) -> u32 {
        self.0.get_width()
    }

    /// Zero-extend the current [`BoolectorExpr`] to the passed bit width and
    /// return the resulting [`BoolectorExpr`].
    #[must_use]
    pub fn zero_ext(&self, width: u32) -> Self {
        assert!(self.len() <= width);
        match self.len().cmp(&width) {
            Ordering::Less => BoolectorExpr(self.0.uext(width - self.len())),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    /// Sign-extend the current [`BoolectorExpr`] to the passed bit width and
    /// return the resulting [`BoolectorExpr`].
    #[must_use]
    pub fn sign_ext(&self, width: u32) -> Self {
        assert!(self.len() <= width);
        match self.len().cmp(&width) {
            Ordering::Less => BoolectorExpr(self.0.sext(width - self.len())),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    #[must_use]
    pub fn resize_unsigned(&self, width: u32) -> Self {
        match self.len().cmp(&width) {
            Ordering::Equal => self.clone(),
            Ordering::Less => self.zero_ext(width),
            Ordering::Greater => self.slice(0, width - 1),
        }
    }

    /// [`BoolectorExpr`] equality check. Both [`BoolectorExpr`]s must have the
    /// same bit width, the result is returned as an [`BoolectorExpr`] of
    /// width `1`.
    #[must_use]
    pub fn eq(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0._eq(&other.0))
    }

    /// [`BoolectorExpr`] inequality check. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    #[must_use]
    pub fn ne(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0._ne(&other.0))
    }

    /// [`BoolectorExpr`] unsigned greater than. Both [`BoolectorExpr`]s must
    /// have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    #[must_use]
    pub fn ugt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ugt(&other.0))
    }

    /// [`BoolectorExpr`] unsigned greater than or equal. Both
    /// [`BoolectorExpr`]s must have the same bit width, the result is
    /// returned as an [`BoolectorExpr`] of width `1`.
    #[must_use]
    pub fn ugte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ugte(&other.0))
    }

    /// [`BoolectorExpr`] unsigned less than. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    #[must_use]
    pub fn ult(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ult(&other.0))
    }

    /// [`BoolectorExpr`] unsigned less than or equal. Both [`BoolectorExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    #[must_use]
    pub fn ulte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ulte(&other.0))
    }

    /// [`BoolectorExpr`] signed greater than. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    #[must_use]
    pub fn sgt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sgt(&other.0))
    }

    /// [`BoolectorExpr`] signed greater or equal than. Both [`BoolectorExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    #[must_use]
    pub fn sgte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sgte(&other.0))
    }

    /// [`BoolectorExpr`] signed less than. Both [`BoolectorExpr`]s must have
    /// the same bit width, the result is returned as an [`BoolectorExpr`]
    /// of width `1`.
    #[must_use]
    pub fn slt(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.slt(&other.0))
    }

    /// [`BoolectorExpr`] signed less than or equal. Both [`BoolectorExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BoolectorExpr`] of width `1`.
    #[must_use]
    pub fn slte(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.slte(&other.0))
    }

    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.add(&other.0))
    }

    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sub(&other.0))
    }

    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.mul(&other.0))
    }

    #[must_use]
    pub fn udiv(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.udiv(&other.0))
    }

    #[must_use]
    pub fn sdiv(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.sdiv(&other.0))
    }

    #[must_use]
    pub fn urem(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.urem(&other.0))
    }

    #[must_use]
    pub fn srem(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.srem(&other.0))
    }

    #[must_use]
    pub fn not(&self) -> Self {
        Self(self.0.not())
    }

    #[must_use]
    pub fn and(&self, other: &Self) -> Self {
        Self(self.0.and(&other.0))
    }

    #[must_use]
    pub fn or(&self, other: &Self) -> Self {
        Self(self.0.or(&other.0))
    }

    #[must_use]
    pub fn xor(&self, other: &Self) -> Self {
        Self(self.0.xor(&other.0))
    }

    /// Shift left logical
    #[must_use]
    pub fn sll(&self, other: &Self) -> Self {
        Self(self.0.sll(&other.0))
    }

    /// Shift right logical
    #[must_use]
    pub fn srl(&self, other: &Self) -> Self {
        Self(self.0.srl(&other.0))
    }

    /// Shift right arithmetic
    #[must_use]
    pub fn sra(&self, other: &Self) -> Self {
        Self(self.0.sra(&other.0))
    }

    #[must_use]
    pub fn ite(&self, then_bv: &Self, else_bv: &Self) -> Self {
        assert_eq!(self.len(), 1);
        Self(self.0.cond_bv(&then_bv.0, &else_bv.0))
    }

    #[must_use]
    pub fn concat(&self, other: &Self) -> Self {
        Self(self.0.concat(&other.0))
    }

    #[must_use]
    pub fn slice(&self, low: u32, high: u32) -> Self {
        assert!(low <= high);
        assert!(high <= self.len());
        Self(self.0.slice(high, low))
    }

    #[must_use]
    pub fn uaddo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.uaddo(&other.0))
    }

    #[must_use]
    pub fn saddo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.saddo(&other.0))
    }

    #[must_use]
    pub fn usubo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.usubo(&other.0))
    }

    #[must_use]
    pub fn ssubo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.ssubo(&other.0))
    }

    #[must_use]
    pub fn umulo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.umulo(&other.0))
    }

    #[must_use]
    pub fn smulo(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len());
        Self(self.0.smulo(&other.0))
    }

    #[must_use]
    pub fn simplify(self) -> Self {
        self
    }

    #[must_use]
    pub fn get_constant(&self) -> Option<u64> {
        self.0.as_binary_str().map(|value| u64::from_str_radix(&value, 2).unwrap())
    }

    #[must_use]
    pub fn get_constant_bool(&self) -> Option<bool> {
        assert_eq!(self.len(), 1);
        self.0.as_binary_str().map(|value| value != "0")
    }

    #[must_use]
    pub fn get_as_symbolic_trinary_string(&self) -> String {
        self.0.get_btor().0.set_opt(BtorOption::ModelGen(boolector::option::ModelGen::All));

        match self.0.get_btor().0.sat() {
            boolector::SolverResult::Sat => {}
            _ => panic!("Tried to resolve as trinary string when value was not sat"),
        }
        self.0.get_btor().0.set_opt(BtorOption::ModelGen(boolector::option::ModelGen::All));
        let ret = self.0.get_a_solution().as_01x_str().to_string();
        self.0.get_btor().0.set_opt(BtorOption::ModelGen(boolector::option::ModelGen::Disabled));
        ret
    }

    #[must_use]
    pub fn to_binary_string(&self) -> String {
        // TODO: Check if there's a better way to get the an underlying string.
        if self.len() <= 64 {
            let width = self.len() as usize;
            // If we for some reason get less binary digits, pad the start with zeroes.
            match self.get_constant() {
                Some(val) => format!("{:0width$b}", val),
                None => format!("(non constant) {:?}", self),
            }
        } else {
            let upper = self.slice(64, self.len() - 1).to_binary_string();
            let lower = self.slice(0, 63).to_binary_string();
            format!("{}{}", upper, lower)
        }
    }

    #[must_use]
    pub fn get_ctx(&self) -> BoolectorSolverContext {
        let ctx = self.0.get_btor();
        BoolectorSolverContext { ctx }
    }

    #[must_use]
    pub fn replace_part(&self, start_idx: u32, replace_with: Self) -> Self {
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

    /// overflows the maximum value is returned.
    ///
    /// Requires that `self` and `other` have the same width.
    #[must_use]
    pub fn uadds(&self, other: &Self) -> Self {
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
    #[must_use]
    pub fn sadds(&self, other: &Self) -> Self {
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
    #[must_use]
    pub fn usubs(&self, other: &Self) -> Self {
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
    #[must_use]
    pub fn ssubs(&self, other: &Self) -> Self {
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
}
