#![allow(clippy::len_without_is_empty)]
use std::{cmp::Ordering, rc::Rc};

use bitwuzla::{Btor, BV};
use general_assembly::{extension::ieee754::RoundingMode, shift::Shift};

use super::fpexpr::FpExpr;
use crate::smt::{SmtExpr, SmtFPExpr};

#[derive(Debug, Clone)]
pub struct BitwuzlaExpr(pub(crate) BV<Rc<Btor>>);

//impl BitwuzlaExpr {
//    fn unbounded(bv: BV<Rc<Btor>>) {
//        BV::new(btor, width, symbol)
//    }
//}
//
impl BitwuzlaExpr {
    pub fn get_ctx(&self) -> Rc<Btor> {
        self.0.get_btor()
    }

    /// Shift left logical
    pub fn sll(&self, other: &Self) -> Self {
        Self(self.0.sll(&other.0))
    }

    /// Shift right logical
    pub fn srl(&self, other: &Self) -> Self {
        Self(self.0.srl(&other.0))
    }

    /// Shift right arithmetic
    pub fn sra(&self, other: &Self) -> Self {
        Self(self.0.sra(&other.0))
    }
}

impl SmtExpr for BitwuzlaExpr {
    type FPExpression = FpExpr;

    fn any(&self, width: u32) -> Self {
        BitwuzlaExpr(BV::new(self.0.get_btor().clone(), width as u64, None))
    }

    fn from_fp(fp: &Self::FPExpression, rm: RoundingMode, signed: bool) -> crate::Result<Self> {
        fp.to_bv(rm, signed)
    }

    /// Returns the bit width of the [`BitwuzlaExpr`].
    fn size(&self) -> u32 {
        self.0.get_width() as u32
    }

    /// Zero-extend the current [`BitwuzlaExpr`] to the passed bit width and
    /// return the resulting [`BitwuzlaExpr`].
    fn zero_ext(&self, width: u32) -> Self {
        assert!(self.size() <= width);
        match self.size().cmp(&width) {
            Ordering::Less => BitwuzlaExpr(self.0.uext(width as u64 - self.size() as u64)),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    /// Sign-extend the current [`BitwuzlaExpr`] to the passed bit width and
    /// return the resulting [`BitwuzlaExpr`].
    fn sign_ext(&self, width: u32) -> Self {
        assert!(self.size() <= width);
        match self.size().cmp(&width) {
            Ordering::Less => BitwuzlaExpr(self.0.sext(width as u64 - self.size() as u64)),
            Ordering::Equal => self.clone(),
            Ordering::Greater => todo!(),
        }
    }

    fn resize_unsigned(&self, width: u32) -> Self {
        match self.size().cmp(&width) {
            Ordering::Equal => self.clone(),
            Ordering::Less => self.zero_ext(width),
            Ordering::Greater => self.slice(0, width - 1),
        }
    }

    /// [`BitwuzlaExpr`] equality check. Both [`BitwuzlaExpr`]s must have the
    /// same bit width, the result is returned as an [`BitwuzlaExpr`] of
    /// width `1`.
    fn _eq(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0._eq(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] inequality check. Both [`BitwuzlaExpr`]s must have the
    /// same bit width, the result is returned as an [`BitwuzlaExpr`] of
    /// width `1`.
    fn _ne(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0._ne(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] unsigned greater than. Both [`BitwuzlaExpr`]s must have
    /// the same bit width, the result is returned as an [`BitwuzlaExpr`] of
    /// width `1`.
    fn ugt(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.ugt(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] unsigned greater than or equal. Both [`BitwuzlaExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BitwuzlaExpr`] of width `1`.
    fn ugte(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.ugte(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] unsigned less than. Both [`BitwuzlaExpr`]s must have
    /// the same bit width, the result is returned as an [`BitwuzlaExpr`] of
    /// width `1`.
    fn ult(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.ult(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] unsigned less than or equal. Both [`BitwuzlaExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BitwuzlaExpr`] of width `1`.
    fn ulte(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.ulte(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] signed greater than. Both [`BitwuzlaExpr`]s must have
    /// the same bit width, the result is returned as an [`BitwuzlaExpr`] of
    /// width `1`.
    fn sgt(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.sgt(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] signed greater or equal than. Both [`BitwuzlaExpr`]s
    /// must have the same bit width, the result is returned as an
    /// [`BitwuzlaExpr`] of width `1`.
    fn sgte(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.sgte(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] signed less than. Both [`BitwuzlaExpr`]s must have the
    /// same bit width, the result is returned as an [`BitwuzlaExpr`] of
    /// width `1`.
    fn slt(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.slt(&other.0).to_bv())
    }

    /// [`BitwuzlaExpr`] signed less than or equal. Both [`BitwuzlaExpr`]s must
    /// have the same bit width, the result is returned as an
    /// [`BitwuzlaExpr`] of width `1`.
    fn slte(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.slte(&other.0).to_bv())
    }

    fn add(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.add(&other.0))
    }

    fn sub(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.sub(&other.0))
    }

    fn mul(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.mul(&other.0))
    }

    fn udiv(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.udiv(&other.0))
    }

    fn sdiv(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.sdiv(&other.0))
    }

    fn urem(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.urem(&other.0))
    }

    fn srem(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
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
        assert!(high <= self.size());
        Self(self.0.slice(high as u64, low as u64))
    }

    fn uaddo(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.uaddo(&other.0).to_bv())
    }

    fn saddo(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.saddo(&other.0).to_bv())
    }

    fn usubo(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.usubo(&other.0).to_bv())
    }

    fn ssubo(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.ssubo(&other.0).to_bv())
    }

    fn umulo(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        Self(self.0.umulo(&other.0).to_bv())
    }

    fn smulo(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
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
        // let str = self.0.as_binary_str().unwrap_or("Could not get value as
        // string!".to_string()); println!("Binary str : {str}");
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

    fn get_a_solution(&self, constraints: &[Self]) -> Option<u64> {
        let constraints: Vec<_> = constraints.iter().map(|el| el.0.clone()).collect();
        match self.0.get_btor().check_sat_assuming(&constraints) {
            bitwuzla::SolverResult::Sat => {}
            _ => return None,
        }
        self.0.get_a_solution().as_u64()
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
        if self.size() <= 64 {
            let width = self.size() as usize;
            match self.get_constant() {
                Some(val) =>
                // If we for some reason get less binary digits, pad the start with zeroes.
                {
                    format!("{:0width$b}", val)
                }
                None => match self.0.as_binary_str_pattern() {
                    Some(val) => format!("0b{} (others possible)", val),
                    None => String::from("UNSAT"),
                },
            }
        } else {
            let upper = self.slice(64, self.size() - 1).to_binary_string();
            let lower = self.slice(0, 63).to_binary_string();
            format!("{}{}", upper, lower)
        }
    }

    fn replace_part(&self, start_idx: u32, replace_with: Self) -> Self {
        let end_idx = start_idx + replace_with.size();
        assert!(end_idx <= self.size());

        let value = if start_idx == 0 {
            replace_with
        } else {
            let prefix = self.slice(0, start_idx - 1);
            replace_with.concat(&prefix)
        };

        let value = if end_idx == self.size() {
            value
        } else {
            let suffix = self.slice(end_idx, self.size() - 1);
            suffix.concat(&value)
        };
        assert_eq!(value.size(), self.size());

        value
    }

    /// Saturated unsigned addition. Adds `self` with `other` and if the result
    /// overflows the maximum value is returned.
    ///
    /// Requires that `self` and `other` have the same width.
    fn uadds(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());

        let result = self.add(other).simplify();
        let overflow = self.uaddo(other).simplify();
        let saturated = BitwuzlaExpr(BV::max_signed(self.get_ctx(), self.size() as u64));

        overflow.ite(&saturated, &result)
    }

    /// Saturated signed addition. Adds `self` with `other` and if the result
    /// overflows either the maximum or minimum value is returned, depending
    /// on the sign bit of `self`.
    ///
    /// Requires that `self` and `other` have the same width.
    fn sadds(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());
        let width = self.size();

        let result = self.add(other).simplify();
        let overflow = self.saddo(other).simplify();

        let min = BitwuzlaExpr(BV::min_signed(self.get_ctx(), width as u64));
        let max = BitwuzlaExpr(BV::max_signed(self.get_ctx(), width as u64));

        // Check the sign bit if max or min should be given on overflow.
        let is_negative = self.slice(self.size() - 1, self.size() - 1).simplify();

        overflow.ite(&is_negative.ite(&min, &max), &result).simplify()
    }

    /// Saturated unsigned subtraction.
    ///
    /// Subtracts `self` with `other` and if the result overflows it is clamped
    /// to zero, since the values are unsigned it can never go below the
    /// minimum value.
    fn usubs(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());

        let result = self.sub(other).simplify();
        let overflow = self.usubo(other).simplify();

        let zero = BitwuzlaExpr(BV::zero(self.get_ctx(), self.size() as u64));
        overflow.ite(&zero, &result)
    }

    /// Saturated signed subtraction.
    ///
    /// Subtracts `self` with `other` with the result clamped between the
    /// largest and smallest value allowed by the bit-width.
    fn ssubs(&self, other: &Self) -> Self {
        assert_eq!(self.size(), other.size());

        let result = self.sub(other).simplify();
        let overflow = self.ssubo(other).simplify();

        let width = self.size();
        let min = BitwuzlaExpr(BV::min_signed(self.get_ctx(), width as u64));
        let max = BitwuzlaExpr(BV::max_signed(self.get_ctx(), width as u64));

        // Check the sign bit if max or min should be given on overflow.
        let is_negative = self.slice(self.size() - 1, self.size() - 1).simplify();

        overflow.ite(&is_negative.ite(&min, &max), &result).simplify()
    }

    fn pop(&self) {
        self.0.get_btor().pop(1);
    }

    fn push(&self) {
        self.0.get_btor().push(1);
    }
}
