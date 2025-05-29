use std::{borrow::Borrow, fmt::write, rc::Rc};

use anyhow::Context;
use bitwuzla::{fp::Formats, Bitwuzla, Btor, RoundingMode as RM, BV, FP};
use general_assembly::extension::ieee754::{ComparisonMode, NonComputational, OperandType, RoundingMode};

use super::expr::BitwuzlaExpr;
use crate::{
    smt::{SmtExpr, SmtFPExpr, SolverError},
    InternalError,
};

#[derive(Clone, Debug)]
pub enum FpOrBv<R: Clone + Borrow<bitwuzla::Bitwuzla> + std::fmt::Debug> {
    Fp(FP<R>),
    Bv(BV<R>),
}
#[derive(Clone, Debug)]
pub struct FpExpr {
    ctx: FpOrBv<Rc<Btor>>,
    ty: OperandType,
}

fn conv_ty(ty: &OperandType) -> Formats {
    match ty {
        OperandType::Binary16 => Formats::F16,
        OperandType::Binary32 => Formats::F32,
        OperandType::Binary64 => Formats::F64,
        OperandType::Binary128 => Formats::F128,
        _ => unimplemented!("No translation for this"),
    }
}

fn conv_rm(rm: &RoundingMode) -> RM {
    match rm {
        RoundingMode::Exact => unimplemented!("Bitwuzla has no support for exact rounding"),
        RoundingMode::TiesToEven => RM::RNE,
        RoundingMode::TiesTowardZero => RM::RTZ,
        RoundingMode::TiesToAway => RM::RNA,
        RoundingMode::TiesTowardPositive => RM::RTP,
        RoundingMode::TiesTowardNegative => RM::RTN,
    }
}

impl FpExpr {
    pub fn unconstrained(ctx: Rc<Btor>, ty: &OperandType, name: Option<&str>) -> Self {
        Self {
            ctx: FpOrBv::Fp(
                bitwuzla::FP::new(ctx, conv_ty(ty), name)
                    .map_err(|e| crate::GAError::SolverError(SolverError::Generic(format!("{e:?}"))))
                    .context("fp any")
                    .expect("Failed to create a new fp variable"),
            ),
            ty: ty.clone(),
        }
    }

    fn _compare(&self, other: &Self, cmp: general_assembly::extension::ieee754::ComparisonMode, _rm: RoundingMode) -> crate::Result<bitwuzla::Bool<Rc<Btor>>> {
        if other.ty != self.ty {
            return Err(crate::InternalError::TypeError).context(format!("While comparing a {:?} and a {:?}", self.ty, other.ty));
        }

        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let other_ctx: &FP<Rc<Bitwuzla>> = (&other.ctx).try_into()?;
        Ok(match cmp {
            ComparisonMode::Less => ctx.lt(other_ctx),
            ComparisonMode::NotLess => ctx.lt(other_ctx).not(),
            ComparisonMode::Greater => ctx.gt(other_ctx),
            ComparisonMode::NotGreater => ctx.gt(other_ctx).not(),
            ComparisonMode::Equal => ctx._eq(other_ctx),
            ComparisonMode::NotEqual => ctx._eq(other_ctx).not(),
            ComparisonMode::GreaterOrEqual => ctx.geq(other_ctx),
            ComparisonMode::LessOrEqual => ctx.leq(other_ctx),
            ComparisonMode::GreaterUnordered => unimplemented!("Bitwuzla has no support for this."),
            ComparisonMode::LessUnordered => unimplemented!("Bitwuzla has no support for this."),
        })
    }
}

impl SmtFPExpr for FpExpr {
    type Expression = super::expr::BitwuzlaExpr;

    fn any(&self, ty: OperandType) -> crate::Result<Self> {
        match &self.ctx {
            FpOrBv::Fp(fp) => Ok(Self {
                ctx: FpOrBv::Fp(
                    fp.unconstrained(&conv_ty(&ty), None)
                        .map_err(|e| crate::GAError::SolverError(SolverError::Generic(format!("{e:?}"))))
                        .context("fp any")?,
                ),
                ty,
            }),
            FpOrBv::Bv(bv) => Ok(Self {
                ctx: FpOrBv::Fp(
                    FP::new(bv.get_btor(), conv_ty(&ty), None)
                        .map_err(|e| crate::GAError::SolverError(SolverError::Generic(format!("{e:?}"))))
                        .context("fp any from bv")?,
                ),
                ty,
            }),
        }
    }

    fn get_const(&self) -> Option<f64> {
        None
    }

    fn ty(&self) -> OperandType {
        self.ty.clone()
    }

    fn add(&self, other: &Self, rounding_mode: RoundingMode) -> crate::Result<Self> {
        if other.ty != self.ty {
            return Err(crate::InternalError::TypeError).context(format!("While adding a {:?} and a {:?}", self.ty, other.ty));
        }
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let other_ctx: &FP<Rc<Bitwuzla>> = (&other.ctx).try_into()?;
        Ok(ctx.add(other_ctx, conv_rm(&rounding_mode)).conv(self.ty.clone()))
    }

    fn sub(&self, other: &Self, rounding_mode: RoundingMode) -> crate::Result<Self> {
        if other.ty != self.ty {
            return Err(crate::InternalError::TypeError).context(format!("While subtracting a {:?} and a {:?}", self.ty, other.ty));
        }
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let other_ctx: &FP<Rc<Bitwuzla>> = (&other.ctx).try_into()?;
        Ok(ctx.sub(other_ctx, conv_rm(&rounding_mode)).conv(self.ty.clone()))
    }

    fn mul(&self, other: &Self, rounding_mode: RoundingMode) -> crate::Result<Self> {
        if other.ty != self.ty {
            return Err(crate::InternalError::TypeError).context(format!("While multiplying a {:?} and a {:?}", self.ty, other.ty));
        }
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let other_ctx: &FP<Rc<Bitwuzla>> = (&other.ctx).try_into()?;
        Ok(ctx.mul(other_ctx, conv_rm(&rounding_mode)).conv(self.ty.clone()))
    }

    fn div(&self, other: &Self, rounding_mode: RoundingMode) -> crate::Result<Self> {
        if other.ty != self.ty {
            return Err(crate::InternalError::TypeError).context(format!("While dividing a {:?} and a {:?}", self.ty, other.ty));
        }
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let other_ctx: &FP<Rc<Bitwuzla>> = (&other.ctx).try_into()?;
        Ok(ctx.div(other_ctx, conv_rm(&rounding_mode)).conv(self.ty.clone()))
    }

    fn remainder(&self, other: &Self, _rm: RoundingMode) -> crate::Result<Self> {
        if other.ty != self.ty {
            return Err(crate::InternalError::TypeError).context(format!("While checking remainder between {:?} and a {:?}", self.ty, other.ty));
        }

        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let other_ctx: &FP<Rc<Bitwuzla>> = (&other.ctx).try_into()?;
        Ok(ctx.rem(other_ctx).conv(self.ty.clone()))
    }

    fn neg(&self, rm: RoundingMode) -> crate::Result<Self> {
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let val = FP::new_from_f64(ctx.btor().clone(), 0., conv_ty(&self.ty)).conv(self.ty.clone());
        self.sub(&val, rm)
    }

    fn abs(&self, _rm: RoundingMode) -> crate::Result<Self> {
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        Ok(ctx.abs().conv(self.ty()))
    }

    fn sqrt(&self, rm: RoundingMode) -> crate::Result<Self> {
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        Ok(ctx.sqrt(conv_rm(&rm)).conv(self.ty()))
    }

    fn to_bv(&self, rm: RoundingMode, signed: bool) -> crate::Result<Self::Expression> {
        println!("Casting to BV");
        match &self.ctx {
            FpOrBv::Bv(bv) => Ok(super::expr::BitwuzlaExpr(bv.clone())),
            FpOrBv::Fp(fp) => {
                match self.ty() {
                    OperandType::Integral { size, signed } if signed => {
                        let tm = fp.to_sbv(conv_rm(&rm), size as u64);
                        return Ok(BitwuzlaExpr(tm));
                    }
                    OperandType::Integral { size, signed } => {
                        let tm = fp.to_ubv(conv_rm(&rm), size as u64);
                        return Ok(BitwuzlaExpr(tm));
                    }
                    _ => {}
                }
                let e = BitwuzlaExpr(BV::new(fp.btor().clone(), self.ty.size().into(), None));

                println!("Getting BV repr");
                let fp2 = Self {
                    ctx: FpOrBv::Fp(FP::from_ieee754_bv(&e.0, &conv_ty(&self.ty()))),
                    ty: self.ty(),
                };
                // let fp2 = e.to_fp(self.ty(), rm.clone(), signed)?;
                Bitwuzla::assert(fp2._compare(&self, ComparisonMode::Equal, rm).expect("Valid comparison"));
                Ok(e)
            } //super::expr::BitwuzlaExpr(fp.to_ieee754_bv())),
        }
    }

    fn compare(&self, other: &Self, cmp: general_assembly::extension::ieee754::ComparisonMode, _rm: RoundingMode) -> crate::Result<Self::Expression> {
        if other.ty != self.ty {
            return Err(crate::InternalError::TypeError).context(format!("While comparing a {:?} and a {:?}", self.ty, other.ty));
        }

        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let other_ctx: &FP<Rc<Bitwuzla>> = (&other.ctx).try_into()?;
        Ok(super::BitwuzlaExpr(
            match cmp {
                ComparisonMode::Less => ctx.lt(other_ctx),
                ComparisonMode::NotLess => ctx.lt(other_ctx).not(),
                ComparisonMode::Greater => ctx.gt(other_ctx),
                ComparisonMode::NotGreater => ctx.gt(other_ctx).not(),
                ComparisonMode::Equal => ctx._eq(other_ctx),
                ComparisonMode::NotEqual => ctx._eq(other_ctx).not(),
                ComparisonMode::GreaterOrEqual => ctx.geq(other_ctx),
                ComparisonMode::LessOrEqual => ctx.leq(other_ctx),
                ComparisonMode::GreaterUnordered => unimplemented!("Bitwuzla has no support for this."),
                ComparisonMode::LessUnordered => unimplemented!("Bitwuzla has no support for this."),
            }
            .to_bv(),
        ))
    }

    fn check_meta(&self, op: general_assembly::extension::ieee754::NonComputational, _rm: RoundingMode) -> crate::Result<Self::Expression> {
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        let ret = super::BitwuzlaExpr(
            match op {
                NonComputational::IsNan => ctx.is_nan(), //bitwuzla::Bool::<Rc<Bitwuzla>>::new(ctx.btor().clone(), None), //ctx.is_nan(),
                NonComputational::IsZero => ctx.is_zero(),
                NonComputational::IsNormal => ctx.is_normal(),
                NonComputational::IsSubNormal => ctx.is_subnormal(),
                NonComputational::IsInfinite => ctx.is_infinite(),
                NonComputational::IsFinite => ctx.is_infinite().not(),
                NonComputational::IsSignMinus => ctx.is_neg(),
                NonComputational::IsCanonical => unimplemented!("Bitwuzla has no support for this"),
            }
            .to_bv(),
        );
        Ok(ret)
    }

    fn round_to_integral(&self, rm: RoundingMode) -> crate::Result<Self> {
        let ctx: &FP<Rc<Bitwuzla>> = (&self.ctx).try_into()?;
        Ok(Self {
            ctx: FpOrBv::Fp(ctx.round_to_integral(conv_rm(&rm))),
            ty: OperandType::Integral {
                size: self.ty.size(),
                signed: true,
            },
        })
    }

    fn convert_from_bv(bv: Self::Expression, rm: RoundingMode, source_ty: OperandType, dest_ty: OperandType, signed: bool) -> crate::Result<Self> {
        match source_ty {
            OperandType::Binary16 => {
                return Ok(Self {
                    ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
                    ty: dest_ty,
                })
            }

            OperandType::Binary32 => {
                return Ok(Self {
                    ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
                    ty: dest_ty,
                })
            }
            OperandType::Binary64 => {
                return Ok(Self {
                    ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
                    ty: dest_ty,
                })
            }
            OperandType::Binary128 => {
                return Ok(Self {
                    ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
                    ty: dest_ty,
                })
            }
            _ => {}
        }

        let ctx = match signed {
            true => FP::from_sbv(bv.0, conv_rm(&rm), &conv_ty(&dest_ty)),
            false => FP::from_ubv(bv.0, conv_rm(&rm), &conv_ty(&dest_ty)),
        };

        Ok(Self {
            ctx: FpOrBv::Fp(ctx),
            ty: dest_ty,
        })
    }
}

impl<R: Clone + Borrow<bitwuzla::Bitwuzla> + std::fmt::Debug> Borrow<FP<R>> for FpOrBv<R> {
    fn borrow(&self) -> &FP<R> {
        match self {
            Self::Fp(fp) => fp,
            _ => panic!("Tried to use a bitvector as a floating pint value"),
        }
    }
}

impl<'a, R: Clone + Borrow<bitwuzla::Bitwuzla> + std::fmt::Debug> TryInto<&'a FP<R>> for &'a FpOrBv<R> {
    type Error = crate::GAError;

    fn try_into(self) -> Result<&'a FP<R>, Self::Error> {
        match self {
            FpOrBv::Fp(fp) => Ok(fp),
            FpOrBv::Bv(_bv) => Err(crate::GAError::InternalError(InternalError::TypeError)),
        }
    }
}

trait Conv {
    fn conv(self, ty: OperandType) -> FpExpr;
}
impl Conv for FP<Rc<Btor>> {
    fn conv(self, ty: OperandType) -> FpExpr {
        FpExpr { ctx: FpOrBv::Fp(self), ty }
    }
}
