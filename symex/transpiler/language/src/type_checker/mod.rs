//! Provides type checking utilities for IR.

use proc_macro2::Span;
use syn::spanned::Spanned;

use crate::{
    ast::{
        function::{
            self,
            Abs,
            Cast,
            Function,
            Intrinsic,
            IsFinite,
            IsNaN,
            IsNormal,
            Jump,
            LocalAddress,
            Log,
            MultiplyAndAccumulate,
            Register,
            Resize,
            Rotation,
            SetCFlag,
            SetCFlagRot,
            SetNFlag,
            SetVFlag,
            SetZFlag,
            SignExtend,
            Sqrt,
            ZeroExtend,
        },
        operand::{
            DynamicFieldExtract,
            ExprOperand,
            FieldExtract,
            IdentOperand,
            Operand,
            SetType,
            Type,
            WrappedLiteral,
        },
        operations::{Assign, BinOp, BinaryOperation, CompareOperation, UnOp, UnaryOperation},
        IRExpr,
        Statement,
        IR,
    },
    TypeCheck,
    TypeCheckMeta,
    TypeError,
};

impl TypeCheckMeta {
    fn get_ty(&self, id: &syn::Ident) -> Option<crate::ast::operand::Type> {
        self.lookup.get(id).cloned()
    }

    fn set_ty(&mut self, id: syn::Ident, ty: crate::ast::operand::Type) {
        self.lookup.insert(id, ty);
    }

    fn register(&self) -> crate::ast::operand::Type {
        // TODO: replace this with a setable word size.
        Type::U(32)
    }

    fn set_type(&mut self, operand: &mut Operand, ty: &Type) {
        match operand {
            Operand::Ident((i, inner_ty)) => {
                *inner_ty = Some(*ty);
                self.set_ty(i.ident.clone(), *ty)
            }
            Operand::Expr((ExprOperand::Ident(i), inner_ty)) => {
                self.set_ty(i.clone(), *ty);
                *inner_ty = Some(*ty)
            }
            Operand::Expr((_, inner_ty)) => *inner_ty = Some(*ty),
            Operand::FieldExtract((_, inner_ty)) => *inner_ty = Some(*ty),
            Operand::DynamicFieldExtract((_, inner_ty)) => *inner_ty = Some(*ty),
            Operand::WrappedLiteral(_) => {}
        }
    }
}

impl TypeCheck for Statement {
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError> {
        match self {
            Statement::If(_i, t, Some(e)) => {
                let mut inner_meta = meta.clone();
                for stmt in t.iter_mut() {
                    stmt.type_check(&mut inner_meta)?;
                }
                let mut inner_meta = meta.clone();
                for stmt in e.iter_mut() {
                    stmt.type_check(&mut inner_meta)?;
                }
            }
            Statement::If(_i, t, None) => {
                let mut inner_meta = meta.clone();
                for stmt in t.iter_mut() {
                    stmt.type_check(&mut inner_meta)?;
                }
            }
            Self::For(_var, _cond, body) => {
                let mut inner_meta = meta.clone();
                for stmt in body.iter_mut() {
                    stmt.type_check(&mut inner_meta)?;
                }
            }
            Self::Exprs(e) => {
                for e in e.iter_mut() {
                    e.type_check(meta)?;
                }
            }
        }
        Ok(None)
    }
}
impl TypeCheck for IR {
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError> {
        let IR { ret: _, extensions } = self;
        for ext in extensions.iter_mut() {
            ext.type_check(meta)?;
        }
        Ok(None)
    }
}

impl Operand {
    fn span(&self) -> Span {
        match self {
            Self::Expr((e, _ty)) => e.span(),
            Self::Ident((i, _)) => i.span(),
            Self::FieldExtract((f, _)) => f.span(),
            Self::DynamicFieldExtract((f, _)) => f.span(),
            Self::WrappedLiteral(WrappedLiteral { val, ty: _ }) => val.span(),
        }
    }
}

impl FieldExtract {
    fn span(&self) -> Span {
        let FieldExtract {
            operand,
            start: _,
            end: _,
            ty: _,
        } = self;
        operand.span()
    }
}

impl DynamicFieldExtract {
    fn span(&self) -> Span {
        let DynamicFieldExtract {
            operand,
            start: _,
            end: _,
            ty: _,
        } = self;
        operand.span()
    }
}
impl IdentOperand {
    fn span(&self) -> Span {
        let Self { define: _, ident } = self;
        ident.span()
    }
}
impl ExprOperand {
    fn span(&self) -> Span {
        match self {
            ExprOperand::Paren(p) => p.span(),
            ExprOperand::Chain(i, c) => {
                let mut span = i.span();
                for el in c {
                    span = span
                        .join(el.0.span())
                        .expect("Multi file is not supported.");
                    for el in &el.1 {
                        span = span.join(el.span()).expect("Multi file is not supported.");
                    }
                }
                span
            }
            ExprOperand::Ident(i) => i.span(),
            ExprOperand::Literal(l) => l.span(),
            ExprOperand::FunctionCall(Function::Ident(i, _)) => i.span(),
            ExprOperand::FunctionCall(Function::Intrinsic(i)) => i.span(),
        }
    }
}
impl Intrinsic {
    fn span(&self) -> Span {
        Span::call_site()
    }
}

impl TypeCheck for IRExpr {
    fn type_check(
        &mut self,
        meta: &mut crate::TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, crate::TypeError> {
        match self {
            Self::UnOp(UnOp {
                dest,
                op,
                rhs,
                result_ty,
            }) => {
                let rhs_ty = rhs.type_check(meta)?;
                let mut dest_ty = dest.type_check(meta)?;
                if let Some(rty) = result_ty {
                    if let Some(dty) = dest_ty {
                        if dty != *rty {
                            return Err(TypeError::InvalidType {
                                expected: dty,
                                got: *rty,
                                span: rhs.span(),
                            });
                        }
                    } else {
                        dest_ty = Some(*rty);
                        meta.set_type(dest, rty);
                    }
                }
                let output_ty = match op {
                    UnaryOperation::BitwiseNot => {
                        if let Some(ty) = rhs_ty {
                            match ty {
                                Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                                    return Err(TypeError::UnsuportedOperation(
                                        "Cannot compute bitwise not on floating point values."
                                            .to_string(),
                                        rhs.span(),
                                    ))
                                }
                                _ => {}
                            }
                            ty
                        } else if let Some(dest) = dest_ty {
                            match dest {
                                Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                                    return Err(TypeError::UnsuportedOperation(
                                        "Cannot compute bitwise not on floating point values."
                                            .to_string(),
                                        rhs.span(),
                                    ))
                                }
                                _ => {}
                            }
                            meta.set_type(rhs, &dest);
                            dest
                        } else {
                            return Err(TypeError::TypeMustBeKnown(
                                "Cannot compute bitwise not without knowing the type.".to_string(),
                                rhs.span(),
                            ));
                        }
                    }
                };
                if let Some(dest) = dest_ty {
                    if dest != output_ty {
                        return Err(TypeError::InvalidType {
                            expected: dest,
                            got: output_ty,
                            span: rhs.span(),
                        });
                    }
                } else {
                    meta.set_type(dest, &output_ty);
                }
                Ok(Some(output_ty))
            }
            Self::Jump(Jump {
                target: target_id,
                condition: _,
            }) => {
                let target = target_id.type_check(meta)?;
                let ty = match target {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot branch to an address with unknown type.".to_string(),
                            target_id.span(),
                        ))
                    }
                };
                match ty {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot branch to a floating point address.".to_string(),
                            target_id.span(),
                        ))
                    }
                    Type::U(_) | Type::I(_) => Ok(None),
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
                // condition is encoded as a rust expressions.
            }
            Self::BinOp(binop) => {
                let BinOp {
                    dest,
                    op,
                    lhs: lhs_operand,
                    rhs: rhs_operand,
                    result_ty,
                } = &mut **binop;
                let lhs = lhs_operand.type_check(meta)?;

                let rhs = rhs_operand.type_check(meta)?;

                let mut dest_ty = dest.type_check(meta)?;
                if let Some(ty) = result_ty {
                    if let Some(ty2) = dest_ty {
                        if ty2 != *ty {
                            return Err(TypeError::InvalidType {
                                expected: ty2,
                                got: *ty,
                                span: {
                                    let mut span = lhs_operand.span();
                                    span = span
                                        .join(rhs_operand.span())
                                        .expect("Multi file is not supported");
                                    span
                                },
                            });
                        }
                    } else {
                        meta.set_type(dest, ty);
                        dest_ty = Some(*ty);
                    }
                }

                let (lhs, rhs) = match (dest_ty, lhs, rhs) {
                    (Some(_), Some(lhs), Some(rhs)) => (lhs, rhs),
                    (Some(ty), Some(lhs), None) if ty == lhs => (ty, ty),
                    (Some(ty), Some(lhs), None) => {
                        return Err(TypeError::InvalidType {
                            expected: ty,
                            got: lhs,
                            span: {
                                let mut span = dest.span();
                                span = span
                                    .join(lhs_operand.span())
                                    .expect("Multi file is not supported");
                                span = span
                                    .join(rhs_operand.span())
                                    .expect("Multi file is not supported");
                                span
                            },
                        })
                    }
                    (Some(ty), None, Some(rhs)) if ty == rhs => (ty, ty),
                    (Some(ty), None, Some(rhs)) => {
                        return Err(TypeError::InvalidType {
                            expected: ty,
                            got: rhs,
                            span: {
                                let mut span = dest.span();
                                span = span
                                    .join(lhs_operand.span())
                                    .expect("Multi file is not supported");
                                span = span
                                    .join(rhs_operand.span())
                                    .expect("Multi file is not supported");
                                span
                            },
                        })
                    }
                    (Some(ty), None, None) => (ty, ty),
                    (None, Some(lhs), None) => {
                        // TODO: Is this reasonable?
                        (lhs, lhs)
                    }
                    (None, None, Some(rhs)) => {
                        // TODO: Is this reasonable?
                        (rhs, rhs)
                    }
                    (None, Some(lhs), Some(rhs)) if lhs == rhs => (lhs, rhs),
                    (None, Some(lhs), Some(rhs)) if !op.is_shift() => {
                        return Err(TypeError::UnsuportedOperation(
                            format!("Cannot perform {lhs:?} {op:?} {rhs:?}"),
                            {
                                let mut span = dest.span();
                                span = span
                                    .join(lhs_operand.span())
                                    .expect("Multi file is not supported");
                                span = span
                                    .join(rhs_operand.span())
                                    .expect("Multi file is not supported");
                                span
                            },
                        ))
                    }
                    (None, Some(lhs), Some(rhs)) => (lhs, rhs),
                    (None, None, None) => {
                        let dest = dest.clone();
                        let lhs_operand = lhs_operand.clone();
                        let rhs_operand = rhs_operand.clone();
                        return Err(TypeError::TypeMustBeKnown(
                            format!("Cannot inffer type of {self:?}"),
                            {
                                let mut span = dest.span();
                                span = span
                                    .join(lhs_operand.span())
                                    .expect("Multi file is not supported");
                                span = span
                                    .join(rhs_operand.span())
                                    .expect("Multi file is not supported");
                                span
                            },
                        ));
                    }
                };
                meta.set_type(rhs_operand, &rhs);
                meta.set_type(lhs_operand, &lhs);
                rhs_operand.set_type(rhs);
                lhs_operand.set_type(lhs);

                if lhs != rhs && !op.is_shift() {
                    return Err(TypeError::UnsuportedOperation(
                        format!("Cannot apply binary operation to operands of differing types. {lhs:?} != {rhs:?}"),
                                {
                                    let mut span = lhs_operand.span();
                                    span = span
                                        .join(rhs_operand.span())
                                        .expect("Multi file is not supported");
                                    span
                                },

                    ));
                }

                let result_ty = match (&op, lhs) {
                    (BinaryOperation::Sub, _) => lhs,
                    (BinaryOperation::Add, _) => lhs,
                    (BinaryOperation::Mul, _) => lhs,
                    (BinaryOperation::Div, _) => lhs,
                    (BinaryOperation::SSub, Type::I(_) | Type::U(_)) => lhs,
                    (BinaryOperation::SAdd, Type::I(_) | Type::U(_)) => lhs,
                    (BinaryOperation::BitwiseOr, Type::U(_) | Type::I(_)) => lhs,
                    (BinaryOperation::BitwiseAnd, Type::U(_) | Type::I(_)) => lhs,
                    (BinaryOperation::BitwiseXor, Type::U(_) | Type::I(_)) => lhs,
                    (BinaryOperation::AddWithCarry, Type::U(_) | Type::I(_)) => lhs,
                    (BinaryOperation::LogicalLeftShift, Type::U(_size) | Type::I(_size))
                    | (BinaryOperation::LogicalRightShift, Type::U(_size) | Type::I(_size))
                    | (BinaryOperation::ArithmeticRightShift, Type::U(_size) | Type::I(_size)) => {
                         match rhs {
                            Type::F16 | Type::F32 | Type::F64 | Type::F128 => return Err(TypeError::UnsuportedOperation(
                            "Cannot shift using a floating point variable as the shifting amount.".to_string(),rhs_operand.span()
                            )),

                            #[allow(unused)]
                            Type::I(size2) | Type::U(size2) if size2 != 0 => {
                                lhs
                            },
                            Type::Unit => return Err(TypeError::UnsuportedOperation(
                        "Cannot shift using unit type as shift amount.".to_string(),rhs_operand.span())),
                            _ => {return Err(TypeError::UnsuportedOperation(
                        "Shift amount must be the same size as the operand".to_string(),lhs_operand.span().join(rhs_operand.span()).expect("Same file")))

                            }
                        }

                    }
                    (BinaryOperation::Compare(_), _) => Type::U(1),
                    _ => {
                        return Err(TypeError::UnsuportedOperation(
                            format!("Cannot apply {op:?} to {lhs:?}",),
                            {
                                let mut span = lhs_operand.span();
                                span = span
                                    .join(rhs_operand.span())
                                    .expect("Multi file is not supported");
                                span
                            },
                        ))
                    }
                };
                if let Some(ty) = dest_ty {
                    if ty != result_ty {
                        return Err(TypeError::InvalidType {
                            expected: ty,
                            got: result_ty,
                            span: {
                                let mut span = dest.span();
                                span = span
                                    .join(lhs_operand.span())
                                    .expect("Multi file is not supported");
                                span = span
                                    .join(rhs_operand.span())
                                    .expect("Multi file is not supported");
                                span
                            },
                        });
                    }
                    Ok(Some(Type::Unit))
                } else {
                    meta.set_type(dest, &result_ty);
                    Ok(None)
                }
            }
            Self::Assign(Assign { dest, rhs }) => {
                let dest_ty = dest.type_check(meta)?;
                let result_ty = match rhs.type_check(meta)? {
                    Some(ty) => ty,
                    None => {
                        if let Some(ty) = dest_ty {
                            meta.set_type(rhs, &ty);
                            ty
                        } else {
                            return Err(TypeError::TypeMustBeKnown(
                                format!("Cannot assign a type of unknown type, while assigning {rhs:?} to {dest:?}"),
                                rhs.span()

                            ));
                        }
                    }
                };
                meta.set_type(rhs, &result_ty);

                if let Some(ty) = dest_ty {
                    match (ty, result_ty) {
                        (t1, t2) if t1 == t2 => Ok(Some(Type::Unit)),
                        _ => Err(TypeError::InvalidType {
                            expected: ty,
                            got: result_ty,
                            span: {
                                let mut span = dest.span();
                                span = span.join(rhs.span()).expect("Multi file not supported.");
                                span
                            },
                        }),
                    }
                } else if dest_ty.is_none() {
                    meta.set_type(dest, &result_ty);
                    Ok(None)
                } else {
                    Ok(dest_ty)
                }
            }
            Self::Function(f) => match f {
                Function::Ident(_, _) => Ok(None),
                Function::Intrinsic(i) => i.type_check(meta),
            },
            Self::SetType(SetType { operand, ty }) => {
                meta.set_ty(operand.clone(), *ty);
                Ok(Some(Type::Unit))
            }
        }
    }
}

impl TypeCheck for Operand {
    fn type_check(
        &mut self,
        meta: &mut crate::TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, crate::TypeError> {
        match self {
            Self::WrappedLiteral(WrappedLiteral { val: _, ty }) => Ok(Some(*ty)),
            Self::Expr((op, ty)) => {
                let op_ty: Option<crate::ast::operand::Type> = op.type_check(meta)?;
                let ret = match (&ty, op_ty) {
                    (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                    (Some(ty), None) => Ok(Some(*ty)),
                    (Some(ty1), Some(ty2)) if *ty1 == ty2 => Ok(Some(*ty1)),
                    (Some(ty1), Some(ty2)) => Err(crate::TypeError::InvalidType {
                        expected: *ty1,
                        got: ty2,
                        span: op.span(),
                    }),
                };
                if let Ok(Some(inner_ty)) = ret {
                    *ty = Some(inner_ty);
                }
                ret
            }
            Self::Ident((id, ty)) => {
                let op_ty = id.type_check(meta)?;
                let ret = match (&ty, op_ty) {
                    (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                    (Some(ty), None) => Ok(Some(*ty)),
                    (Some(ty1), Some(ty2)) if *ty1 == ty2 => Ok(Some(*ty1)),
                    (Some(ty1), Some(ty2)) => Err(crate::TypeError::InvalidType {
                        expected: *ty1,
                        got: ty2,
                        span: id.span(),
                    }),
                };
                if let Ok(Some(inner_ty)) = ret {
                    *ty = Some(inner_ty);
                    meta.set_ty(id.ident.clone(), inner_ty);
                }

                ret
            }
            Self::FieldExtract((op, ty)) => {
                let op_ty = op.type_check(meta)?;
                let ret = match (&ty, op_ty) {
                    (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                    (Some(ty), None) => Ok(Some(*ty)),
                    (Some(ty1), Some(ty2)) if *ty1 == ty2 => Ok(Some(*ty1)),
                    (Some(ty1), Some(ty2)) => Err(crate::TypeError::InvalidType {
                        expected: *ty1,
                        got: ty2,
                        span: op.span(),
                    }),
                };
                if let Ok(Some(inner_ty)) = &ret {
                    inner_ty.can_field_extract()?;
                    *ty = Some(*inner_ty);
                } else if ret.is_ok() {
                    return Err(TypeError::TypeMustBeKnown("Cannot bitfield extract from arbitrary data. You must specify the type before this.".to_owned(),op.span()));
                }

                ret
            }
            Self::DynamicFieldExtract((op, ty)) => {
                let op_ty = op.type_check(meta)?;
                let ret = match (&ty, op_ty) {
                    (None, Some(ty)) => Ok(Some(ty)),
                    (None, None) => Ok(None),
                    (Some(ty), None) => Ok(Some(*ty)),
                    (Some(ty1), Some(ty2)) if *ty1 == ty2 => Ok(Some(*ty1)),
                    (Some(ty1), Some(ty2)) => Err(crate::TypeError::InvalidType {
                        expected: *ty1,
                        got: ty2,
                        span: op.span(),
                    }),
                };
                if let Ok(Some(inner_ty)) = &ret {
                    inner_ty.can_field_extract()?;
                    *ty = Some(*inner_ty);
                } else if ret.is_ok() {
                    return Err(TypeError::TypeMustBeKnown("Cannot bitfield extract from arbitrary data. You must specify the type before this.".to_owned(),op.span()));
                }

                ret
            }
        }
    }
}
impl TypeCheck for DynamicFieldExtract {
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError> {
        let DynamicFieldExtract {
            operand,
            start: _,
            end: _,
            ty: _,
        } = self;

        let ty = match meta.get_ty(operand) {
            Some(ty) => ty,
            None => {
                return Err(TypeError::TypeMustBeKnown(
                    "Cannot dynamically bitfield extract from unknown type".to_string(),
                    self.span(),
                ))
            }
        };

        match ty {
            Type::F128 | Type::F64 | Type::F32 | Type::F16 => Err(TypeError::UnsuportedOperation(
                "Cannot dynamically bitfield extract on a floating point value".to_string(),
                self.span(),
            )),
            Type::I(size) | Type::U(size) => Ok(Some(Type::U(size))),

            Type::Unit => panic!("Cannot use unit types for expressions"),
        }
    }
}
impl TypeCheck for FieldExtract {
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError> {
        let FieldExtract {
            operand,
            start,
            end,
            ty: _,
        } = self;

        let ty = match meta.get_ty(operand) {
            Some(ty) => ty,
            None => {
                return Err(TypeError::TypeMustBeKnown(
                    "Cannot bitfield extract from unknown type".to_string(),
                    self.span(),
                ))
            }
        };
        // TODO: Add in limit checking here.

        if end < start {
            return Err(TypeError::UnsuportedOperation(
                "Fields must be supplied as start:end".to_string(),
                self.span(),
            ));
        }

        match ty {
            Type::F128 | Type::F64 | Type::F32 | Type::F16 => Err(TypeError::UnsuportedOperation(
                "Cannot bitfield extract on a floating point value".to_string(),
                self.span(),
            )),
            Type::I(size) | Type::U(size) if *end < size => Ok(Some(Type::U(*end - *start + 1))),
            Type::I(_size) | Type::U(_size) => Err(TypeError::UnsuportedOperation(
                "Cannot bitfield extract out side of type width".to_string(),
                self.span(),
            )),

            Type::Unit => panic!("Cannot use unit types for expressions"),
        }
    }
}

impl TypeCheck for IdentOperand {
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError> {
        let Self { define: _, ident } = self;
        Ok(meta.get_ty(ident))
    }
}

impl TypeCheck for ExprOperand {
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError> {
        match self {
            Self::Ident(i) => Ok(meta.get_ty(i)),
            // These are typed in the rust type system and need to be explicitly typed in
            Self::Paren(_) => Ok(None),
            Self::Chain(_, _) => Ok(None),
            Self::Literal(l) => match l {
                syn::Lit::Int(i) => {
                    let mut suffix = i.suffix().to_string();
                    let sign = match suffix.clone().chars().next() {
                        Some('i') => {
                            suffix
                                .strip_prefix("i")
                                .expect("Invalid checks")
                                .to_string();
                            true
                        }
                        Some('u') => {
                            suffix = suffix
                                .strip_prefix("u")
                                .expect("Invalid checks")
                                .to_string();
                            false
                        }
                        _ => {
                            return Err(TypeError::UnsupportedType(
                                "Integer literals must be expliticty typed (read 123i32)."
                                    .to_string(),
                                l.span(),
                            ))
                        }
                    };

                    let bits = suffix.parse().map_err(|_| {
                        TypeError::UnsupportedType(
                            "Could not parse bit size.".to_string(),
                            l.span(),
                        )
                    })?;

                    match sign {
                        true => Ok(Some(Type::I(bits))),
                        false => Ok(Some(Type::U(bits))),
                    }
                }
                syn::Lit::Bool(_b) => Ok(Some(Type::U(1))),
                syn::Lit::Float(f) => {
                    let suffix = f.suffix();
                    let size = match suffix.strip_prefix("f") {
                        Some(s) => s.parse().map_err(|_| {
                            TypeError::UnsupportedType(
                                "Could not parse floating point size.".to_string(),
                                f.span(),
                            )
                        })?,
                        None => {
                            return Err(TypeError::UnsupportedType(
                                "Floating point literals must specify size (read 123.0f32)."
                                    .to_string(),
                                f.span(),
                            ))
                        }
                    };

                    match size {
                        16 => Ok(Some(Type::F16)),
                        32 => Ok(Some(Type::F32)),
                        64 => Ok(Some(Type::F64)),
                        128 => Ok(Some(Type::F128)),
                        v => Err(TypeError::UnsupportedType(
                            format!("Invalid floating point size ({v}) must be 16,32,64,128"),
                            self.span(),
                        )),
                    }
                }
                _ => Err(TypeError::UnsupportedType(
                    "Literals need to be bools, integers or floating point values.".to_string(),
                    self.span(),
                )),
            },
            Self::FunctionCall(f) => {
                let inner = match f {
                    crate::ast::function::Function::Ident(_, _) => return Ok(None),
                    crate::ast::function::Function::Intrinsic(inner) => inner,
                };
                inner.type_check(meta)
            }
        }
    }
}
impl TypeCheck for Intrinsic {
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError> {
        match self {
            crate::ast::function::Intrinsic::Ror(ror) => {
                let crate::ast::function::Ror { operand, n: _ } = ror;
                let ty = match operand.type_check(meta)? {
                    Some(val) => val,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot apply ror to an unknown type".to_owned(),
                            operand.span(),
                        ))
                    }
                };

                match ty {
                    Type::I(_) | Type::U(_) => Ok(Some(ty)),
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot apply ror to a floating point value".to_owned(),
                            operand.span(),
                        ))
                    }
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
            }
            Intrinsic::Sra(sra) => {
                let crate::ast::function::Sra { operand, n: _ } = sra;
                let ty = match operand.type_check(meta)? {
                    Some(val) => val,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot apply sra to an unknown type".to_owned(),
                            operand.span(),
                        ))
                    }
                };

                match ty {
                    Type::I(_) | Type::U(_) => Ok(Some(ty)),
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot apply sra to a floating point value".to_owned(),
                            operand.span(),
                        ))
                    }
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
            }
            Intrinsic::Ite(ite) => {
                let function::Ite {
                    lhs,
                    rhs,
                    operation,
                    then,
                    otherwise,
                    comparison_type,
                } = ite;
                let _ty = operation.type_check(lhs, rhs, meta)?;

                let mut inner_meta = meta.clone();
                for el in then {
                    el.type_check(&mut inner_meta)?;
                }
                let mut inner_meta = meta.clone();
                for el in otherwise {
                    el.type_check(&mut inner_meta)?;
                }
                *comparison_type = lhs.type_check(meta)?;
                // Ites are not used for assign statements.
                Ok(None)
            }
            Intrinsic::Flag(_) => Ok(Some(Type::U(1))),
            Intrinsic::Abort(_) => Ok(None),
            Intrinsic::Resize(resize) => {
                let Resize {
                    operand,
                    target_ty,
                    rm: _,
                } = resize;
                let source = operand.type_check(meta)?;
                match source {
                    Some(_) => {}
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Must know type before resizing.".to_string(),
                            operand.span(),
                        ))
                    }
                };

                Ok(Some(*target_ty))
            }
            Intrinsic::SetNFlag(set) => {
                let SetNFlag { operand } = set;
                let ty = operand.type_check(meta)?;

                let ty = match ty {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot set flags for unknown types.".to_string(),
                            operand.span(),
                        ))
                    }
                };
                match ty {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot set n flag for floating point values.".to_string(),
                            operand.span(),
                        ))
                    }
                    // Set N flag should not be used to assign.
                    Type::I(1..) | Type::U(1..) => Ok(None),
                    Type::I(0) | Type::U(0) => Err(TypeError::UnsuportedOperation(
                        "Cannot set n flag for zero sized operands".to_string(),
                        operand.span(),
                    )),
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
            }
            Intrinsic::SetZFlag(set) => {
                let SetZFlag { operand } = set;
                let ty = operand.type_check(meta)?;

                let ty = match ty {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot set flags for unknown types.".to_string(),
                            operand.span(),
                        ))
                    }
                };
                match ty {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot set z flag for floating point values.".to_string(),
                            operand.span(),
                        ))
                    }
                    // Set N flag should not be used to assign.
                    Type::I(1..) | Type::U(1..) => Ok(None),
                    Type::I(0) | Type::U(0) => Err(TypeError::UnsuportedOperation(
                        "Cannot set z flag for zero sized operands".to_string(),
                        operand.span(),
                    )),
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
            }
            Intrinsic::SetVFlag(set) => {
                let SetVFlag {
                    operand1,
                    operand2,
                    sub: _,
                    carry: _,
                } = set;
                let ty1 = operand1.type_check(meta)?;

                let ty1 = match ty1 {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot set flags for unknown types.".to_string(),
                            operand1.span(),
                        ))
                    }
                };
                let ty2 = operand2.type_check(meta)?;

                let ty2 = match ty2 {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot set flags for unknown types.".to_string(),
                            operand2.span(),
                        ))
                    }
                };
                match ty1 {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set v flag for floating point values.".to_string(),
                            operand1.span(),
                        ))
                    }
                    // Set N flag should not be used to assign.
                    Type::I(1..) | Type::U(1..) => {}
                    Type::I(0) | Type::U(0) => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set v flag for zero sized operands".to_string(),
                            operand1.span(),
                        ))
                    }
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                };
                match ty2 {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set v flag for floating point values.".to_string(),
                            operand2.span(),
                        ))
                    }
                    // Set N flag should not be used to assign.
                    Type::I(1..) | Type::U(1..) => {}
                    Type::I(0) | Type::U(0) => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set v flag for zero sized operands".to_string(),
                            operand2.span(),
                        ))
                    }
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
                Ok(None)
            }
            Intrinsic::SetCFlag(set) => {
                let SetCFlag {
                    operand1,
                    operand2,
                    sub: _,
                    carry: _,
                } = set;
                let ty1 = operand1.type_check(meta)?;

                let ty1 = match ty1 {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot set flags for unknown types.".to_string(),
                            operand1.span(),
                        ))
                    }
                };
                let ty2 = operand2.type_check(meta)?;

                let ty2 = match ty2 {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot set flags for unknown types.".to_string(),
                            operand2.span(),
                        ))
                    }
                };
                match ty1 {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set c flag for floating point values.".to_string(),
                            operand1.span(),
                        ))
                    }
                    // Set N flag should not be used to assign.
                    Type::I(1..) | Type::U(1..) => {}
                    Type::I(0) | Type::U(0) => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set c flag for zero sized operands".to_string(),
                            operand1.span(),
                        ))
                    }
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                };
                match ty2 {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set c flag for floating point values.".to_string(),
                            operand2.span(),
                        ))
                    }
                    // Set N flag should not be used to assign.
                    Type::I(1..) | Type::U(1..) => {}
                    Type::I(0) | Type::U(0) => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set c flag for zero sized operands".to_string(),
                            operand2.span(),
                        ))
                    }
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
                Ok(None)
            }
            Intrinsic::Register(register) => {
                let Register {
                    name: _,
                    source_type,
                } = register;
                let ty = source_type.unwrap_or(meta.register());
                Ok(Some(ty))
            }
            Intrinsic::ZeroExtend(zero) => {
                let ZeroExtend { operand, bits } = zero;

                let ty = match operand.type_check(meta)? {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot zero extend an unknown type".to_string(),
                            operand.span(),
                        ))
                    }
                };
                match ty {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot zero extend floating point values.".to_string(),
                            operand.span(),
                        ))
                    }
                    Type::I(n) | Type::U(n) if n > *bits => Err(TypeError::UnsuportedOperation(
                        "Cannot zero extend to a format, did you mean to use resize?".to_string(),
                        operand.span(),
                    )),

                    Type::U(_) => Ok(Some(Type::U(*bits))),
                    Type::I(_) => Ok(Some(Type::I(*bits))),

                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
            }
            Intrinsic::SignExtend(sig) => {
                let SignExtend {
                    operand,
                    sign_bit: _,
                    target_size,
                } = sig;

                let ty = match operand.type_check(meta)? {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot sign extend an unknown type".to_string(),
                            operand.span(),
                        ))
                    }
                };
                match ty {
                    Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot sign extend floating point values.".to_string(),
                            operand.span(),
                        ))
                    }
                    Type::I(n) | Type::U(n) if n > *target_size => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot sign extend to a format, did you mean to use resize?"
                                .to_string(),
                            operand.span(),
                        ))
                    }

                    // Should we considered sign extended unsigned values signed?
                    Type::U(_) | Type::I(_) => Ok(Some(Type::I(*target_size))),
                    Type::Unit => panic!("Cannot use unit types for expressions"),
                }
            }
            Intrinsic::SetCFlagRot(rot) => {
                let SetCFlagRot {
                    operand1,
                    operand2,
                    rotation,
                } = rot;

                let operand2 = match operand2 {
                    Some(val) => val,
                    None => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot set c flag for rotations that have no operand2".to_string(),
                            self.span(),
                        ))
                    }
                };

                rotation.type_check(operand1, operand2, meta)?;
                Ok(None)
            }
            Intrinsic::LocalAddress(a) => {
                let LocalAddress { name, bits } = a;
                let ty = match meta.get_ty(name) {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot use an untyped local as an address.".to_string(),
                            name.span(),
                        ))
                    }
                };
                if let Type::U(_bits) = ty {
                } else {
                    return Err(TypeError::UnsuportedOperation(
                        "Cannot use a non unsigned bit vector as an address.".to_string(),
                        name.span(),
                    ));
                }

                Ok(Some(Type::U(*bits)))
            }
            Intrinsic::Abs(Abs { operand }) => {
                let ty = operand.type_check(meta)?;
                match ty {
                    Some(Type::I(size)) => Ok(Some(Type::U(size))),
                    Some(Type::U(size)) => Ok(Some(Type::U(size))),
                    Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(ty),

                    Some(Type::Unit) => Err(TypeError::UnsuportedOperation(
                        "Cannot compute absolute value of a unit type value.".to_string(),
                        operand.span(),
                    )),
                    None => Err(TypeError::TypeMustBeKnown(
                        "Cannot compute absolute value of an unknown type.".to_string(),
                        operand.span(),
                    )),
                }
            }
            Intrinsic::Sqrt(Sqrt { operand }) => {
                let ty = operand.type_check(meta)?;
                match ty {
                    Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(ty),
                    Some(ty) => Err(TypeError::UnsuportedOperation(
                        format!("Cannot compute sqrt for type {ty:?}"),
                        operand.span(),
                    )),
                    None => Err(TypeError::TypeMustBeKnown(
                        "Cannot compute sqrt without knowing the type.".to_string(),
                        operand.span(),
                    )),
                }
            }
            Intrinsic::Cast(Cast {
                operand,
                target_type,
            }) => {
                let ty = match operand.type_check(meta)? {
                    Some(ty) => ty,
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot cast a value of unknown type.".to_string(),
                            operand.span(),
                        ))
                    }
                };

                match (ty, &target_type) {
                    (Type::U(_), Type::F16 | Type::F32 | Type::F64 | Type::F128) => {
                        Ok(Some(*target_type))
                    }
                    (Type::I(_), Type::F16 | Type::F32 | Type::F64 | Type::F128) => {
                        Ok(Some(*target_type))
                    }
                    (Type::F16, Type::U(16))
                    | (Type::F32, Type::U(32))
                    | (Type::F64, Type::U(64))
                    | (Type::F128, Type::U(128)) => Ok(Some(*target_type)),
                    (Type::F16, Type::I(16))
                    | (Type::F32, Type::I(32))
                    | (Type::F64, Type::I(64))
                    | (Type::F128, Type::I(128)) => Ok(Some(*target_type)),
                    _ => Err(TypeError::UnsuportedOperation(
                        format!("Cannot cast {ty:?} to {target_type:?}"),
                        operand.span(),
                    )),
                }
            }
            Intrinsic::IsNaN(IsNaN { operand }) => match operand.type_check(meta)? {
                Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(Some(Type::U(1))),
                None => Err(TypeError::TypeMustBeKnown(
                    "Cannot compute is nan for untyped variables.".to_string(),
                    operand.span(),
                )),
                Some(Type::U(_) | Type::I(_) | Type::Unit) => Err(TypeError::UnsuportedOperation(
                    "Cannot compute isNaN for non floating point values".to_string(),
                    operand.span(),
                )),
            },
            Intrinsic::MultiplyAndAccumulate(MultiplyAndAccumulate { lhs, rhs, addend }) => {
                let ty = lhs.type_check(meta)?;
                let lhs_ty = match ty {
                    Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => {
                        ty.expect("Previous checks to work")
                    }
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot fma for untyped variables.".to_string(),
                            lhs.span(),
                        ))
                    }
                    Some(Type::U(_) | Type::I(_) | Type::Unit) => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot compute fma for non floating point values".to_string(),
                            lhs.span(),
                        ))
                    }
                };

                let ty = rhs.type_check(meta)?;
                let rhs_ty = match ty {
                    Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => {
                        ty.expect("Previous checks to work")
                    }
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot fma for untyped variables.".to_string(),
                            rhs.span(),
                        ))
                    }
                    Some(Type::U(_) | Type::I(_) | Type::Unit) => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot compute fma for non floating point values".to_string(),
                            rhs.span(),
                        ))
                    }
                };

                let ty = addend.type_check(meta)?;
                let addend_ty = match ty {
                    Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => {
                        ty.expect("Previous checks to work")
                    }
                    None => {
                        return Err(TypeError::TypeMustBeKnown(
                            "Cannot fma for untyped variables.".to_string(),
                            addend.span(),
                        ))
                    }
                    Some(Type::U(_) | Type::I(_) | Type::Unit) => {
                        return Err(TypeError::UnsuportedOperation(
                            "Cannot compute fma for non floating point values".to_string(),
                            addend.span(),
                        ))
                    }
                };

                if rhs_ty != lhs_ty {
                    return Err(TypeError::UnsuportedOperation(
                        format!("Cannot multiply {lhs_ty} and  {rhs_ty}"),
                        lhs.span().join(rhs.span()).expect("Same file"),
                    ));
                }
                if addend_ty != lhs_ty {
                    return Err(TypeError::UnsuportedOperation(
                        format!("Cannot add {lhs_ty} and  {addend_ty}"),
                        lhs.span()
                            .join(rhs.span())
                            .expect("Same file")
                            .join(addend.span())
                            .expect("Same file"),
                    ));
                }

                Ok(Some(lhs_ty))
            }
            Intrinsic::IsNormal(IsNormal { operand }) => match operand.type_check(meta)? {
                Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(Some(Type::U(1))),
                None => Err(TypeError::TypeMustBeKnown(
                    "Cannot compute is normal for untyped variables.".to_string(),
                    operand.span(),
                )),
                Some(Type::U(_) | Type::I(_) | Type::Unit) => Err(TypeError::UnsuportedOperation(
                    "Cannot compute is normal for non floating point values".to_string(),
                    operand.span(),
                )),
            },
            Intrinsic::IsFinite(IsFinite { operand }) => match operand.type_check(meta)? {
                Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(Some(Type::U(1))),
                None => Err(TypeError::TypeMustBeKnown(
                    "Cannot compute is finite for untyped variables.".to_string(),
                    operand.span(),
                )),
                Some(Type::U(_) | Type::I(_) | Type::Unit) => Err(TypeError::UnsuportedOperation(
                    "Cannot compute is finite for non floating point values".to_string(),
                    operand.span(),
                )),
            },
            Intrinsic::Log(Log {
                level: _,
                operand,
                meta: _,
                call_site: _,
            }) => {
                let ty = operand.type_check(meta)?;
                match ty {
                    Some(Type::I(_) | Type::U(_)) => Ok(Some(Type::Unit)),
                    Some(Type::F16 | Type::F32 | Type::F64 | Type::F128) => {
                        Err(TypeError::UnsuportedOperation(
                            "Cannot log floating point values yet.".to_string(),
                            operand.span(),
                        ))
                    }
                    Some(Type::Unit) => Err(TypeError::UnsuportedOperation(
                        "Cannot log unit type values.".to_string(),
                        operand.span(),
                    )),
                    None => Err(TypeError::UnsuportedOperation(
                        "Must know type of operand before logging.".to_string(),
                        operand.span(),
                    )),
                }
            }
        }
    }
}

impl Rotation {
    fn type_check(
        &self,
        lhs: &mut Operand,
        rhs: &mut Operand,
        meta: &mut TypeCheckMeta,
    ) -> Result<Type, TypeError> {
        let lhs_ty = match lhs.type_check(meta)? {
            Some(lhs) => lhs,
            None => {
                return Err(TypeError::TypeMustBeKnown(
                    "Cannot apply a rotation to a value of unknown type".to_string(),
                    lhs.span(),
                ))
            }
        };
        let rhs_ty = match rhs.type_check(meta)? {
            Some(rhs) => rhs,
            None => {
                return Err(TypeError::TypeMustBeKnown(
                    "Cannot use a value as a rotation distance if its type is not known."
                        .to_string(),
                    rhs.span(),
                ))
            }
        };

        match rhs_ty {
            Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                return Err(TypeError::UnsuportedOperation(
                    "Cannot use a floating point value as a rotation distance.".to_string(),
                    rhs.span(),
                ))
            }
            Type::U(_) | Type::I(_) => {}
            Type::Unit => panic!("Cannot use unit types for expressions"),
        }

        match lhs_ty {
            Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                return Err(TypeError::UnsuportedOperation(
                    "Cannot apply a rotation to a floating point value".to_string(),
                    lhs.span(),
                ))
            }
            Type::U(_) | Type::I(_) => {}
            Type::Unit => panic!("Cannot use unit types for expressions"),
        }

        Ok(Type::U(1))
    }
}

impl CompareOperation {
    fn type_check(
        &self,
        lhs: &mut Operand,
        rhs: &mut Operand,
        meta: &mut TypeCheckMeta,
    ) -> Result<Type, TypeError> {
        let lhs_ty = match lhs.type_check(meta)? {
            Some(value) => value,
            None => {
                return Err(TypeError::TypeMustBeKnown(
                    "Cannot compare unknown types".to_string(),
                    lhs.span(),
                ));
            }
        };
        let rhs_ty = match rhs.type_check(meta)? {
            Some(value) => value,
            None => {
                return Err(TypeError::TypeMustBeKnown(
                    "Cannot compare unknown types".to_string(),
                    rhs.span(),
                ));
            }
        };
        if lhs_ty != rhs_ty {
            return Err(TypeError::UnsuportedOperation(
                "Cannot compare different types.".to_string(),
                {
                    let mut span = lhs.span();
                    span = span.join(rhs.span()).expect("Multi file not supported.");
                    span
                },
            ));
        }

        Ok(Type::U(1))
    }
}

impl crate::ast::operand::Type {
    fn can_field_extract(&self) -> Result<(), TypeError> {
        match self {
            Self::F16 | Self::F32 | Self::F64 | Self::F128 => Err(TypeError::UnsuportedOperation("Cannot bit field extract on floating point values. Please convert to a bitvector first.".to_owned(),Span::call_site())),
            Self::I(_) => Ok(()),
            Self::U(_) => Ok(()),
            Type::Unit => panic!("Cannot use unit types for expressions"),
        }
    }
}
