//! Defines transpiling rules for the ast
//! [`Functions`](crate::ast::function::Function).

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};

use crate::{
    ast::{function::*, operand::Type},
    Compile,
    Error,
    TranspilerState,
};

impl Compile for (Function, Type) {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        Ok(match &self.0 {
            // This should not be managed by us
            Function::Ident(i, args) => {
                quote! {#i(#(#args),*)}
            }
            Function::Intrinsic(i) => (*(*i).clone(), self.1).compile(state)?,
        })
    }
}

impl Compile for (Intrinsic, Type) {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        match &self.0 {
            Intrinsic::ZeroExtend(z) => z.compile(state),
            Intrinsic::SignExtend(s) => s.compile(state),
            Intrinsic::Resize(r) => r.compile(state),
            Intrinsic::SetNFlag(n) => n.compile(state),
            Intrinsic::SetZFlag(z) => z.compile(state),
            Intrinsic::LocalAddress(a) => a.compile(state),
            Intrinsic::SetVFlag(f) => f.compile(state),
            Intrinsic::SetCFlag(f) => f.compile(state),
            Intrinsic::SetCFlagRot(f) => f.compile(state),
            Intrinsic::Flag(f) => f.compile(state),
            Intrinsic::Register(r) => (r.clone(), self.1).compile(state),
            Intrinsic::Ror(r) => r.compile(state),
            Intrinsic::Sra(s) => s.compile(state),
            Intrinsic::Ite(i) => i.compile(state),
            Intrinsic::Abort(a) => a.compile(state),
            Intrinsic::Abs(a) => a.compile(state),
            Intrinsic::Sqrt(s) => s.compile(state),
            Intrinsic::Cast(c) => c.compile(state),
            Intrinsic::IsNaN(i) => i.compile(state),
            Intrinsic::IsNormal(i) => i.compile(state),
            Intrinsic::IsFinite(i) => i.compile(state),
            Intrinsic::Log(l) => l.compile(state),
            Intrinsic::MultiplyAndAccumulate(m) => m.compile(state),
            // Intrinsic::Saturate(s) => s.compile(state),
        }
    }
}

impl Compile for (FunctionCall, Type) {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        let f: TokenStream = (self.0.ident.clone(), self.1).compile(state)?;
        let args = self.0.args.clone();

        Ok(quote! {
            #f(#(#args),*)
        })
    }
}
//
//impl Compile for Signed {
//    type Output = TokenStream;
//
//    fn compile(&self, state: &mut TranspilerState<Self::Output>) ->
// Result<Self::Output, Error> {        let lhs = self.op1.clone();
//        let rhs = self.op2.clone();
//        let mut op = self.operation.clone();
//        op.signed();
//        let dst = state.intermediate();
//        let operation = BinOp {
//            lhs,
//            rhs,
//            dest: Operand::Ident(dst.clone()),
//            op,
//        }
//        .compile(state)?;
//        state.to_insert_above.push(operation);
//        let dst = dst.compile(state)?;
//        Ok(quote!(
//        #dst
//        ))
//    }
//}

impl Compile for LocalAddress {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let name = self.name.clone();
        let mut name_stripped = name.clone().into_token_stream().to_string();
        name_stripped = name_stripped
            .strip_prefix('\"')
            .unwrap_or(name_stripped.as_str())
            .to_string();
        name_stripped = name_stripped
            .strip_suffix('\"')
            .unwrap_or(name_stripped.as_str())
            .to_string();

        state.access_str(name_stripped.clone());
        let bits = self.bits;

        let span = self.name.span();
        let inner = quote_spanned! {span => AddressInLocal(#name_stripped.to_owned(),#bits)};
        Ok(
            quote!(general_assembly::operand::Operand::#inner),
        )
    }
}

impl Compile for (Register, crate::ast::operand::Type) {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let name = self.0.name.clone();
        let mut name_stripped = name.clone().into_token_stream().to_string();
        name_stripped = name_stripped
            .strip_prefix('\"')
            .unwrap_or(name_stripped.as_str())
            .to_string();
        name_stripped = name_stripped
            .strip_suffix('\"')
            .unwrap_or(name_stripped.as_str())
            .to_string();

        state.access_str(name_stripped);
        let fp = self.1.fp_name();
        match (self.0.source_type, self.1) {
            (None, Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(quote! {
                general_assembly::extension::ieee754::OperandStorage::Register {
                    id: #name.to_string(),
                    ty: #fp,
                }
            }),
            (Some(Type::U(_size)), Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(quote! {
                general_assembly::extension::ieee754::OperandStorage::CoreRegister {
                    id: #name.to_string(),
                    ty: #fp,
                    signed: false,
                }
            }),
            (Some(Type::I(_size)), Type::F16 | Type::F32 | Type::F64 | Type::F128) => Ok(quote! {
                general_assembly::extension::ieee754::OperandStorage::CoreRegister {
                    id: #name.to_string(),
                    ty: #fp,
                    signed: true,
                }
            }),
            (
                Some(Type::F16 | Type::F32 | Type::F64 | Type::F128),
                Type::F16 | Type::F32 | Type::F64 | Type::F128,
            ) => Ok(quote! {
                general_assembly::extension::ieee754::OperandStorage::CoreRegister {
                    id: #name.to_string(),
                    ty: #fp,
                    signed: true,
                }
            }),
            _ => Ok(quote!(general_assembly::operand::Operand::Register(#name.to_owned()))),
        }
    }
}

impl Compile for Flag {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let name = self.name.clone();
        let mut name_stripped = name.clone().into_token_stream().to_string();
        name_stripped = name_stripped
            .strip_prefix('\"')
            .unwrap_or(name_stripped.as_str())
            .to_string();
        name_stripped = name_stripped
            .strip_suffix('\"')
            .unwrap_or(name_stripped.as_str())
            .to_string();

        state.access_str(name_stripped);
        Ok(quote!(general_assembly::operand::Operand::Flag(#name.to_owned())))
    }
}

impl Compile for Jump {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let operand = self.target.clone().compile(state)?;
        Ok(match self.condition.clone() {
            Some(condition) => {
                quote!(general_assembly::operation::Operation::ConditionalJump { destination: #operand, condition:#condition.clone() })
            }
            None => {
                quote!(general_assembly::operation::Operation::ConditionalJump { destination: #operand, condition:general_assembly::condition::Condition::None })
            }
        })
    }
}

impl Compile for SetNFlag {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let operand = self.operand.compile(state)?;
        Ok(quote!(general_assembly::operation::Operation::SetNFlag( #operand )))
    }
}

impl Compile for SetZFlag {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let operand = self.operand.compile(state)?;
        Ok(quote!(general_assembly::operation::Operation::SetZFlag (#operand)))
    }
}

impl Compile for SetVFlag {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let operand1 = self.operand1.compile(state)?;
        let operand2 = self.operand2.compile(state)?;
        let carry = self.carry.clone();
        let sub = self.sub.clone();

        Ok(quote!(
        general_assembly::operation::Operation::SetVFlag {
             operand1: #operand1,
             operand2: #operand2,
             carry: #carry,
             sub: #sub
         }))
    }
}

impl Compile for SetCFlagRot {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let operand1 = self.operand1.compile(state)?;
        if self.rotation == Rotation::Ror {
            return Ok(quote!(
            general_assembly::operation::Operation::SetCFlagRor(#operand1)
             ));
        }
        let operand2 = self
            .operand2
            .clone()
            .expect("Parser is broken")
            .compile(state)?;

        Ok(match self.rotation {
            Rotation::Lsl => quote!(
               general_assembly::operation::Operation::SetCFlagShiftLeft{
                    operand:#operand1,
                    shift:#operand2
                }
            ),
            Rotation::Rsl => quote!(
               general_assembly::operation::Operation::SetCFlagSrl{
                    operand:#operand1,
                    shift:#operand2
                }
            ),
            Rotation::Rsa => quote!(
               general_assembly::operation::Operation::SetCFlagSra{
                    operand:#operand1,
                    shift:#operand2
                }
            ),
            Rotation::Ror => quote!(
               general_assembly::operation::Operation::SetCFlagRor(#operand1)
            ),
        })
    }
}

impl Compile for SetCFlag {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let operand1 = self.operand1.compile(state)?;
        let operand2 = self.operand2.compile(state)?;
        let carry = self.carry.clone();
        let sub = self.sub.clone();

        Ok(quote!(
        general_assembly::operation::Operation::SetCFlag {
             operand1: #operand1,
             operand2: #operand2,
             carry: #carry,
             sub: #sub
         }))
    }
}
impl<T:Compile<Output = TokenStream>> Compile for Option<T>{ 
    type Output = T::Output;
    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        Ok(match self {
            Self::Some(s) =>{
                let inner = s.compile(state)?;
                quote! {Some(#inner)}
            },
            None => quote! {None}
        })
    }
}
impl Compile for RoundingMode{ 
    type Output = TokenStream;
    fn compile(&self, _state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        Ok(match self {
            Self::Exact => quote! {general_assembly::extension::ieee754::RoundingMode::Exact},
            Self::TiesTowardNegative => quote! {general_assembly::extension::ieee754::RoundingMode::TiesTowardNegative},
            Self::TiesTowardPositive => quote! {general_assembly::extension::ieee754::RoundingMode::TiesTowardPositive},
            Self::TiesToEven => quote! {general_assembly::extension::ieee754::RoundingMode::TiesToEven},
            Self::TiesToAway => quote! {general_assembly::extension::ieee754::RoundingMode::TiesToAway},
            Self::TiesTowardZero=> quote! {general_assembly::extension::ieee754::RoundingMode::TiesTowardZero},
            Self::Runtime(i) => quote! {#i}
        })
    }
}

impl Compile for Resize {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let intermediate = state.intermediate(self.target_ty).compile(state)?;
        let source_ty = self.operand.get_type();
        let operand = self.operand.compile(state)?;
        state.access_operand(self.operand.clone());

        let rm = self.rm.compile(state)?;
        let dest_ty = self.target_ty;

        let source_fp = source_ty.fp_name();
        let dest_fp = dest_ty.fp_name();
        match (source_ty, dest_ty) {
            (Type::U(_size), Type::F128 | Type::F64 | Type::F32 | Type::F16) => {
                state.to_insert_above.push(quote!(general_assembly::operation::Operation::Ieee754(
                general_assembly::extension::ieee754::Operations::ConvertFromInt {
                    destination: #intermediate.clone(),
                    operand: general_assembly::extension::ieee754::Operand {
                        ty: #source_fp,
                        value: general_assembly::extension::ieee754::OperandStorage::CoreOperand {
                            operand: #operand,
                            ty: #source_fp,
                            signed: false,
                        }
                    },
                }
                )));
            }
            (Type::I(_size), Type::F128 | Type::F64 | Type::F32 | Type::F16) => {
                state.to_insert_above.push(quote!(general_assembly::operation::Operation::Ieee754(
                general_assembly::extension::ieee754::Operations::ConvertFromInt {
                    destination: #intermediate.clone(),
                    operand: general_assembly::extension::ieee754::Operand {
                        ty: #source_fp,
                        value: general_assembly::extension::ieee754::OperandStorage::CoreOperand {
                            operand: #operand,
                            ty: #source_fp,
                            signed: true,
                        }
                    },
                }
                )));
            }
            (Type::F128 | Type::F64 | Type::F32 | Type::F16, Type::U(_size)) => {
                state.to_insert_above.push(quote!(general_assembly::operation::Operation::Ieee754(
                general_assembly::extension::ieee754::Operations::RoundToInt{
                    destination: general_assembly::extension::ieee754::Operand {
                            ty: #dest_fp.clone(),
                            value: general_assembly::extension::ieee754::OperandStorage::CoreOperand {
                                operand: #intermediate.clone(),
                                ty: #source_fp,
                                signed: false,
                            }
                        },
                    source: #operand.clone(),
                    rounding:#rm,
                },
                )))
            }
            (Type::F128 | Type::F64 | Type::F32 | Type::F16, Type::I(_size)) => {
                state.to_insert_above.push(quote!(general_assembly::operation::Operation::Ieee754(
                general_assembly::extension::ieee754::Operations::RoundToInt{
                    destination: general_assembly::extension::ieee754::Operand {
                            ty: #dest_fp.clone(),
                            value: general_assembly::extension::ieee754::OperandStorage::CoreOperand {
                                operand: #intermediate.clone(),
                                ty: #source_fp,
                                signed: true,
                            }
                        },
                    source: #operand.clone(),
                    rounding:#rm,
                },
                )));
            }
            // // No conversion needed.
            // (Type::U(size1) | Type::I(size1), Type::U(size2) | Type::I(size2))
            //     if size1 == size2 =>
            // {
            //     return Ok(quote! {#operand})
            // }
            (Type::I(_size1), Type::U(size2) ) => {
                state
                    .to_insert_above
                    .push(quote!(general_assembly::operation::Operation::Resize {
                            destination: #intermediate.clone(),
                            operand: #operand.clone(),
                            bits: #size2.clone()
                    }));
            }
            (Type::U(_size1),  Type::U(size2)) => {
                state
                    .to_insert_above
                    .push(quote!(general_assembly::operation::Operation::Resize {
                            destination: #intermediate.clone(),
                            operand: #operand.clone(),
                            bits: #size2.clone()
                    }));
            }
            (Type::U(size1),  Type::I(size2)) => {
                state
                    .to_insert_above
                    .push(quote!(general_assembly::operation::Operation::SignExtend {
                            destination: #intermediate.clone(),
                            operand: #operand.clone(),
                            /// What bit is considered the sign bit in operand
                            /// before the extension.
                            sign_bit: #size1.clone(),
                            /// The number of bits after extension.
                            target_size: #size2.clone(),
                    }));
            }
            (Type::I(size1),  Type::I(size2))  if size1 > size2 => {
                state
                    .to_insert_above
                    .push(quote!(general_assembly::operation::Operation::Resize {
                            destination: #intermediate.clone(),
                            operand: #operand.clone(),
                            bits: #size2.clone()
                    }));
            }
            (Type::I(size1),  Type::I(size2))   => {
                state
                    .to_insert_above
                    .push(quote!(general_assembly::operation::Operation::SignExtend {
                            destination: #intermediate.clone(),
                            operand: #operand.clone(),
                            /// What bit is considered the sign bit in operand
                            /// before the extension.
                            sign_bit: #size1.clone(),
                            /// The number of bits after extension.
                            target_size: #size2.clone(),
                    }));
            }
            (
                Type::F128 | Type::F64 | Type::F32 | Type::F16,
                Type::F128 | Type::F64 | Type::F32 | Type::F16,
            ) => {
                // For these we expect the SMT solver to handle it.
                state.to_insert_above.push(quote!(
                general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Convert {
                    destination: #intermediate.clone(),
                    source: #operand.clone(),
                    rounding: #rm,
                })
                ));
            }
            (Type::Unit, _) => {
                return Ok(quote! {compile_error!("Cannot resize from a unit type")})
            }
            (_, Type::Unit) => {
                return Ok(quote! {compile_error!("Cannot resize in to a unit type")})
            }
        }
        Ok(quote!(#intermediate))
    }
}

impl Compile for SignExtend {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let intermediate = state.intermediate(self.operand.get_type()).compile(state)?;
        let operand = self.operand.compile(state)?;
        let sign_bit = self.sign_bit.clone();
        let size = self.target_size;
        state
            .to_insert_above
            .push(quote!(general_assembly::operation::Operation::SignExtend {
                    destination: #intermediate.clone(),
                    operand: #operand,
                    sign_bit: #sign_bit.clone(),
                    target_size: #size.clone()

            }));
        Ok(quote!(#intermediate))
    }
}

impl Compile for ZeroExtend {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let intermediate = state.intermediate(Type::U(self.bits)).compile(state)?;
        let operand = self.operand.compile(state)?;
        state.access_operand(self.operand.clone());
        let bits = self.bits;
        state
            .to_insert_above
            .push(quote!(general_assembly::operation::Operation::ZeroExtend {
                    destination: #intermediate.clone(),
                    operand: #operand, bits: #bits.clone(), target_bits: #bits.clone()

            }));
        Ok(quote!(#intermediate))
    }
}

impl Compile for Sra {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let intermediate = state.intermediate(self.operand.get_type()).compile(state)?;
        let operand = self.operand.compile(state)?;
        state.access_operand(self.operand.clone());
        let shift = self.n.clone();
        state
            .to_insert_above
            .push(quote!(general_assembly::operation::Operation::Sra {
                    destination: #intermediate.clone(),
                    operand: #operand, shift: #shift.clone()
            }));
        Ok(quote!(#intermediate))
    }
}
impl Compile for Ror {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let intermediate = state.intermediate(self.operand.get_type()).compile(state)?;
        let operand = self.operand.compile(state)?;
        let shift = self.n.clone();
        state
            .to_insert_above
            .push(quote!(general_assembly::operation::Operation::Sror {
                    destination: #intermediate.clone(),
                    operand: #operand, shift: #shift.clone()
            }));
        Ok(quote!(#intermediate))
    }
}

impl Compile for Ite {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        state.access_operand(self.lhs.clone());
        let lhs = self.lhs.compile(state)?;

        state.access_operand(self.rhs.clone());
        let rhs = self.rhs.compile(state)?;
        let ty = self.comparison_type.expect("Could not get comparison type. Type checker must be faulty");
        let operation = (self.operation.clone(), ty).compile(state)?;
        let mut then = Vec::with_capacity(self.then.len());
        for el in &self.then {
            then.push(el.compile(state)?);
        }
        let mut otherwise = Vec::with_capacity(self.otherwise.len());
        for el in &self.otherwise {
            otherwise.push(el.compile(state)?);
        }
        let intermediate = state.intermediate(Type::U(1)).compile(state)?;
        let ret = match ty {
            Type::I(_) | Type::U(_) => {
                quote! {
                    general_assembly::operation::Operation::Compare {
                         lhs:#lhs.clone(),
                         rhs:#rhs.clone(),
                         operation:#operation,
                        destination:#intermediate,
                     },
                   general_assembly::operation::Operation::Ite {
                        condition:#intermediate,
                        then: vec![#(#then),*],
                        otherwise: vec![#(#otherwise),*],
                    }
                }
            }
            Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                quote! {
                    general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Compare {
                        lhs:#lhs.clone(),
                        rhs:#rhs.clone(),
                        operation:#operation.clone(),
                        destination:#intermediate,
                        signal:false,
                    }),
                   general_assembly::operation::Operation::Ite {
                        condition:#intermediate,
                        then: vec![#(#then),*],
                        otherwise: vec![#(#otherwise),*],
                    }
                }
            }
            Type::Unit => unimplemented!("Cannot compare unit types."),
        };

        Ok(ret)
    }
}

impl Compile for Abort {
    type Output = TokenStream;

    fn compile(&self, _state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let inner = self.inner.clone();
        Ok(quote! {general_assembly::operation::Operation::Abort{error:format!(#inner)}})
    }
}

impl Compile for Abs {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let inner = self.operand.compile(state)?;
        let ty = self.operand.get_type();
        let intermediate = state.intermediate(ty).compile(state)?;
        state.to_insert_above.push(match ty {
            Type::F128 | Type::F64 | Type::F32 | Type::F16 => {
                quote! {general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Abs {
                    operand:#inner,
                    destination:#intermediate,
                })}
            }
            Type::I(_) => todo!("Compute value of abs."),
            Type::Unit => return Err(Error::InternalError("Type checker faulty, cannot compute absolute value of unit type".to_string())),
            Type::U(_) => return Ok(quote! {general_assembly::operation::Operation::Nop}),
        });
        Ok(intermediate)
    }
}

impl Compile for Sqrt {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let inner = self.operand.compile(state)?;
        let ty = self.operand.get_type();
        let intermediate = state.intermediate(ty).compile(state)?;

        // TODO: implement for other types.

        state.to_insert_above.push(quote! {
            general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Sqrt {
                operand:#inner,
                destination:#intermediate,
            })
        });

        Ok(intermediate)
    }
}

impl Compile for MultiplyAndAccumulate {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let Self { lhs, rhs, addend } = self;
        let lhs_ty = lhs.get_type();
        let lhs = lhs.compile(state)?;
        let intermediate = state.intermediate(lhs_ty).compile(state)?;
        let rhs = rhs.compile(state)?;
        let add = addend.compile(state)?;

        // TODO: implement for other types.

        state.to_insert_above.push(quote! { 
            general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::FusedMultiplication {
                lhs:#lhs,
                rhs:#rhs,
                add:#add,
                destination:#intermediate,
            })
        });

        Ok(intermediate)
    }
}
impl Compile for IsFinite {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let inner = self.operand.compile(state)?;
        //let ty = self.operand.get_type();
        let intermediate = state.intermediate(Type::U(1)).compile(state)?;

        state.to_insert_above.push(quote! {
            general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::NonComputational {
                operand:#inner,
                operation:general_assembly::extension::ieee754::NonComputational::IsFinite,
                destination:#intermediate,
            })
        });

        Ok(intermediate)
    }
}

impl Compile for IsNaN {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let inner = self.operand.compile(state)?;
        //let ty = self.operand.get_type();
        let intermediate = state.intermediate(Type::U(1)).compile(state)?;

        state.to_insert_above.push(quote! {
            general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::NonComputational {
                operand:#inner,
                operation:general_assembly::extension::ieee754::NonComputational::IsNan,
                destination:#intermediate,
            })
        });

        Ok(intermediate)
    }
}

impl Compile for IsNormal {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let inner = self.operand.compile(state)?;
        //let ty = self.operand.get_type();
        let intermediate = state.intermediate(Type::U(1)).compile(state)?;

        state.to_insert_above.push(quote! {
            general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::NonComputational {
                operand:#inner,
                operation:general_assembly::extension::ieee754::NonComputational::IsNormal,
                destination:#intermediate,
            })
        });

        Ok(intermediate)
    }
}

impl Compile for Cast {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let inner = self.operand.compile(state)?;
        let ty = self.operand.get_type();
        let target_ty = self.target_type;
        let target_ty_fp = target_ty.fp_name();
        let ty_fp = ty.fp_name();
        let intermediate = state.intermediate(target_ty).compile(state)?;
        state.to_insert_above.push( match (ty, target_ty) {
            (Type::U(16), Type::F16) | (Type::U(32), Type::F32) | (Type::U(64),Type::F64) | (Type::U(128), Type::F128) => {
                quote! {
                    general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Copy{
                        destination: #intermediate,
                        source: general_assembly::extension::ieee754::Operand {ty: #target_ty_fp, value: general_assembly::extension::ieee754::OperandStorage::CoreOperand{
                            operand: #inner,
                            ty: #target_ty_fp,
                            signed: false 
                        }}
                    })
                }
            },
            (Type::I(16), Type::F16) | (Type::I(32), Type::F32) | (Type::I(64),Type::F64) | (Type::I(128), Type::F128) => {
                quote! {
                    general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Copy{
                        destination: #intermediate,
                        source: general_assembly::extension::ieee754::Operand {ty: #target_ty_fp, value: general_assembly::extension::ieee754::OperandStorage::CoreOperand{
                            operand: #inner,
                            ty: #target_ty_fp,
                            signed: true
                        }}
                    })
                }
            }
            (Type::F16, Type::U(16)) | (Type::F32, Type::U(32)) | (Type::F64, Type::U(64)) | (Type::F128,Type::U(128)) => {
                quote! {
                    general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Copy{
                        source: #inner,
                        destination: general_assembly::extension::ieee754::Operand {ty: #ty_fp, value: general_assembly::extension::ieee754::OperandStorage::CoreOperand{
                            operand: #intermediate,
                            ty: #ty_fp,
                            signed: false 
                        }}
                    })
                }
            },
            (Type::F16, Type::I(16)) | (Type::F32, Type::I(32)) | (Type::F64, Type::I(64)) | (Type::F128,Type::I(128)) => {
                quote! {
                    general_assembly::operation::Operation::Ieee754(general_assembly::extension::ieee754::Operations::Copy{
                        source: #inner,
                        destination: general_assembly::extension::ieee754::Operand {ty: #ty_fp, value: general_assembly::extension::ieee754::OperandStorage::CoreOperand{
                            operand: #intermediate,
                            ty: #ty_fp,
                            signed: true
                        }}
                    })
                }
            }
            _ => todo!("No more casts needed for now.")
        });

        // TODO: implement for other types.

        Ok(intermediate)
    }
}

impl Compile for Log {
    type Output = TokenStream;
    
    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {

        let Self { level, operand, meta, call_site } = self;
        let ty = operand.get_type();

        match ty {
            Type::I(_) | Type::U(_) => {},
            _ => todo!("Add debugging for other types")
        }

        let log_message = quote_spanned! {*call_site => Log};
        let operand = operand.compile(state)?;
        let level = match level {
            LogLevel::Error => quote! {general_assembly::operand::LogLevel::Error},
            LogLevel::Warn => quote! {general_assembly::operand::LogLevel::Warn},
            LogLevel::Debug => quote! {general_assembly::operand::LogLevel::Debug},
            LogLevel::Info => quote! {general_assembly::operand::LogLevel::Info},
            LogLevel::Trace=> quote! {general_assembly::operand::LogLevel::Trace},
        };

        Ok(quote! {general_assembly::operation::Operation::#log_message {
            level:#level,
            operand:#operand,
            meta:#meta.to_string(),
        }})
    }
}
// //
// impl Compile for Saturate {
//    type Output = TokenStream;
//     fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
//
//         let Self { lhs, rhs, operation } = self;
//
//
//     }
// }
