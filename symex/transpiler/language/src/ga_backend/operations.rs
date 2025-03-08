//! Defines transpiling rules for the ast
//! [`Operations`](crate::ast::operations::Operation).
use proc_macro2::TokenStream;
use quote::quote;

use crate::{ast::operations::*, Compile, Error};

impl Compile for Assign {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        let dst: TokenStream = self.dest.compile(state)?;
        let rhs: TokenStream = self.rhs.compile(state)?;
        let to_insert = state.to_insert_above.drain(..);
        Ok(quote! {
            #(#to_insert,)*
            Operation::Move { destination: #dst, source: #rhs }
        })
    }
}

impl Compile for UnOp {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        let dst: TokenStream = self.dest.compile(state)?;
        let rhs: TokenStream = self.rhs.compile(state)?;
        let ret = match self.op {
            UnaryOperation::BitwiseNot => quote!(
                Operation::Not { destination: #dst, operand: #rhs }
            ),
        };

        let to_insert = state.to_insert_above.drain(..);
        Ok(quote!(
        #(#to_insert,)*
        #ret
        ))
    }
}

impl Compile for BinOp {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        let dst: TokenStream = self.dest.compile(state)?;
        let rhs: TokenStream = self.rhs.compile(state)?;
        let lhs: TokenStream = self.lhs.compile(state)?;
        let ret = match self.op {
            BinaryOperation::Sub => quote!(
                        Operation::Sub {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::SSub => quote!(
                        Operation::SSub {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs,
                            signed: false,
                        }
            ),
            BinaryOperation::SSubs => quote!(
                        Operation::SSub {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs,
                            signed: true,
                        }
            ),
            BinaryOperation::Add => quote!(
                        Operation::Add {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::SAdd => quote!(
                        Operation::SAdd {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs,
                            signed:false,
                        }
            ),
            BinaryOperation::SAdds => quote!(
                        Operation::SAdd {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs,
                            signed:true,
                        }
            ),
            BinaryOperation::AddWithCarry => quote!(
                        Operation::Adc {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::UDiv => quote!(
                        Operation::UDiv {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::SDiv => quote!(
                        Operation::SDiv {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::Mul => quote!(
                        Operation::Mul {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::BitwiseOr => quote!(
                        Operation::Or {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::BitwiseAnd => quote!(
                        Operation::And {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::BitwiseXor => quote!(
                        Operation::Xor {
                            destination: #dst,
                            operand1: #lhs,
                            operand2: #rhs
                        }
            ),
            BinaryOperation::LogicalLeftShift => quote!(
                        Operation::Sl {
                            destination: #dst,
                            operand: #lhs,
                            shift: #rhs
                        }
            ),
            BinaryOperation::LogicalRightShift => quote!(
                        Operation::Srl {
                            destination: #dst,
                            operand: #lhs,
                            shift: #rhs
                        }
            ),
            BinaryOperation::ArithmeticRightShift => quote!(
                        Operation::Sra {
                            destination: #dst,
                            operand: #lhs,
                            shift: #rhs
                        }
            ),
        };
        let to_insert = state.to_insert_above.drain(..);
        Ok(quote!(
        #(#to_insert,)*
        #ret
        ))
    }
}
impl Compile for CompareOperation {
    type Output = TokenStream;

    fn compile(
        &self,
        _state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        Ok(match self {
            Self::Lt => quote! {Comparison::Lt},
            Self::Gt => quote! {Comparison::Gt},
            Self::Geq => quote! {Comparison::Geq},
            Self::Leq => quote! {Comparison::Leq},
            Self::Eq => quote! {Comparison::Eq},
            Self::Neq => quote! {Comparison::Neq},
        })
    }
}
