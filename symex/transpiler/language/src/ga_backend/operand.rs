//! Defines transpiling rules for the ast
//! [`Operands`](crate::ast::operand::Operand).
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};

use crate::{ast::operand::*, Compile, Error};

impl Compile for Operand {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        match self {
            Self::Expr((e, ty)) => (e.clone(), ty.expect("Type check pass faulty")).compile(state),
            Self::Ident((i, ty)) => {
                //state.access(i.ident.clone());
                (
                    i.clone(),
                    ty.expect("Type check pass faulty for Ident operands"),
                )
                    .compile(state)
            }
            Self::FieldExtract(f) => f.compile(state),
            Self::WrappedLiteral(l) => l.compile(state),
            Self::DynamicFieldExtract(f) => f.compile(state),
        }
    }
}

impl Compile for WrappedLiteral {
    type Output = TokenStream;

    fn compile(
        &self,
        _state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        let val = self.val.clone();
        let span = val.span();
        let tyfp = self.ty.fp_name();
        match self.ty {
            Type::U(1) => Ok(
                quote_spanned! {span => general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Bit(#val))},
            ),
            Type::U(8) => Ok(
                quote_spanned! {span => general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word8(#val as u8))},
            ),
            Type::U(16) => Ok(
                quote_spanned! {span => general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word16(#val as u16))},
            ),
            Type::U(32) => Ok(
                quote_spanned! {span => general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word32(#val as u32))},
            ),
            Type::U(64) => Ok(
                quote_spanned! {span => general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word64(#val as u64))},
            ),
            Type::U(128) => Ok(
                quote_spanned! {span => general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word128(#val as u128))},
            ),
            Type::I(8) => Ok(
                quote_spanned! {span =>general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word8((#val).cast_unsigned()))},
            ),
            Type::I(16) => Ok(
                quote_spanned! {span =>general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word16((#val).cast_unsigned()))},
            ),
            Type::I(32) => Ok(
                quote_spanned! {span =>general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word32((#val).cast_unsigned()))},
            ),
            Type::I(64) => Ok(
                quote_spanned! {span =>general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word64((#val).cast_unsigned()))},
            ),
            Type::I(128) => Ok(
                quote_spanned! {span =>general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word128((#val).cast_unsigned()))},
            ),
            Type::F16 | Type::F32 | Type::F64 | Type::F128 => Ok(
                quote_spanned! {span =>general_assembly::extension::ieee754::Operand{
                    ty: #tyfp,
                    value: general_assembly::extension::ieee754::OperandStorage::Immediate { value: #val as f64 , ty: #tyfp }
                }},
            ),
            _ => Err(Error::InternalError(
                "Unsupported wrapped literal type.".to_string(),
            )),
        }
    }
}

impl Compile for (ExprOperand, Type) {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        Ok(match &self.0 {
            ExprOperand::Paren(p) => quote!((#p)),
            ExprOperand::Chain(i, it) => {
                let ident: TokenStream = (*(*i).clone(), self.1).compile(state)?;
                let mut ops: Vec<TokenStream> = Vec::new();
                for (ident, args) in it {
                    let mut args_ret = Vec::with_capacity(args.len());
                    for arg in args {
                        let arg = arg.compile(state)?;
                        args_ret.push(arg);
                    }
                    ops.push(quote!(#ident(#(#args_ret),*)));
                }
                quote!(#ident.#(#ops).*)
            }
            ExprOperand::Ident(i) => {
                state.access(i.clone());
                quote!(#i.clone())
            }
            ExprOperand::Literal(l) => quote!(#l),
            ExprOperand::FunctionCall(f) => (f.clone(), self.1).compile(state)?,
        })
    }
}
impl Compile for (IdentOperand, Type) {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        match self.0.define {
            // TODO: Inform decare local of type.
            true => state.declare_local(self.0.ident.clone(), self.1),
            false => {
                state.access(self.0.ident.clone());
            }
        };
        let ident = self.0.ident.clone();
        let span = self.0.ident.span();
        Ok(quote_spanned!(span => #ident.clone()))
    }
}

impl Compile for DelimiterType {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        Ok(match self {
            Self::Const(l) => quote!(#l),
            Self::Ident(i) => {
                state.access(i.clone());
                quote!(#i)
            }
        })
    }
}

impl Compile for (DynamicFieldExtract, Option<Type>) {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        let intermediate = state.intermediate(self.1.expect("Bitfield extractions cannot be performed if the type is not known. Type checker must be faulty")).compile(state)?;
        let operand = self.0.operand.clone();
        state.access(operand.clone());
        let (start, end) = (
            self.0.start.clone().compile(state)?,
            self.0.end.clone().compile(state)?,
        );
        // let (start, end) = (self.0.start, self.0.end);

        state.to_insert_above.extend([quote! (
            general_assembly::operation::Operation::BitFieldExtract{
                destination: #intermediate.clone(),
                operand: #operand.clone(),
                start_bit: #start,
                stop_bit: #end,
            }
        )]);
        Ok(quote! {#intermediate})
    }
}

impl Compile for (FieldExtract, Option<Type>) {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        let intermediate = state.intermediate(self.1.expect("Bitfield extractions cannot be performed if the type is not known. Type checker must be faulty")).compile(state)?;
        let operand = self.0.operand.clone();
        state.access(operand.clone());
        // let (start, end) = (
        // self.0.start.clone().compile(state)?,
        // self.0.end.clone().compile(state)?,
        // );
        let (start, end) = (self.0.start, self.0.end);

        state.to_insert_above.extend([quote! (
            general_assembly::operation::Operation::BitFieldExtract{
                destination: #intermediate.clone(),
                operand: #operand.clone(),
                start_bit: #start,
                stop_bit: #end,
            }
        )]);
        Ok(quote! {#intermediate})

        //let intermediate2 = state.intermediate().compile(state)?;
        //state.access(self.operand.clone());
        //let ty = self.ty.clone().unwrap_or(syn::parse_quote!(u32));
        //state.to_insert_above.extend([
        //    quote!(
        //        Operation::Srl {
        //            destination: #intermediate1.clone(),
        //            operand: #operand.clone(),
        //            shift: Operand::Immediate((#start as #ty).into())
        //        }
        //    ),
        //    quote!(
        //        #[allow(clippy::unnecessary_cast)]
        //        Operation::And {
        //            destination: #intermediate2.clone(),
        //            operand1: #intermediate1.clone(),
        //            operand2: Operand::Immediate(
        //                (
        //                    (
        //                        (
        //                            (0b1u64 << (#end as u64 - #start as u64 +
        // 1u64)) as u64                        ) - (1 as u64)
        //                    )as #ty
        //                ).into()
        //            )
        //
        //        }
        //    ),
        //]);
        //Ok(quote!(#intermediate2))
    }
}
