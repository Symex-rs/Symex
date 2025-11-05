//! Defines a simple backed to transpile the [`ast`](crate::ast)
//! into [`Operations`](general_assembly::operation::Operation).

pub mod function;
pub mod operand;
pub mod operations;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::Ident;

use crate::{
    ast::{
        operand::{Type, WrappedLiteral},
        *,
    },
    Compile,
    Error,
    TranspilerState,
};

impl From<IR> for Result<TokenStream, Error> {
    fn from(value: IR) -> Result<TokenStream, Error> {
        let mut state = TranspilerState::new();
        state.enter_scope();

        let ret = value.ret.clone().unwrap_or(format_ident!("ret"));
        let mut ext = Vec::new();

        for el in value.extensions {
            ext.push((ret.clone(), el).compile(&mut state)?);
        }
        let declarations: Vec<WrappedLocalDeclaration> =
            state.to_declare()?.iter().map(|el| el.into()).collect();
        state.to_declare()?;
        Ok(match value.ret {
            Some(_) => quote!(
                #(#declarations)*

                #(#ext;)*
            ),
            None => quote!(
                {
                    let mut ret =  Vec::new();
                    #(#declarations)*
                    #(#ext;)*
                    ret
                }
            ),
        })
    }
}

impl Compile for IRExpr {
    type Output = TokenStream;

    fn compile(
        &self,
        state: &mut crate::TranspilerState<Self::Output>,
    ) -> Result<Self::Output, Error> {
        match self {
            Self::Assign(assign) => assign.compile(state),
            Self::UnOp(unop) => unop.compile(state),
            Self::BinOp(binop) => binop.compile(state),
            Self::Function(f) => (f.clone(), Type::Unit).compile(state),
            Self::Jump(j) => j.compile(state),
            Self::SetType(_) => Ok(quote! {general_assembly::operation::Operation::Nop}),
        }
    }
}

impl Type {
    fn fp_name(&self) -> TokenStream {
        match self {
            Self::F16 => quote! {general_assembly::extension::ieee754::OperandType::Binary16},
            Self::F32 => quote! {general_assembly::extension::ieee754::OperandType::Binary32},
            Self::F64 => quote! {general_assembly::extension::ieee754::OperandType::Binary64},
            Self::F128 => quote! {general_assembly::extension::ieee754::OperandType::Binary128},
            Self::I(size) => quote! {general_assembly::extension::ieee754::OperandType::Integral {
                size:#size,
                signed:true,
            }},
            Self::U(size) => quote! {general_assembly::extension::ieee754::OperandType::Integral {
                size:#size,
                signed:false,
            }},
            Self::Unit => {
                quote! {compile_error!("Cannot use a unit type as a floating point value")}
            }
        }
    }

    fn local(&self, i: Ident) -> TokenStream {
        let name_str = i.to_string();
        let fp = self.fp_name();
        match self {
            Self::I(_) | Self::U(_) => {
                quote! {let #i = general_assembly::operand::Operand::Local(#name_str.to_string());}
            }
            Self::F16 | Self::F32 | Self::F64 | Self::F128 => {
                quote! {let #i = general_assembly::extension::ieee754::Operand {
                    ty: #fp,
                    value: general_assembly::extension::ieee754::OperandStorage::Local(#name_str.to_string()),
                };}
            }
            Self::Unit => quote! {compile_error!("Cannot use unit types as local values.")},
        }
    }
}

/// TODO: docs
pub struct WrappedLocalDeclaration(Ident, Type);
impl From<&(Ident, Type)> for WrappedLocalDeclaration {
    fn from(value: &(Ident, Type)) -> Self {
        Self(value.0.clone(), value.1)
    }
}
impl ToTokens for WrappedLocalDeclaration {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(self.1.local(self.0.clone()));
    }
}
impl Compile for WrappedLocalDeclaration {
    type Output = TokenStream;

    fn compile(&self, _state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        Ok(self.1.local(self.0.clone()))
    }
}

impl Compile for (Ident, Statement) {
    type Output = TokenStream;

    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error> {
        let ret = match self.1.clone() {
            Statement::If(e, happy_case_in, Some(sad_case_in)) => {
                state.enter_scope();

                let mut happy_case: Vec<TokenStream> = Vec::new();
                for el in (*happy_case_in).into_iter() {
                    happy_case.push((self.0.clone(), el).compile(state)?);
                }
                let to_declare_happy: Vec<WrappedLocalDeclaration> =
                    state.to_declare()?.iter().map(|el| el.into()).collect();

                state.enter_scope();
                let mut sad_case: Vec<TokenStream> = Vec::new();
                for el in (*sad_case_in).into_iter() {
                    sad_case.push((self.0.clone(), el).compile(state)?);
                }
                let to_declare_sad: Vec<WrappedLocalDeclaration> =
                    state.to_declare()?.iter().map(|el| el.into()).collect();

                Ok(quote!(
                    if #e {
                        #(#to_declare_happy)*
                        #(#happy_case;)*
                    } else {
                        #(#to_declare_sad)*
                        #(#sad_case;)*
                    }
                ))
            }
            Statement::If(e, happy_case_in, None) => {
                state.enter_scope();
                let mut happy_case: Vec<TokenStream> = Vec::new();
                for el in (*happy_case_in).into_iter() {
                    happy_case.push((self.0.clone(), el).compile(state)?);
                }
                let to_declare_happy: Vec<WrappedLocalDeclaration> =
                    state.to_declare()?.iter().map(|el| el.into()).collect();
                Ok(quote!(
                    // #(let #to_declare_global =
                        // Operand::Local(#declaration_strings_global.to_owned());)*
                    if #e {
                        #(#to_declare_happy)*
                        #(#happy_case;)*
                    }
                ))
            }
            Statement::For(i, e, block_in) => {
                state.enter_scope();
                let mut block: Vec<TokenStream> = Vec::new();
                for el in (*block_in).into_iter() {
                    block.push((self.0.clone(), el).compile(state)?);
                }
                let to_declare_inner: Vec<WrappedLocalDeclaration> =
                    state.to_declare()?.iter().map(|el| el.into()).collect();
                Ok(quote!(
                    for #i in #e {
                        #(#to_declare_inner)*
                        #(#block;)*
                    }
                ))
            }
            Statement::Exprs(extensions) => {
                let mut ext = Vec::new();
                for el in extensions {
                    ext.push(el.compile(state)?);
                }
                let ret = self.0.clone();
                let declarations: Vec<WrappedLocalDeclaration> = state
                    .to_declare
                    .last_mut()
                    .expect("Did not expect to be empty...")
                    .drain(..)
                    .map(|(id, ty)| (&(id, ty)).into())
                    .collect();
                let to_insert_above: Vec<TokenStream> = state.to_insert_above.drain(..).collect();
                Ok(quote!(
                #(#declarations)*
                #ret.extend([
                    #(#to_insert_above,)*
                    #(#ext,)*
                ])
                ))
            }
        };
        ret
    }
}

impl crate::ast::operand::Operand {
    fn get_type(&self) -> Type {
        match self {
            Self::FieldExtract((_, ty)) => ty.expect("Type checker failed"),
            Self::Expr((_, ty)) => ty.expect("Type checker failed"),
            Self::Ident((_, ty)) => ty.expect("Type checker failed"),
            Self::WrappedLiteral(WrappedLiteral { val: _, ty }) => *ty,
            Self::DynamicFieldExtract((_, ty)) => ty.expect("Type checker failed"),
        }
    }
}
