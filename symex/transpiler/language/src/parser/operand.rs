//! Defines parsing rules for the ast
//! [`Operands`](crate::ast::operand::Operand).
use quote::ToTokens;
use syn::{
    parenthesized,
    parse::{discouraged::Speculative, Parse, ParseStream, Result},
    token::Let,
    Expr,
    Ident,
    Lit,
    LitInt,
    Token,
    Type,
};

use crate::ast::operand::*;

impl ExprOperand {
    fn parse_first_stage(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        if let Ok(function) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::FunctionCall(function));
        }

        let speculative = input.fork();
        if let Ok(ident) = speculative.parse() {
            if !speculative.peek(syn::token::Paren) {
                input.advance_to(&speculative);
                return Ok(Self::Ident(ident));
            }
        }

        let speculative = input.fork();
        if let Ok(lit) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Literal(lit));
        }

        if input.peek(syn::token::Paren) {
            let content;
            parenthesized!(content in input);
            let inner: Expr = content.parse()?;
            if !content.is_empty() {
                return Err(content.error("Expected : (<Expr>)"));
            }
            return Ok(Self::Paren(inner));
        }
        Err(input.error(
            "Expected an ExprOperand here.
    - A function call
    - A literal
    - An idenitifer",
        ))
    }
}
impl Parse for ExprOperand {
    fn parse(input: ParseStream) -> Result<Self> {
        let value = Self::parse_first_stage(input)?;
        if input.peek(Token![.]) {
            let mut ops = vec![];
            while input.peek(Token![.]) {
                let _: Token![.] = input.parse()?;
                let fident: Ident = input.parse()?;
                if input.peek(syn::token::Paren) {
                    let content;
                    syn::parenthesized!(content in input);
                    let operands = content.parse_terminated(Operand::parse, syn::token::Comma)?;
                    ops.push((fident, operands.into_iter().map(Box::new).collect()));
                    continue;
                }
                return Err(input.error("Expected function arguments"));
            }
            return Ok(Self::Chain(Box::new(value), ops));
        }

        Ok(value)
    }
}

impl Parse for Operand {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        if let Ok(val) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::FieldExtract((val, None)));
        }

        let speculative = input.fork();
        if let Ok(val) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::DynamicFieldExtract((val, None)));
        }

        let speculative = input.fork();
        if let Ok(lit) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::WrappedLiteral(lit));
        }

        let speculative = input.fork();
        if let Ok(val) = speculative.parse() {
            input.advance_to(&speculative);
            // These must be inferred.
            return Ok(Self::Expr((val, None)));
        }

        let speculative = input.fork();
        if let Ok(val) = speculative.parse() {
            let val: ParseableIdent = val;

            input.advance_to(&speculative);
            return Ok(Self::Ident(val.0));
        }

        Err(input.error("Expected operand"))
    }
}

struct ParseableIdent((IdentOperand, Option<crate::ast::operand::Type>));
impl Parse for ParseableIdent {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Let) {
            let _: Let = input.parse()?;
            let ident: Ident = input.parse()?;
            let mut ty = None;
            if input.peek(Token![:]) {
                let _: Token![:] = input.parse()?;
                ty = Some(input.parse()?);
            }
            return Ok(Self((
                IdentOperand {
                    define: true,
                    ident,
                },
                ty,
            )));
        }
        let ident: Ident = input.parse()?;
        Ok(Self((
            IdentOperand {
                define: false,
                ident,
            },
            None,
        )))
    }
}

impl Parse for crate::ast::operand::Type {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty: syn::Type = input.parse()?;

        let ty = ty.to_token_stream().to_string().to_lowercase();
        if ty.starts_with("i") {
            let ty = ty.strip_prefix("i").expect("Pre-condition faulty");
            let value = str::parse(ty).map_err(|_| input.error("Invalid type"))?;
            return Ok(Self::I(value));
        }
        if ty.starts_with("u") {
            let ty = ty.strip_prefix("u").expect("Pre-condition faulty");
            let value = str::parse(ty).map_err(|_| input.error("Invalid type"))?;
            return Ok(Self::U(value));
        }
        Ok(match ty.as_str() {
            "f16" => Self::F16,
            "f32" => Self::F32,
            "f64" => Self::F64,
            "f128" => Self::F128,
            _ => return Err(input.error("Invalid type")),
        })
    }
}

impl Parse for DelimiterType {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        if let Ok(val) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Ident(val));
        }

        Ok(Self::Const(input.parse()?))
    }
}

impl Parse for FieldExtract {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Ident) {
            return Err(input.error("Expected Identifier"));
        }
        let operand: Ident = input.parse()?;

        if !input.peek(Token![<]) {
            return Err(input.error("Expected <end:start:ty?>"));
        }

        let _: syn::token::Lt = input.parse()?;

        let end: LitInt = input.parse()?;
        let end = end.base10_parse::<u32>()?;

        let start = match input.peek(Token![:]) {
            true => {
                let _: Token![:] = input.parse()?;

                let start: LitInt = input.parse()?;
                start.base10_parse::<u32>()?
            }
            false => end,
        };

        let speculative = input.fork();
        let ty: Option<Type> = match speculative.parse() {
            Ok(ty) => {
                let _: Token![:] = ty;
                input.advance_to(&speculative);
                Some(input.parse()?)
            }
            Err(_) => None,
        };

        if !input.peek(Token![>]) {
            return Err(input.error("Expected <end:start:ty?>"));
        }
        let _: Token![>] = input.parse()?;

        Ok(Self {
            operand,
            start,
            end,
            ty,
        })
    }
}

impl Parse for DynamicFieldExtract {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Ident) {
            return Err(input.error("Expected Identifier"));
        }
        let operand: Ident = input.parse()?;

        if !input.peek(Token![<]) {
            return Err(input.error("Expected <end:start:ty?>"));
        }

        let _: syn::token::Lt = input.parse()?;

        let end = input.parse()?;

        if !input.peek(Token![:]) {
            return Err(input.error("Expected <end:start:ty?>"));
        }
        let _: Token![:] = input.parse()?;

        let start = input.parse()?;

        let speculative = input.fork();
        let ty: Option<Type> = match speculative.parse() {
            Ok(ty) => {
                let _: Token![:] = ty;
                input.advance_to(&speculative);
                Some(input.parse()?)
            }
            Err(_) => None,
        };

        if !input.peek(Token![>]) {
            return Err(input.error("Expected <end:start:ty?>"));
        }
        let _: Token![>] = input.parse()?;

        Ok(Self {
            operand,
            start,
            end,
            ty,
        })
    }
}

impl Parse for SetType {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident: Ident = input.parse()?;
        let _: Token![:] = input.parse()?;
        let ty: crate::ast::operand::Type = input.parse()?;
        //let _:Token![] = input.parse()?;
        if input.peek(Token![;]) {
            Ok(Self { operand: ident, ty })
        } else {
            Err(input.error("Expected ;"))
        }
    }
}
impl Parse for WrappedLiteral {
    fn parse(input: ParseStream) -> Result<Self> {
        let lit: Lit = input.parse()?;
        let ty = match &lit {
            Lit::Str(_) => {
                return Err(syn::Error::new(
                    lit.span(),
                    "No support for literal strings.",
                ))
            }
            Lit::CStr(_) => {
                return Err(syn::Error::new(
                    lit.span(),
                    "No support for literal c strings.",
                ))
            }

            Lit::Float(l) => {
                let suffix = l.suffix().to_lowercase();
                if suffix.starts_with("f") {
                    let bits = suffix.strip_prefix("f").unwrap();
                    let size = bits.parse::<u32>().map_err(|_| {
                        syn::Error::new(lit.span(), "Could not parse bit size of literal.")
                    })?;
                    match size {
                        16 => Ok(crate::ast::operand::Type::F16),
                        32 => Ok(crate::ast::operand::Type::F32),
                        64 => Ok(crate::ast::operand::Type::F64),
                        128 => Ok(crate::ast::operand::Type::F128),
                        _ => Err(syn::Error::new(lit.span(), "Invalid floating point size.")),
                    }
                } else {
                    Err(syn::Error::new(
                        lit.span(),
                        "Literal operands must have a specified type.",
                    ))
                }
            }
            Lit::Int(l) => {
                let suffix = l.suffix().to_lowercase();
                if suffix.starts_with("u") {
                    let bits = suffix.strip_prefix("u").unwrap();
                    let size = bits.parse::<u32>().map_err(|_| {
                        syn::Error::new(lit.span(), "Could not parse bit size of literal.")
                    })?;
                    Ok(crate::ast::operand::Type::U(size))
                } else if suffix.starts_with("i") {
                    let bits = suffix.strip_prefix("i").unwrap();
                    let size = bits.parse::<u32>().map_err(|_| {
                        syn::Error::new(lit.span(), "Could not parse bit size of literal.")
                    })?;
                    Ok(crate::ast::operand::Type::I(size))
                } else {
                    Err(syn::Error::new(
                        lit.span(),
                        "Literal operands must have a specified type.",
                    ))
                }
            }
            Lit::Bool(_l) => Ok(crate::ast::operand::Type::U(1)),
            _ => Err(syn::Error::new(lit.span(), "Unsupported literal type.")),
        }?;
        Ok(Self { val: lit, ty })
    }
}
