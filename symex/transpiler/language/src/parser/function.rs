//! Defines parsing rules for the ast
//! [`Functions`](crate::ast::function::Function).
use proc_macro2::TokenStream;
use syn::{
    braced,
    parenthesized,
    parse::{discouraged::Speculative, Parse, ParseStream, Result},
    Expr,
    Ident,
    Lit,
    LitInt,
    LitStr,
    Token,
};

use crate::ast::{
    function::*,
    operand::{Operand, Type},
    IRExpr,
};
impl Parse for Function {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        if let Ok(intrinsic) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Intrinsic(intrinsic));
        }
        let ident: Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let inner = content.parse_terminated(Expr::parse, Token![,])?;
        Ok(Self::Ident(ident, inner.into_iter().collect()))
    }
}
impl Parse for Intrinsic {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::LocalAddress(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Log(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Register(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Flag(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::ZeroExtend(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::SignExtend(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Resize(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::SetNFlag(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::SetCFlag(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::SetCFlagRot(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::SetVFlag(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Ror(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Sra(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Ite(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Abort(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Abs(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Sqrt(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Cast(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::IsNormal(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::IsNaN(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::IsFinite(el));
        }

        let speculative = input.fork();
        if let Ok(el) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::MultiplyAndAccumulate(el));
        }

        Ok(Self::SetZFlag(input.parse()?))
    }
}
impl Parse for FunctionCall {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident: Function = input.parse()?;

        let content;
        syn::parenthesized!(content in input);
        let args = content.parse_terminated(Expr::parse, syn::token::Comma)?;
        Ok(Self {
            ident,
            args: args.into_iter().collect(),
        })
    }
}

// =========================================================================
//                          Intrinsics parsing
// =========================================================================

impl Parse for Jump {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "jump" {
            return Err(input.error("jump"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);

        let target: Operand = content.parse()?;
        if content.peek(Token![,]) {
            let _: Token![,] = content.parse()?;
            let conditions = content.parse()?;
            if !content.is_empty() {
                return Err(content.error("Too many arguments"));
            }
            Ok(Self {
                target,
                condition: Some(conditions),
            })
        } else {
            Ok(Self {
                target,
                condition: None,
            })
        }
    }
}

impl Parse for LocalAddress {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "localaddress" {
            return Err(input.error("localaddress"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);

        let name: Ident = content.parse()?;

        let _: Token![,] = content.parse()?;
        let bits: LitInt = content.parse()?;
        let bits = bits
            .base10_digits()
            .parse()
            .map_err(|_| syn::Error::new_spanned(bits, "Could not parse as u32"))?;
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self { name, bits })
    }
}

impl Parse for Register {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        let ident = ident.to_string().to_lowercase();
        if ident.as_str() != "register" && ident.as_str() != "reg" {
            return Err(input.error("expected Reg or Register"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);

        let name: Lit = match content.peek(Ident) {
            // If name is an identifier, we convert the identifier to a string
            true => {
                let ident: Ident = content.parse()?;
                Lit::Str(LitStr::new(&ident.to_string(), ident.span()))
            }
            false => content.parse()?,
        };
        if content.peek(Token![,]) {
            let _: Token![,] = content.parse()?;
            let ty: Type = content.parse()?;
            Ok(Self {
                name,
                source_type: Some(ty),
            })
        } else {
            Ok(Self {
                name,
                source_type: None,
            })
        }
    }
}

impl Parse for Flag {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "flag" {
            return Err(input.error("flag"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);

        let name: Lit = match content.peek(Ident) {
            // If name is an identifier, we convert the identifier to a string
            true => {
                let ident: Ident = content.parse()?;
                Lit::Str(LitStr::new(&ident.to_string(), ident.span()))
            }
            false => content.parse()?,
        };
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self { name })
    }
}

impl Parse for ZeroExtend {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "zeroextend" {
            return Err(input.error("Expected zeroextend"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let n: LitInt = content.parse()?;
        let n = n
            .base10_digits()
            .parse()
            .map_err(|_| syn::Error::new_spanned(n, "Could not parse as u32"))?;
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self {
            operand: op,
            bits: n,
        })
    }
}

impl Parse for Resize {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "resize" {
            return Err(input.error("Expected resize"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let target_ty: Type = content.parse()?;
        let mut rm = None;
        if content.peek(Token![,]) {
            let _: Token![,] = content.parse()?;
            rm = Some(content.parse()?);
        }
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self {
            operand: op,
            target_ty,
            rm,
        })
    }
}

impl Parse for SignExtend {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "signextend" {
            return Err(input.error("Expected signextend"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let n: Expr = content.parse()?;
        let _: Token![,] = content.parse()?;
        let size: LitInt = content.parse()?;
        let size = size
            .base10_digits()
            .parse()
            .map_err(|_| syn::Error::new_spanned(size, "Could not parse as u32"))?;
        if !content.is_empty() {
            return Err(content.error("Too many tokens."));
        }
        Ok(Self {
            operand: op,
            sign_bit: n,
            target_size: size,
        })
    }
}
impl Parse for ConditionalJump {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "conditionaljump" {
            return Err(input.error("Expected ConditionalJump"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let condition: Ident = content.parse()?;
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self {
            operand: op,
            condition,
        })
    }
}
impl Parse for SetNFlag {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "setnflag" {
            return Err(input.error("Expected setnflag"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self { operand: op })
    }
}
impl Parse for SetZFlag {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "setzflag" {
            return Err(input.error("Expected setzflag"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self { operand: op })
    }
}
impl Parse for SetCFlagRot {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "setcflag" {
            return Err(input.error("Expected setcflag"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op1: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;

        if content.peek2(Token![,]) {
            let op2: Operand = content.parse()?;

            let _: Token![,] = content.parse()?;

            let shift = {
                let ident: Ident = content.parse()?;
                match ident.to_string().to_lowercase().as_str() {
                    "lsl" => Rotation::Lsl,
                    "rsl" => Rotation::Rsl,
                    "rsa" => Rotation::Rsa,
                    _ => return Err(content.error("Expected, \"lsl, rsl, rsa\"")),
                }
            };
            return Ok(Self {
                operand1: op1,
                operand2: Some(op2),
                rotation: shift,
            });
        }
        let shift = {
            let ident: Ident = content.parse()?;
            match ident.to_string().to_lowercase().as_str() {
                "ror" => Rotation::Ror,
                _ => return Err(content.error("Expected, \"ror\"")),
            }
        };
        Ok(Self {
            operand1: op1,
            operand2: None,
            rotation: shift,
        })
    }
}
impl Parse for SetCFlag {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "setcflag" {
            return Err(input.error("Expected setcflag"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op1: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let op2: Operand = content.parse()?;

        let _: Token![,] = content.parse()?;

        let (sub, carry) = if content.peek(Ident) {
            // Now we can support ADC, SUB, SBC, ADD
            let ident: Ident = content.parse()?;
            let f = Lit::Bool(syn::LitBool {
                value: false,
                span: ident.span(),
            });
            let t = Lit::Bool(syn::LitBool {
                value: true,
                span: ident.span(),
            });
            let ident = ident.to_string();
            match ident.to_lowercase().as_str() {
                "adc" => (f, t),
                "sub" => (t, f),
                "sbc" => (t.clone(), t),
                "add" => (f.clone(), f),
                _ => return Err(input.error("Previous value must be adc, sub, sbc or add")),
            }
        } else {
            let sub: Lit = content.parse()?;

            let _: Token![,] = content.parse()?;
            let carry: Lit = content.parse()?;
            (sub, carry)
        };

        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self {
            operand1: op1,
            operand2: op2,
            sub,
            carry,
        })
    }
}
impl Parse for SetVFlag {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "setvflag" {
            return Err(input.error("Expected setvflag"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op1: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let op2: Operand = content.parse()?;

        let _: Token![,] = content.parse()?;

        let (sub, carry) = if content.peek(Ident) {
            // Now we can support ADC, SUB, SBC, ADD
            let ident: Ident = content.parse()?;
            let f = Lit::Bool(syn::LitBool {
                value: false,
                span: ident.span(),
            });
            let t = Lit::Bool(syn::LitBool {
                value: true,
                span: ident.span(),
            });
            let ident = ident.to_string();
            match ident.to_lowercase().as_str() {
                "adc" => (f, t),
                "sub" => (t, f),
                "sbc" => (t.clone(), t),
                "add" => (f.clone(), f),
                _ => return Err(input.error("Previous value must be adc, sub, sbc or add")),
            }
        } else {
            let sub: Lit = content.parse()?;

            let _: Token![,] = content.parse()?;
            let carry: Lit = content.parse()?;
            (sub, carry)
        };

        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self {
            operand1: op1,
            operand2: op2,
            sub,
            carry,
        })
    }
}

impl Parse for Ror {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "ror" {
            return Err(input.error("ror"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let n = content.parse()?;
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self { operand: op, n })
    }
}

impl Parse for Sra {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "sra" {
            return Err(input.error("sra"));
        }
        input.advance_to(&speculative);
        let content;
        syn::parenthesized!(content in input);
        let op: Operand = content.parse()?;
        let _: Token![,] = content.parse()?;
        let n = content.parse()?;
        if !content.is_empty() {
            return Err(content.error("Too many arguments"));
        }
        Ok(Self { operand: op, n })
    }
}

impl Parse for Ite {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "ite" {
            return Err(input.error("ite"));
        }
        let _: Ident = input.parse()?;

        let inner;
        parenthesized!(inner in input);

        let lhs = inner.parse()?;

        let operation = inner.parse()?;

        let rhs = inner.parse()?;

        let _: Token![,] = inner.parse()?;
        let braced;
        braced!(braced in inner);
        let then = braced
            .parse_terminated(IRExpr::parse, Token![;])?
            .into_iter()
            .collect::<Vec<_>>();
        let _: Token![,] = inner.parse()?;
        let braced;
        braced!(braced in inner);
        let otherwise = braced
            .parse_terminated(IRExpr::parse, Token![;])?
            .into_iter()
            .collect::<Vec<_>>();
        Ok(Self {
            lhs,
            operation,
            rhs,
            then,
            otherwise,
            comparison_type: None,
        })
    }
}

impl Parse for Abort {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        let ident: Ident = speculative.parse()?;
        if ident.to_string().to_lowercase().as_str() != "abort" {
            return Err(input.error("abort"));
        }
        let _: Ident = input.parse()?;

        let inner;
        parenthesized!(inner in input);
        let inner: TokenStream = inner.parse()?;
        Ok(Self { inner })
    }
}

impl Parse for Abs {
    fn parse(input: ParseStream) -> Result<Self> {
        let _: Token![|] = input.parse()?;
        let id: Operand = input.parse()?;
        let _: Token![|] = input.parse()?;
        Ok(Self { operand: id })
    }
}

impl Parse for Cast {
    fn parse(input: ParseStream) -> Result<Self> {
        let id: Ident = input.parse()?;
        if id.to_string().to_lowercase() != "cast" {
            return Err(syn::Error::new(id.span(), "Expected cast"));
        }

        let content;
        syn::parenthesized!(content in input);
        let id = content.parse()?;
        let _: Token![,] = content.parse()?;
        let ty: Type = content.parse()?;
        Ok(Self {
            operand: id,
            target_type: ty,
        })
    }
}

impl Parse for Sqrt {
    fn parse(input: ParseStream) -> Result<Self> {
        let id: Ident = input.parse()?;
        if id.to_string().to_lowercase() != "sqrt" {
            return Err(syn::Error::new(id.span(), "Expected sqrt"));
        }

        let content;
        syn::parenthesized!(content in input);
        let id = content.parse()?;
        Ok(Self { operand: id })
    }
}

impl Parse for IsFinite {
    fn parse(input: ParseStream) -> Result<Self> {
        let id: Ident = input.parse()?;
        if id.to_string().to_lowercase() != "isfinite" {
            return Err(syn::Error::new(id.span(), "Expected isfinite"));
        }

        let content;
        syn::parenthesized!(content in input);
        let id = content.parse()?;
        Ok(Self { operand: id })
    }
}

impl Parse for IsNaN {
    fn parse(input: ParseStream) -> Result<Self> {
        let id: Ident = input.parse()?;
        if id.to_string().to_lowercase() != "isnan" {
            return Err(syn::Error::new(id.span(), "Expected isnan"));
        }

        let content;
        syn::parenthesized!(content in input);
        let id = content.parse()?;
        Ok(Self { operand: id })
    }
}

impl Parse for IsNormal {
    fn parse(input: ParseStream) -> Result<Self> {
        let id: Ident = input.parse()?;
        if id.to_string().to_lowercase() != "isnormal" {
            return Err(syn::Error::new(id.span(), "Expected isnormal"));
        }

        let content;
        syn::parenthesized!(content in input);
        let id = content.parse()?;
        Ok(Self { operand: id })
    }
}

impl Parse for RoundingMode {
    fn parse(input: ParseStream) -> Result<Self> {
        let id: Ident = input.parse()?;
        if id.to_string().to_lowercase() == "tozero" {
            return Ok(Self::TiesTowardZero);
        }

        if id.to_string().to_lowercase() == "awayfromzero" {
            return Ok(Self::TiesToAway);
        }

        if id.to_string().to_lowercase() == "toeven" {
            return Ok(Self::TiesToEven);
        }

        if id.to_string().to_lowercase() == "topositive" {
            return Ok(Self::TiesTowardPositive);
        }
        if id.to_string().to_lowercase() == "tonegative" {
            return Ok(Self::TiesTowardNegative);
        }
        if id.to_string().to_lowercase() == "exact" {
            return Ok(Self::Exact);
        }
        Ok(Self::Runtime(id))
    }
}

impl Parse for Log {
    fn parse(input: ParseStream) -> Result<Self> {
        let f: Ident = input.parse()?;
        let call_site = f.span();
        let level = match f.to_string().to_lowercase().as_str() {
            "info" => LogLevel::Info,
            "debug" => LogLevel::Debug,
            "warn" => LogLevel::Warn,
            "error" => LogLevel::Error,
            "trace" => LogLevel::Trace,
            _ => return Err(syn::Error::new(call_site, "Expected a log level")),
        };

        let content;
        syn::parenthesized!(content in input);

        let meta: String = match content.peek(LitStr) {
            true => {
                let lit: LitStr = content.parse()?;
                let _: Token![,] = content.parse()?;
                lit.value()
            }
            false => "".to_string(),
        };

        let arg: Operand = content.parse()?;

        Ok(Self {
            level,
            operand: arg,
            call_site,
            meta,
        })
    }
}

impl Parse for MultiplyAndAccumulate {
    fn parse(input: ParseStream) -> Result<Self> {
        let id: Ident = input.parse()?;
        if id.to_string().to_lowercase() != "fma" {
            return Err(syn::Error::new(id.span(), "Expected isfinite"));
        }

        let content;
        syn::parenthesized!(content in input);
        let lhs = content.parse()?;
        let _: Token![,] = content.parse()?;
        let rhs = content.parse()?;
        let _: Token![,] = content.parse()?;
        let addend = content.parse()?;
        Ok(Self { lhs, rhs, addend })
    }
}
