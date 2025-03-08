//! Defines the parsing rules for the [`ast`](crate::ast).

pub mod function;
pub mod operand;
pub mod operation;

use syn::{
    parenthesized,
    parse::{discouraged::Speculative, Parse, ParseStream},
    Expr,
    Ident,
    Result,
    Token,
};

use self::operations::{BinOp, BinaryOperation};
use crate::ast::{operand::Operand, *};

impl IR {
    fn parse_internal(input: ParseStream) -> Result<Self> {
        // Expected syntax : ret.extend[ .. ]
        let speculative = input.fork();
        let ret: Option<Ident> = match Ident::parse(&speculative) {
            Ok(ret) => match syn::token::Dot::parse(&speculative) {
                Ok(_) => {
                    input.advance_to(&speculative);

                    let token: Ident = input.parse()?;
                    if token.to_string().as_str() != "extend" {
                        return Err(input.error("Expected extend"));
                    }
                    Some(ret)
                }
                _ => None,
            },
            _ => None,
        };
        let content;
        syn::bracketed!(content in input);

        let mut extensions: Vec<Statement> = vec![];
        while !content.is_empty() {
            extensions.push(content.parse()?);
        }

        let ret = Self {
            ret,
            extensions: extensions.into_iter().collect(),
        };
        Ok(ret)
    }
}
impl Parse for IR {
    fn parse(input: ParseStream) -> Result<Self> {
        let ret = match Self::parse_internal(input) {
            Ok(val) => val,
            Err(e) => {
                return Err(e);
            }
        };
        Ok(ret)
    }
}
impl Parse for Statement {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![if]) {
            let _: Token![if] = input.parse()?;
            // Simply require parenthesise here, this is a bit of a "fulhack"
            // but it works for now
            let content;
            parenthesized!(content in input);

            let e: Expr = content.parse()?;
            if !content.is_empty() {
                return Err(content.error("Too many input arguments"));
            }
            let content;
            syn::braced!(content in input);

            let mut happy_case: Box<Vec<Statement>> = Box::default();
            while !content.is_empty() {
                let further_values: Statement = content.parse()?;
                happy_case.push(further_values);
            }
            let sad_case = if input.peek(Token![else]) {
                let _: Token![else] = input.parse()?;
                let content;
                syn::braced!(content in input);
                let mut sad_case: Box<Vec<Statement>> = Box::default();
                while !content.is_empty() {
                    let further_values: Statement = content.parse()?;
                    sad_case.push(further_values);
                }
                Some(sad_case)
            } else {
                None
            };
            return Ok(Self::If(e, happy_case, sad_case));
        }
        if input.peek(Token![for]) {
            let _: Token![for] = input.parse()?;
            let var: Ident = input.parse()?;
            let _: Token![in] = input.parse()?;
            let e: Expr = input.parse()?;
            let content;
            syn::braced!(content in input);
            let mut block: Box<Vec<Statement>> = Box::default();
            while !content.is_empty() {
                let further_values: Statement = content.parse()?;
                block.push(further_values);
            }
            return Ok(Self::For(var, e, block));
        }

        let mut ret: Vec<Box<IRExpr>> = vec![];

        while !input.is_empty() {
            if input.peek(Token![if]) | input.peek(Token![for]) {
                break;
            }
            let speculative = input.fork();
            match speculative.parse() {
                Ok(val) => {
                    let _: syn::token::Semi = match speculative.parse() {
                        Ok(t) => t,
                        Err(_) => return Err(speculative.error("Expected `;`")),
                    };
                    input.advance_to(&speculative);
                    ret.push(Box::new(val));
                }
                Err(e) => {
                    return Err(e);
                }
            }
        }
        Ok(Self::Exprs(ret))
    }
}

impl Parse for IRExpr {
    fn parse(input: ParseStream) -> Result<Self> {
        let speculative = input.fork();
        if let Ok(unop) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::UnOp(unop));
        }

        let speculative = input.fork();
        if let Ok(assign) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Assign(assign));
        }

        // Things like a |= 1
        'a: {
            let speculative = input.fork();
            let dest: Operand = match speculative.parse() {
                Ok(val) => val,
                _ => break 'a,
            };
            let operation: BinaryOperation = match speculative.parse() {
                Ok(val) => val,
                _ => break 'a,
            };
            let _eq: Token![=] = match speculative.parse() {
                Ok(val) => val,
                _ => return Err(input.error("Expected =")),
            };
            let operand: Operand = match speculative.parse() {
                Ok(val) => val,
                _ => return Err(input.error("Expected operand")),
            };
            if !speculative.peek(Token![;]) {
                return Err(input.error("Expected ;"));
            }
            input.advance_to(&speculative);
            return Ok(Self::BinOp(BinOp {
                dest: dest.clone(),
                op: operation,
                lhs: dest,
                rhs: operand,
            }));
        }

        let speculative = input.fork();
        if let Ok(res) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::BinOp(res));
        }

        let speculative = input.fork();
        if let Ok(res) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Jump(res));
        }

        let speculative = input.fork();
        if let Ok(func) = speculative.parse() {
            input.advance_to(&speculative);
            return Ok(Self::Function(func));
        }
        Err(input.error("Expected a valid IRExpr here"))
    }
}
