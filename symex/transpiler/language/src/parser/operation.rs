//! Defines parsing rules for the ast
//! [`Operations`](crate::ast::operations::Operation).
use syn::{
    parse::{discouraged::Speculative, Parse, ParseStream, Result},
    Ident,
    Token,
};

use crate::ast::{
    operand::Operand,
    operations::{Assign, BinOp, BinaryOperation, CompareOperation, UnOp, UnaryOperation},
};
impl Parse for Assign {
    fn parse(input: ParseStream) -> Result<Self> {
        let dest: Operand = input.parse()?;

        let _: Token![=] = input.parse()?;
        let rhs: Operand = input.parse()?;
        if !input.peek(Token![;]) {
            return Err(input.error("Expected ;"));
        }
        Ok(Self { dest, rhs })
    }
}
impl Parse for UnOp {
    fn parse(input: ParseStream) -> Result<Self> {
        let dest: Operand = input.parse()?;
        let _: Token![=] = input.parse()?;
        let op: UnaryOperation = input.parse()?;
        let rhs: Operand = input.parse()?;
        if !input.peek(syn::token::Semi) {
            return Err(input.error("Expected ;"));
        }
        Ok(Self { dest, op, rhs })
    }
}
impl Parse for BinOp {
    fn parse(input: ParseStream) -> Result<Self> {
        let dest: Operand = input.parse()?;
        let _: Token![=] = input.parse()?;

        let lhs: Operand = input.parse()?;

        let op: BinaryOperation = input.parse()?;

        let rhs: Operand = input.parse()?;
        if !input.peek(syn::token::Semi) {
            return Err(input.error("Expected ;"));
        }
        Ok(Self { dest, op, lhs, rhs })
    }
}
impl Parse for UnaryOperation {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![!]) {
            let _: Token![!] = input.parse()?;
            return Ok(Self::BitwiseNot);
        }
        Err(input.error("Expected unary op"))
    }
}
impl Parse for BinaryOperation {
    fn parse(input: ParseStream) -> Result<Self> {
        use BinaryOperation::*;
        if input.peek(Token![+]) {
            let _: Token![+] = input.parse()?;
            return Ok(Add);
        }
        if input.peek(Token![-]) {
            let _: Token![-] = input.parse()?;
            return Ok(Sub);
        }
        if input.peek(Ident) {
            let speculative = input.fork();
            let ident: Ident = speculative.parse()?;
            if ident.to_string().to_lowercase() == "adc" {
                input.advance_to(&speculative);
                return Ok(AddWithCarry);
            }
        }
        if input.peek(syn::token::Slash) {
            let _: syn::token::Slash = input.parse()?;
            return Ok(Self::UDiv);
        }
        if input.peek(Ident) {
            let speculative = input.fork();
            let ident: Ident = speculative.parse()?;
            if ident.to_string().to_lowercase() == "sdiv" {
                input.advance_to(&speculative);
                return Ok(SDiv);
            }
        }
        if input.peek(Ident) {
            let speculative = input.fork();
            let ident: Ident = speculative.parse()?;
            if ident.to_string().to_lowercase() == "sadd" {
                input.advance_to(&speculative);
                return Ok(SAdd);
            }
        }
        if input.peek(Ident) {
            let speculative = input.fork();
            let ident: Ident = speculative.parse()?;
            if ident.to_string().to_lowercase() == "sadds" {
                input.advance_to(&speculative);
                return Ok(SAdds);
            }
        }
        if input.peek(Ident) {
            let speculative = input.fork();
            let ident: Ident = speculative.parse()?;
            if ident.to_string().to_lowercase() == "ssub" {
                input.advance_to(&speculative);
                return Ok(SAdd);
            }
        }
        if input.peek(Ident) {
            let speculative = input.fork();
            let ident: Ident = speculative.parse()?;
            if ident.to_string().to_lowercase() == "ssubs" {
                input.advance_to(&speculative);
                return Ok(SAdds);
            }
        }
        if input.peek(Token![*]) {
            let _: Token![*] = input.parse()?;
            return Ok(Self::Mul);
        }
        if input.peek(Token![&]) {
            let _: Token![&] = input.parse()?;
            return Ok(Self::BitwiseAnd);
        }
        if input.peek(Token![|]) {
            let _: Token![|] = input.parse()?;
            return Ok(Self::BitwiseOr);
        }
        if input.peek(Token![^]) {
            let _: Token![^] = input.parse()?;
            return Ok(Self::BitwiseXor);
        }
        if input.peek(Token![>>]) {
            let _: Token![>>] = input.parse()?;
            return Ok(Self::LogicalRightShift);
        }
        if input.peek(Token![<<]) {
            let _: Token![<<] = input.parse()?;
            return Ok(Self::LogicalLeftShift);
        }
        if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            // Revisit this later
            if ident.to_string().to_lowercase() == "asr" {
                return Ok(ArithmeticRightShift);
            } else {
                todo!()
                // compile_error!("Expected \"Adc\" found
                // {:}",ident.to_string());
            }
        }
        Err(input.error("Expected operation"))
    }
}

impl Parse for CompareOperation {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![==]) {
            let _: Token![==] = input.parse()?;
            return Ok(Self::Eq);
        }
        if input.peek(Token![!=]) {
            let _: Token![!=] = input.parse()?;
            return Ok(Self::Neq);
        }
        if input.peek(Token![>=]) {
            let _: Token![>=] = input.parse()?;
            return Ok(Self::Geq);
        }
        if input.peek(Token![<=]) {
            let _: Token![<=] = input.parse()?;
            return Ok(Self::Leq);
        }
        if input.peek(Token![>]) {
            let _: Token![>] = input.parse()?;
            return Ok(Self::Gt);
        }
        if input.peek(Token![<]) {
            let _: Token![<] = input.parse()?;
            return Ok(Self::Lt);
        }

        Err(input.error("Expected a comparison operation"))
    }
}
