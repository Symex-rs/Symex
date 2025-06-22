//! Defines the an intermediate language used to define a vector of
//! [`Operation`](general_assembly::operation::Operation)s.

#![deny(clippy::all)]
#![deny(missing_docs)]
#![deny(rustdoc::all)]
#![allow(clippy::match_like_matches_macro)]

pub mod ast;
pub mod ga_backend;
pub mod parser;
pub mod type_checker;

use std::collections::HashMap;

use ast::operand::{ExprOperand, FieldExtract, Operand, Type};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote_spanned, ToTokens};
use syn::Ident;

/// All possible errors that can occur when transpiling against some target.
#[derive(Debug)]
pub enum Error {
    /// The program tried to access a variable that did not exist yet.
    UseBeforeDeclaration(String),

    /// Declared a value that is never used.
    UnusedDeclartion(Ident),

    /// The user requested a non supported instruction.
    UnsupportedInstruction(String),

    /// An internal error occurred.
    InternalError(String),
}
impl Error {
    /// Returns the span of the error.
    pub fn span(&self) -> Span {
        match self {
            Self::UnusedDeclartion(i) => i.span(),
            _ => Span::call_site(),
        }
    }

    /// Returns this as a compile error.
    pub fn compile_error(&self) -> TokenStream {
        let str = match self {
            Self::UnusedDeclartion(id) => format!("Unused declaration: {id}"),
            _ => format!("Self {self:?}"),
        };
        quote_spanned! {self.span() => compile_error!(#str)}
    }
}

#[derive(Debug)]
struct TranspilerState<T: std::fmt::Debug> {
    to_declare: Vec<Vec<(Ident, Type)>>,

    to_insert_above: Vec<T>,
    usage_counter: Vec<HashMap<String, (Ident, u32)>>,
    intermediate_counter: u32,
}

trait Compile {
    type Output: std::fmt::Debug;
    fn compile(&self, state: &mut TranspilerState<Self::Output>) -> Result<Self::Output, Error>;
}

#[derive(Debug, Clone)]
/// TODO: docs
pub enum TypeError {
    /// Type must be known at this point.
    TypeMustBeKnown(String, Span),

    /// Type mismatch.
    InvalidType {
        /// TODO: docs
        expected: crate::ast::operand::Type,
        /// TODO: docs
        got: crate::ast::operand::Type,
        /// The span of the operation.
        span: Span,
    },

    /// The requested operation was not valid for the specified type.
    UnsuportedOperation(String, Span),

    /// A foreign type that is not supported.
    UnsupportedType(String, Span),
}

impl TypeError {
    /// Returns this as a compile error.
    pub fn compile_error(&self) -> TokenStream {
        match self {
            Self::UnsupportedType(s, span) => {
                let str = format!("Unsupported type, {s}");
                quote_spanned! {*span => compile_error!(#str)}
            }
            Self::UnsuportedOperation(s, span) => {
                let str = format!("Unsupported operation, {s}");
                quote_spanned! {*span => compile_error!(#str)}
            }
            Self::TypeMustBeKnown(s, span) => {
                let str = format!("Type must be known, {s}");
                quote_spanned! {*span => compile_error!(#str)}
            }
            Self::InvalidType {
                expected,
                got,
                span,
            } => {
                let got = format!("{got:?}");
                let expected = format!("{expected:?}");
                let str = format!("Invalid type, expected {expected} but got {got}");
                quote_spanned! {*span => compile_error!(#str)}
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
/// TODO: docs
pub struct TypeCheckMeta {
    lookup: HashMap<Ident, crate::ast::operand::Type>,
}
impl TypeCheckMeta {
    /// TODO: docs
    pub fn new() -> Self {
        Self {
            lookup: HashMap::new(),
        }
    }
}

/// TODO: docs
pub trait TypeCheck {
    /// TODO: Docs
    fn type_check(
        &mut self,
        meta: &mut TypeCheckMeta,
    ) -> Result<Option<crate::ast::operand::Type>, TypeError>;
}

impl<T: std::fmt::Debug> TranspilerState<T> {
    fn new() -> Self {
        Self {
            to_declare: vec![Vec::new()],
            to_insert_above: Vec::new(),
            usage_counter: vec![HashMap::new()],
            intermediate_counter: 0,
        }
    }

    fn access_count(&self, name: &String) -> Option<u32> {
        for scope in self.usage_counter.iter() {
            if let Some(value) = scope.get(name) {
                return Some(value.1);
            }
        }
        None
    }

    /// Increments the first occurrence of that name.
    fn increment_access(&mut self, name: &String) {
        for scope in self.usage_counter.iter_mut() {
            if let Some(value) = scope.get_mut(name) {
                value.1 += 1;
            }
        }
    }

    // Exception since the naming is reasonable in this case.
    #[allow(clippy::wrong_self_convention)]
    /// Returns the variables that need to be declared.
    ///
    /// If any of the variables that need to be declared after this scope
    /// have not been used we throw an error.
    pub fn to_declare(&mut self) -> Result<Vec<(Ident, Type)>, Error> {
        let to_declare = self.to_declare.pop().expect("Invalid stack management");
        for el in to_declare.iter() {
            let key = el.0.to_string();
            match self.access_count(&key) {
                Some(value) => {
                    if value == 0 {
                        return Err(Error::UnusedDeclartion(Ident::new(&key, Span::call_site())));
                    }
                }
                None => {
                    return Err(Error::UseBeforeDeclaration(key));
                }
            }
        }
        let counter = self.usage_counter.pop().expect("Invalid stack management");
        for (_key, (id, value)) in counter.iter() {
            if *value == 0 {
                return Err(Error::UnusedDeclartion(id.clone()));
            }
        }

        Ok(to_declare)
    }

    /// Declares a new local variable.
    pub fn declare_local(&mut self, ident: Ident, ty: Type) {
        self.to_declare
            .last_mut()
            .unwrap()
            .push((ident.clone(), ty));
        self.usage_counter
            .first_mut()
            .expect("declare local borked")
            .insert(ident.to_string(), (ident, 0));
    }

    /// Accesses the variable by identifier.
    pub fn access(&mut self, ident: Ident) {
        let key = ident.to_string();
        self.increment_access(&key)
    }

    /// Accesses the variable by identifier.
    pub fn access_operand(&mut self, ident: Operand) {
        let id = match ident {
            Operand::Ident((i, _)) => i.ident,
            Operand::Expr((ExprOperand::Ident(i), _)) => i,
            Operand::Expr((ExprOperand::Literal(l), _)) => {
                Ident::new(&l.to_token_stream().to_string(), l.span())
            }
            Operand::FieldExtract((
                FieldExtract {
                    operand,
                    start: _,
                    end: _,
                    ty: _,
                },
                _,
            )) => operand,
            _ => return,
        };

        let key = id.to_string();
        self.increment_access(&key)
    }

    /// Accesses a variable by string.
    pub fn access_str(&mut self, ident: String) {
        self.increment_access(&ident)
    }

    /// Enters a new block.
    ///
    /// This creates a new nested set of local variables.
    pub fn enter_scope(&mut self) {
        self.to_declare.push(Vec::new());
        self.usage_counter.push(HashMap::new());
    }

    /// Declares a new intermediate variable.
    pub fn intermediate(&mut self, ty: Type) -> (ast::operand::IdentOperand, Type) {
        let new_ident = format_ident!("intermediate_{}", self.intermediate_counter);
        self.to_declare
            .last_mut()
            .expect("Intermediate broken")
            .push((new_ident.clone(), ty));
        self.usage_counter
            .last_mut()
            .expect("Intermediate broken")
            .insert(new_ident.clone().to_string(), (new_ident.clone(), 0));
        self.intermediate_counter += 1;
        (
            ast::operand::IdentOperand {
                define: false,
                ident: new_ident,
            },
            ty,
        )
    }
}
