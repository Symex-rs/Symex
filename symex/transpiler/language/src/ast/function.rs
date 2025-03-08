//! Defines all AST types that concern functions.
use proc_macro2::TokenStream;
use syn::{Expr, Ident, Lit};

use super::{
    operand::{IdentOperand, Operand},
    operations::{BinOp, BinaryOperation, CompareOperation},
    IRExpr,
};

#[derive(Debug, Clone)]
/// Enumerates all supported function types
pub enum Function {
    /// A function call that is not intrinsic to the transpiler.
    ///
    /// This can be defined in normal rust code.
    Ident(Ident, Vec<Expr>),
    /// An intrinsic function.
    ///
    /// These are defined and expanded at compile-time.
    /// This allows for expansion of meta instructions such as
    /// [`Signed`].
    Intrinsic(Box<Intrinsic>),
}

/// A simple representation of a normal rust function call
///
/// These refer to functions outside of the macro call.
/// For these we simply ignore them and re call them in
/// the output.
#[derive(Debug, Clone)]
pub struct FunctionCall {
    /// The name of the function called.
    pub ident: Function,
    /// The arguments passed to the function.
    pub args: Vec<Expr>,
}

// TODO! Implement remaining set flag things
#[derive(Debug, Clone)]
/// Enumerates all of the built in functions
///
/// These are ways of calling [`general_assembly`]
/// instructions that are not arithmetic operations
pub enum Intrinsic {
    /// Zero extends the operand with zeros from the
    /// bit specified and onward.
    ZeroExtend(ZeroExtend),

    /// Extends the operand with the value at the specified bit
    /// and onwards.
    SignExtend(SignExtend),

    /// Resizes the operand to the specified number of bits.
    Resize(Resize),

    /// Sets the Negative flag for the specified operand.
    SetNFlag(SetNFlag),

    /// Sets the Zero flag for the specified operand.
    SetZFlag(SetZFlag),

    /// One time use operand that is a
    /// [`AddressInLocal`](general_assembly::operand::Operand::AddressInLocal).
    LocalAddress(LocalAddress),

    /// Sets the overflow flag based on the operands and the operation applied.
    SetVFlag(SetVFlag),

    /// Sets the carry flag based on the operands and the operations applied.
    SetCFlag(SetCFlag),

    /// Sets the carry flag based on the operands and the operations applied.
    SetCFlagRot(SetCFlagRot),

    /// One time use operand that is a
    /// [`Flag`](general_assembly::operand::Operand::Flag)
    Flag(Flag),

    /// One time use operand that is a
    /// [`Register`](general_assembly::operand::Operand::Register)
    Register(Register),

    /// Rotates the operand right the number of steps specified.
    Ror(Ror),

    /// Shifts the operand right maintaining the sign of it.
    Sra(Sra),

    /// Converts the inner [`IRExpr`](crate::ast::IRExpr) to its signed
    /// equivalent.
    Signed(Signed),

    /// Conditionally runs a set of operations.
    Ite(Ite),

    /// Aborts the current path returning a message to the user.
    Abort(Abort),
    // /// Saturates the contained operation.
    //Saturate(Saturate),
}

// ===============================================
//              Definition of intrinsics
// ===============================================

#[derive(Debug, Clone)]
/// A jump instruction.
pub struct Jump {
    /// Where to jump to.
    pub target: Operand,
    /// What condition to use.
    pub condition: Option<Expr>,
}

#[derive(Debug, Clone)]
/// Converts the [`BinOp`](super::operations::Operation) contained with to
/// its signed equivalent.
pub struct Signed {
    /// The lhs of the operation.
    pub op1: Operand,
    /// The rhs of the operation.
    pub op2: Operand,
    /// The operation to apply.
    pub operation: BinaryOperation,
}

#[derive(Debug, Clone)]
/// Resizes the operand to the specified number of bits.
pub struct Resize {
    /// Operand to resize.
    pub operand: Operand,
    /// Target number of bits.
    pub bits: Expr,
}

#[derive(Debug, Clone)]
/// Zero extends the operand to the machine word size.
pub struct ZeroExtend {
    /// Operand to resize.
    pub operand: Operand,
    /// From which bit to zero extend.
    pub bits: Expr,
}

#[derive(Debug, Clone)]
/// Sign extends the operand to the machine word size.
pub struct SignExtend {
    /// Operand to sign extend.
    pub operand: Operand,
    /// The bit that contains the sign.
    pub sign_bit: Expr,
    /// The size of the target value in bits.
    pub target_size: Expr,
}

#[derive(Debug, Clone)]
/// Gets/Sets the specified flag.
pub struct Flag {
    /// The name of the flag.
    pub name: Lit,
}

#[derive(Debug, Clone)]
/// Gets/Sets the specified register.
pub struct Register {
    /// The name of the register.
    pub name: Lit,
}

#[derive(Debug, Clone)]
/// Reads/Writes to an address in the local scope.
pub struct LocalAddress {
    /// Name of the local variable.
    pub name: Lit,
    /// Number of bits to read from the address.
    pub bits: Lit,
}

#[derive(Debug, Clone)]
/// Jumps if the condition is met.
pub struct ConditionalJump {
    /// Where to jump to.
    pub operand: Operand,
    /// Condition that needs to be met.
    pub condition: Ident,
}

#[derive(Debug, Clone)]
/// Sets the Negative flag for the specified operand.
pub struct SetNFlag {
    /// The operand for which the flag will be set.
    pub operand: Operand,
}

#[derive(Debug, Clone)]
/// Sets the Zero flag for the specified operand.
pub struct SetZFlag {
    /// The operand for which the flag will be set.
    pub operand: Operand,
}

// TODO! Remove this once it is not needed any more.
#[derive(Debug, Clone, PartialEq)]
#[allow(missing_docs)]
pub enum Rotation {
    Lsl,
    Rsl,
    Rsa,
    Ror,
    // Rrx
}
// TODO! Remove this once it is not needed any more.
#[derive(Debug, Clone)]
/// Sets the carry flag for the specified operation.
pub struct SetCFlagRot {
    /// The lhs of the operation.
    pub operand1: Operand,
    /// The rhs of the operation.
    pub operand2: Option<Operand>,
    /// The operation to set the flag for.
    pub rotation: Rotation,
}

#[derive(Debug, Clone)]
/// Sets the carry flag for the specified operation.
pub struct SetCFlag {
    /// The lhs of the operation.
    pub operand1: Operand,
    /// The rhs of the operation.
    pub operand2: Operand,
    /// Whether or not the operation was a subtract.
    pub sub: Lit,
    /// Whether or not the operation used the carry flag.
    pub carry: Lit,
}

#[derive(Debug, Clone)]
/// Sets the overflow flag for the specified operation.
pub struct SetVFlag {
    /// The lhs of the operation.
    pub operand1: Operand,
    /// The rhs of the operation.
    pub operand2: Operand,
    /// Whether or not the operation was a subtract.
    pub sub: Lit,
    /// Whether or not the operation used the carry flag.
    pub carry: Lit,
}

#[derive(Debug, Clone)]
/// Rotates the operand right by the specified number of steps.
pub struct Ror {
    /// Operand to rotate.
    pub operand: Operand,
    /// How far to rotate.
    pub n: Expr,
}

#[derive(Debug, Clone)]
/// Shifts the operand right maintaining the sign.
pub struct Sra {
    /// Operand to shift.
    pub operand: Operand,
    /// How far to shift.
    pub n: Expr,
}

#[derive(Debug, Clone)]
/// Conditionally runs a set of operations.
pub struct Ite {
    /// The left hand side of the comparison operation.
    pub lhs: IdentOperand,
    /// The comparison operation to apply.
    pub operation: CompareOperation,
    /// The right hand side of the comparison operation.
    pub rhs: IdentOperand,
    /// Executes if the comparison returns true.
    pub then: Vec<IRExpr>,
    /// Executes if the comparison returns false.
    pub otherwise: Vec<IRExpr>,
}

#[derive(Debug, Clone)]
/// Conditionally aborts the current path.
pub struct Abort {
    /// The message to pass to format!.
    pub inner: TokenStream,
}
