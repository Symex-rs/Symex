//! Defines all AST types that concern functions.
use proc_macro2::{Span, TokenStream};
use syn::{Expr, Ident, Lit};

use super::{
    operand::{Operand, Type},
    operations::CompareOperation,
    IRExpr,
};

#[derive(Debug, Clone, PartialEq)]
/// Enumerates all supported function types
pub enum Function {
    /// A function call that is not intrinsic to the transpiler.
    ///
    /// This can be defined in normal rust code.
    Ident(Ident, Vec<Expr>),
    /// An intrinsic function.
    ///
    /// These are defined and expanded at compile-time.
    Intrinsic(Box<Intrinsic>),
}

/// A simple representation of a normal rust function call
///
/// These refer to functions outside of the macro call.
/// For these we simply ignore them and re call them in
/// the output.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
    /// The name of the function called.
    pub ident: Function,
    /// The arguments passed to the function.
    pub args: Vec<Expr>,
}

// TODO! Implement remaining set flag things
#[derive(Debug, Clone, PartialEq)]
/// Enumerates all of the built in functions
///
/// These are ways of calling [`general_assembly`]
/// instructions that are not arithmetic operations
#[allow(clippy::large_enum_variant)]
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

    /// Conditionally runs a set of operations.
    Ite(Ite),

    /// Aborts the current path returning a message to the user.
    Abort(Abort),

    /// Computes the absolute value of a value.
    Abs(Abs),
    // /// Determines whether or not a fp value is normal.
    //IsNormal(IsNormal),
    /// Computes the square root of a number.
    Sqrt(Sqrt),

    /// Casts the operand to another type.
    Cast(Cast),

    /// Logs a message to the terminal.
    Log(Log),

    // FP specific
    /// Checks if a value is NaN.
    IsNaN(IsNaN),
    /// Checks if a value is normal.
    IsNormal(IsNormal),
    /// Checks if a value is finite.
    IsFinite(IsFinite),

    /// Multiplies two numbers and adds the third number to the result.
    MultiplyAndAccumulate(MultiplyAndAccumulate),
    // Saturate(Saturate),
}

// ===============================================
//              Definition of intrinsics
// ===============================================

#[derive(Debug, Clone, PartialEq)]
/// A jump instruction.
pub struct Jump {
    /// Where to jump to.
    pub target: Operand,
    /// What condition to use.
    pub condition: Option<Expr>,
}
#[derive(Debug, Clone, PartialEq)]
/// Resizes the operand to the specified number of bits.
pub struct Resize {
    /// Operand to resize.
    pub operand: Operand,
    /// Target number of bits.
    pub target_ty: crate::ast::operand::Type,
    /// Rounding mode.
    pub rm: Option<RoundingMode>,
}

#[derive(Debug, Clone, PartialEq)]
/// Zero extends the operand to the machine word size.
pub struct ZeroExtend {
    /// Operand to resize.
    pub operand: Operand,
    /// From which bit to zero extend.
    pub bits: u32,
}

#[derive(Debug, Clone, PartialEq)]
/// Sign extends the operand to the machine word size.
pub struct SignExtend {
    /// Operand to sign extend.
    pub operand: Operand,
    /// The bit that contains the sign.
    pub sign_bit: Expr,
    /// The size of the target value in bits.
    pub target_size: u32,
}

#[derive(Debug, Clone, PartialEq)]
/// Gets/Sets the specified flag.
pub struct Flag {
    /// The name of the flag.
    pub name: Lit,
}

#[derive(Debug, Clone, PartialEq)]
/// Gets/Sets the specified register.
pub struct Register {
    /// The name of the register.
    pub name: Lit,
    /// The source register type.
    ///
    /// This is useful if one want to read or write a core register as a
    /// floating point value.
    pub source_type: Option<crate::ast::operand::Type>,
}

#[derive(Debug, Clone, PartialEq)]
/// Reads/Writes to an address in the local scope.
pub struct LocalAddress {
    /// Name of the local variable.
    pub name: Ident,
    /// Number of bits to read from the address.
    pub bits: u32,
}

#[derive(Debug, Clone, PartialEq)]
/// Jumps if the condition is met.
pub struct ConditionalJump {
    /// Where to jump to.
    pub operand: Operand,
    /// Condition that needs to be met.
    pub condition: Ident,
}

#[derive(Debug, Clone, PartialEq)]
/// Sets the Negative flag for the specified operand.
pub struct SetNFlag {
    /// The operand for which the flag will be set.
    pub operand: Operand,
}

#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
/// Sets the carry flag for the specified operation.
pub struct SetCFlagRot {
    /// The lhs of the operation.
    pub operand1: Operand,
    /// The rhs of the operation.
    pub operand2: Option<Operand>,
    /// The operation to set the flag for.
    pub rotation: Rotation,
}

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
/// Rotates the operand right by the specified number of steps.
pub struct Ror {
    /// Operand to rotate.
    pub operand: Operand,
    /// How far to rotate.
    pub n: Expr,
}

#[derive(Debug, Clone, PartialEq)]
/// Computes the absolute value of an operand.
pub struct Abs {
    /// Operand to compute the absolute value of.
    pub operand: Operand,
}

#[derive(Debug, Clone, PartialEq)]
/// Shifts the operand right maintaining the sign.
pub struct Sra {
    /// Operand to shift.
    pub operand: Operand,
    /// How far to shift.
    pub n: Expr,
}

#[derive(Debug, Clone, PartialEq)]
/// Conditionally runs a set of operations.
pub struct Ite {
    /// The left hand side of the comparison operation.
    pub lhs: Operand,
    /// The comparison operation to apply.
    pub operation: CompareOperation,
    /// The right hand side of the comparison operation.
    pub rhs: Operand,
    /// Executes if the comparison returns true.
    pub then: Vec<IRExpr>,
    /// Executes if the comparison returns false.
    pub otherwise: Vec<IRExpr>,
    /// The type of the comparison operands.
    pub comparison_type: Option<crate::ast::operand::Type>,
}

#[derive(Debug, Clone)]
/// Conditionally aborts the current path.
pub struct Abort {
    /// The message to pass to format!.
    pub inner: TokenStream,
}

/// Computes the square root of an operand.
#[derive(Debug, Clone, PartialEq)]
pub struct Sqrt {
    /// The operand to compute the square root of.
    pub operand: Operand,
}

/// Checks if a value is NaN.
#[derive(Debug, Clone, PartialEq)]
pub struct IsNaN {
    /// The operand to check if it is NaN.
    pub operand: Operand,
}

/// Checks if a value is Normal.
#[derive(Debug, Clone, PartialEq)]
pub struct IsNormal {
    /// The operand to check if it is Normal.
    pub operand: Operand,
}

/// Checks if a value is Finite.
#[derive(Debug, Clone, PartialEq)]
pub struct IsFinite {
    /// The operand to check if it is Finite.
    pub operand: Operand,
}

/// Casts an operand in to a target type.
#[derive(Debug, Clone, PartialEq)]
pub struct Cast {
    /// The operand to cast to the target type.
    pub operand: Operand,
    /// The target type to cast to.
    pub target_type: Type,
}

/// Multiplies and accumulates the three operands
#[derive(Debug, Clone, PartialEq)]
pub struct MultiplyAndAccumulate {
    /// The lhs of the multiplication.
    pub lhs: Operand,
    /// The rhs of the multiplication.
    pub rhs: Operand,
    /// The addend to the multiplication.
    pub addend: Operand,
}

impl PartialEq for Abort {
    fn eq(&self, other: &Self) -> bool {
        self.inner.to_string() == other.inner.to_string()
    }
}

#[derive(Debug, Clone, PartialEq)]
/// Enumerates all of the IEEE754 rounding modes.
pub enum RoundingMode {
    /// Rounds towards even numbers.
    TiesToEven,
    /// Round away from zero.
    TiesToAway,
    /// Rounds towards zero.
    TiesTowardZero,
    /// Round towards positive values.
    TiesTowardPositive,
    /// Rounds towards negative values.
    TiesTowardNegative,

    /// ?
    Exact,

    /// A rounding mode determined at runtime.
    Runtime(Ident),
}

#[derive(Debug, Clone)]
/// A logging message.
pub struct Log {
    /// The log level of the message.
    pub level: LogLevel,
    /// The operand to print.
    pub operand: Operand,
    /// Optional meta data.
    pub meta: String,
    /// Where the log call was made.
    pub call_site: Span,
}

impl PartialEq for Log {
    fn eq(&self, other: &Self) -> bool {
        self.operand == other.operand
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
/// Enumerates all of the supported log levels.
pub enum LogLevel {
    /// Most fine-grain logging.
    Trace,
    /// Second most fine-grain logging.
    Info,
    /// Useful for debugging.
    Debug,
    /// Warnings
    Warn,
    /// Errors.
    Error,
}
