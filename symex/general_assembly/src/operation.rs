//! Defines all operations that are valid in [`Symex`](../../../) General
//! Assembly language.

use crate::{
    condition::{Comparison, Condition},
    operand::Operand,
    shift::Shift,
};

/// Represents a single operation
#[derive(Debug, Clone)]
pub enum Operation {
    /// No operation
    Nop,

    /// Moves the value in the source to the destination.
    /// If source is an address it is loaded from memory
    /// and if destination is an address it is stored into memory.
    #[allow(missing_docs)]
    Move {
        destination: Operand,
        source: Operand,
    },

    /// Addition.
    ///
    /// ```ignore
    /// destination = operand1 + operand2
    /// ```
    #[allow(missing_docs)]
    Add {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Saturating Addition.
    ///
    /// ```ignore
    /// destination = operand1 + operand2
    /// ```
    #[allow(missing_docs)]
    SAdd {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
        signed: bool,
    },

    /// Add with carry.
    ///
    /// ```ignore
    /// destination = operand1 + operand2 + carry_flag
    /// ```
    #[allow(missing_docs)]
    Adc {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Subtraction.
    ///
    /// ```ignore
    /// destination = operand1 - operand2
    /// ```
    #[allow(missing_docs)]
    Sub {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Saturating subtraction.
    ///
    /// ```ignore
    /// destination = operand1 - operand2
    /// ```
    #[allow(missing_docs)]
    SSub {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
        signed: bool,
    },

    /// Multiplication.
    ///
    /// ```ignore
    /// destination = operand1 * operand2
    /// ```
    #[allow(missing_docs)]
    Mul {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Signed division.
    ///
    /// ```ignore
    /// destination = SInt(operand1) / SInt(operand2)
    /// ```
    #[allow(missing_docs)]
    SDiv {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Unsigned division.
    ///
    /// ```ignore
    /// destination = UInt(operand1) / UInt(operand2)
    /// ```
    #[allow(missing_docs)]
    UDiv {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Bitwise and.
    ///
    /// ```ignore
    /// destination = operand1 & operand2
    /// ```
    #[allow(missing_docs)]
    And {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Bitwise or.
    ///
    /// ```ignore
    /// destination = operand1 | operand2
    /// ```
    #[allow(missing_docs)]
    Or {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Bitwise exclusive or.
    ///
    /// ```ignore
    /// destination = operand1 ^ operand2
    /// ```
    #[allow(missing_docs)]
    Xor {
        destination: Operand,
        operand1: Operand,
        operand2: Operand,
    },

    /// Bitwise not.
    ///
    /// ```ignore
    /// destination = !operand
    /// ```
    #[allow(missing_docs)]
    Not {
        destination: Operand,
        operand: Operand,
    },

    /// General rotation or shift.
    Shift {
        /// Where to store the result.
        destination: Operand,
        /// What [`Operand`] to apply the shift to.
        operand: Operand,
        /// How far should the operand be shifted.
        shift_n: Operand,
        /// The [`Shift`] that should be applied.
        shift_t: Shift,
    },

    /// Shift left.
    ///
    /// ```ignore
    /// destination = operand << shift
    /// ```
    #[allow(missing_docs)]
    Sl {
        destination: Operand,
        operand: Operand,
        shift: Operand,
    },

    /// Shift right logical.
    ///
    /// ```ignore
    /// destination = operand >> shift
    /// ```
    #[allow(missing_docs)]
    Srl {
        destination: Operand,
        operand: Operand,
        shift: Operand,
    },

    /// Shift right arithmetic.
    ///
    /// ```ignore
    /// destination = operand >> shift
    /// ```
    #[allow(missing_docs)]
    Sra {
        destination: Operand,
        operand: Operand,
        shift: Operand,
    },

    /// Rotating shift right.
    ///
    /// Rotates the `operand` `shift` steps
    /// and stores the result in `destination`.
    #[allow(missing_docs)]
    Sror {
        destination: Operand,
        operand: Operand,
        shift: Operand,
    },

    /// Zero extend
    ///
    /// Zero extends `bits` bits from operand and stores it in destination.
    /// Destination is always machine word sized.
    ZeroExtend {
        /// Where to store the result.
        destination: Operand,

        /// The value to be zero extended.
        operand: Operand,

        /// What bit is considered the last bit in operand
        /// before the extension.
        bits: u32,

        /// The size of the output value.
        target_bits: u32,
    },

    /// Extracts start_bit until stop_bit from the operand and right adjusts it
    /// in to destination.
    BitFieldExtract {
        /// Where to store the result.
        destination: Operand,
        /// Which value to extract bits from.
        operand: Operand,
        /// Where to start the extraction.
        start_bit: u32,
        /// Where to stop the extraction.
        stop_bit: u32,
    },

    /// Count the number of ones in the operand.
    #[allow(missing_docs)]
    CountOnes {
        destination: Operand,
        operand: Operand,
    },

    /// Count the number of zeroes in the operand.
    #[allow(missing_docs)]
    CountZeroes {
        destination: Operand,
        operand: Operand,
    },

    /// Count the number of leading ones (most significant to least
    /// significant).
    #[allow(missing_docs)]
    CountLeadingOnes {
        destination: Operand,
        operand: Operand,
    },

    /// Count the number of leading zeroes (most significant to least)
    /// significant).
    #[allow(missing_docs)]
    CountLeadingZeroes {
        destination: Operand,
        operand: Operand,
    },

    /// Sign extend.
    SignExtend {
        /// Where to store the result.
        destination: Operand,
        /// The value to be sign extended.
        operand: Operand,
        /// What bit is considered the sign bit in operand
        /// before the extension.
        sign_bit: u32,
        /// The number of bits after extension.
        target_size: u32,
    },

    /// Resizes the operand to the desired number of bits.
    ///
    /// Zero extends the `operand` to the desired number of `bits`.
    Resize {
        /// Where to store the result.
        destination: Operand,
        /// The value to resize.
        operand: Operand,
        /// How wide the value should be after resizing.
        bits: u32,
    },

    /// Conditional jump.
    ///
    /// This operation sets PC to the value stored
    /// in `destination` if the `condition` evaluates to true
    /// In a symbolic execution engine the condition might be
    /// able to be both true and false, in this case it causes a fork.
    #[allow(missing_docs)]
    ConditionalJump {
        destination: Operand,
        condition: Condition,
    },

    /// Set the negative flag
    SetNFlag(Operand),

    /// Set the zero flag
    SetZFlag(Operand),

    /// Set the carry flag
    SetCFlag {
        /// Left hand side of the operation.
        operand1: Operand,
        /// Right hand side of the operation.
        operand2: Operand,
        /// Whether or not the operation was a subtraction.
        sub: bool,
        /// Whether or not the operation used the carry bit.
        carry: bool,
    },

    /// Set the carry flag based on a left shift.
    #[allow(missing_docs)]
    SetCFlagShiftLeft { operand: Operand, shift: Operand },

    /// Set the carry flag based on a right shift logical.
    #[allow(missing_docs)]
    SetCFlagSrl { operand: Operand, shift: Operand },

    /// Set the carry flag based on a right shift arithmetic.
    #[allow(missing_docs)]
    SetCFlagSra { operand: Operand, shift: Operand },

    /// Set the carry flag based on a bit rotation.
    SetCFlagRor(Operand),

    /// Set overflow flag.
    ///
    /// Encodings:
    ///  - ADC => sub : false, carry : true
    ///  - ADD => sub : false, carry : false
    ///  - SUB => sub : true, carry : false,
    ///  - SBC => sub : true, carry : true
    SetVFlag {
        /// Left hand side of the operation.
        operand1: Operand,
        /// Right hand side of the operation.
        operand2: Operand,
        /// Whether or not the operation was subtraction.
        sub: bool,
        /// Whether or not the operation used the carry flag.
        carry: bool,
    },

    /// Do all the operations in operations for each operand.
    ///
    /// The current operand is stored in local as CurrentOperand.
    #[allow(missing_docs)]
    ForEach {
        operands: Vec<Operand>,
        operations: Vec<Operation>,
    },

    /// Conditional execution
    ///
    /// Will only run the following instructions i instructions
    /// if the i:th condition in the list is true.
    #[allow(missing_docs)]
    ConditionalExecution { conditions: Vec<Condition> },

    /// Conditionally executes operations depending on the value of the
    /// operands.
    Ite {
        /// The left hand side of the comparison.
        lhs: Operand,
        /// The right hand side of the comparison.
        rhs: Operand,
        /// The comparison operation.
        operation: Comparison,
        /// If the comparison yields true these will be executed.
        then: Vec<Operation>,
        /// If the comparison yields false these will be executed.
        otherwise: Vec<Operation>,
    },

    /// Aborts the execution returning the error message to the user.
    Abort {
        /// Error message to be printed to the user.
        error: String,
    },
}
