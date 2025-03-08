#[derive(Clone, Debug)]
pub enum OperandType {
    Binary16,
    Binary32,
    Binary64,
    Binary128,
    Binary256,
    Integral,
}

#[derive(Clone, Debug)]
pub enum OperandStorage {
    Address(crate::operand::Operand),
    Register(String),
    Local(String),
    Flag(String),
}

#[derive(Clone, Debug)]
pub struct Operand {
    ty: OperandType,
    value: OperandStorage,
}

pub enum Operations {
    /// Rounds a floating point value to an integral value.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    RoundToInt {
        /// The operand to round.
        source: Operand,
        /// Where to store the result.
        destination: Operand,
        /// If this is omitted it will use the system wide value.
        rounding: Option<RoundingMode>,
    },
    /// Gets the first value that is comparativly larger than the source.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    NextUp {
        /// The operand to get the next value for.
        source: Operand,
        /// Where to store the result.
        destination: Operand,
    },
    /// Gets the first value that is comparativly smaller than the source.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    NextDown {
        /// The operand to get the next value for.
        source: Operand,
        /// Where to store the result.
        destination: Operand,
    },
    /// Computes nominator%denominator
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Remainder {
        /// The nominator in the remainder operation.
        nominator: Operand,
        /// The denominator in the operation
        denominator: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Computes lhs+rhs
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Addition {
        /// The left hand side of the addition.
        lhs: Operand,
        /// The right hand side of the addition.
        rhs: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Computes lhs-rhs
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Subtraction {
        /// The left hand side of the subtraction.
        lhs: Operand,
        /// The right hand side of the subtraction.
        rhs: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Computes lhs*rhs
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Multiplication {
        /// The left hand side of the multiplication.
        lhs: Operand,
        /// The right hand side of the multiplication.
        rhs: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Computes nominator/denominator
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Division {
        /// The nominator in the division.
        nominator: Operand,
        /// The denominator in the division.
        denominator: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Computes square root of the operand.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Division {
        /// The operand in the square root.
        operand: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Computes lhs*rhs + add
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    FusedMultiplication {
        /// The lhs in the fused multiplication.
        lhs: Operand,
        /// The rhs in the fused multiplication.
        rhs: Operand,
        /// The additive term in the fused multiplication.
        add: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Converts an int to a floating point value.
    ConvertFromInt {
        /// The operand to convert from.
        operand: Operand,
        /// Where to store the result.
        destination: Operand,
        /// Whether or not to perserv the sign.
        signed: bool,
    },

    /// Copies a value.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Copy {
        /// The value to copy.
        source: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Negates a value.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Negate {
        /// The value to negate.
        source: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Computes the absolute value of a operand.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    Abs {
        /// The value to negate.
        operand: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Copies the sign of a operand and applies it to anther operand.
    ///
    /// ## Exceptions
    ///
    /// This will cause an exception if the source value is of Integral
    /// type.
    CopySign {
        /// The value to copy.
        source: Operand,
        /// The value to copy the sing from.
        sign_source: Operand,
        /// Where to store the result.
        destination: Operand,
    },

    /// Compares two operands with the desired operation mode.
    Compare {
        /// The left hand side of the comparison.
        lhs: Operand,
        /// The right hand side of the comparison.
        rhs: Operand,
        /// The comparison operation to apply.
        operation: ComparisonMode,
        /// Where to store the result (boolean)
        destination: Operand,
        /// Whether or not to raise a signal.
        signal: bool,
    },

    /// Applies a non-computational function on an operand (see 5.7.2)
    NonComputational {
        /// The right hand side of the comparison.
        operand: Operand,
        /// The comparison operation to apply.
        operation: NonComputational,
        /// Where to store the result (boolean)
        destination: Operand,
    },

    /// Checks if the arguments are ordered.
    TotalOrder {
        /// The left hand side of the operation.
        lhs: Operand,
        /// The right hand side of the operation.
        rhs: Operand,
        /// Whether or not to use the absolute value of the left and right side.
        abs: bool,
    },
}

pub enum RoundingMode {
    TiesToEven,
    TiesToAway,
    TiesTowardZero,
    TiesTowardPositive,
    TiesTowardNegative,
    // ?
    Exact,
}

pub enum ComparisonMode {
    Greater,
    GreaterOrEqual,
    NotGreater,
    LessUnordered,
    Less,
    LessOrEqual,
    NotLess,
    GreaterUnordered,
    NotEqual,
    Equal,
}

pub enum NonComputational {
    IsSignMinus,
    IsNormal,
    IsFinite,
    IsZero,
    IsSubNormal,
    IsInfinite,
    IsNan,
    IsCanonical,
    // Omitted as this is not expected to be in the binary.
    // Radix
}
