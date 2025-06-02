#[derive(Clone, Debug, PartialEq, Eq)]
/// Enumerates all of the handled IEEE 754 types.
pub enum OperandType {
    /// 16 bit float.
    Binary16,
    /// 32 bit float.
    Binary32,
    /// 64 bit float.
    Binary64,
    /// 128 bit float.
    Binary128,
    /// Integral type.
    Integral {
        /// The size of the value in bits.
        size: u32,
        /// Whether or not the value should be interpreted as signed.
        signed: bool,
    },
}

#[derive(Clone, Debug)]
/// Enumerates all of the possible storage locations for an operand.
pub enum OperandStorage {
    /// The operand is stored at an address.
    Address(crate::operand::Operand),
    /// The operand is stored in a register.
    Register {
        /// The register name.
        id: String,
        /// The register type.
        ty: OperandType,
    },
    /// The operand is stored in a local variable.
    Local(String),
    /// An immediate field.
    Immediate {
        /// The immediate value to load.
        value: f64,
        /// The type of the operand.
        ty: OperandType,
    },
    /// A floating point value stored in a core register.
    CoreRegister {
        /// The name of the core register that stores the operand.
        id: String,
        /// The type of the operand.
        ty: OperandType,
        /// Whether or not the value is signed.
        ///
        /// Note: This is a duplicate of the sign bit in an integral type if the
        /// value is of integral type.
        signed: bool,
    },
    /// A value stored in the core.
    CoreOperand {
        /// The core operand to use.
        operand: crate::operand::Operand,
        /// The type of the core operand.
        ty: OperandType,
        /// Whether or not the value is signed.
        ///
        /// Note: This is a duplicate of the sign bit in an integral type if the
        /// value is of integral type.
        signed: bool,
    },
}

#[derive(Clone, Debug)]
/// Denotes an IEEE754 operand.
pub struct Operand {
    /// The type of the operand.
    pub ty: OperandType,
    /// The value of the operand.
    pub value: OperandStorage,
}

#[derive(Clone, Debug)]
/// Enumerates the supported IEEE instructions.
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
    ///
    ///
    /// ## Notes
    ///
    /// ### Sign
    ///
    /// This can return negative remainders in certain cases.
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
    Sqrt {
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
    },

    /// Converts between int and floating point values.
    ///
    /// This is a non standard instruction.
    Convert {
        /// The operand to convert from.
        source: Operand,
        /// Where to store the result.
        destination: Operand,
        /// The rounding mode to use.
        rounding: Option<RoundingMode>,
    },

    /// Copies a value.
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
        destination: crate::operand::Operand,
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
        destination: crate::operand::Operand,
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

#[derive(Clone, Debug)]
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
}

#[derive(Clone, Debug)]
/// Enumerates all of the IEEE754 comparisons.
pub enum ComparisonMode {
    /// Checks if lhs is strictly greater than the rhs in an ordered manner.
    Greater,
    /// Checks if the lhs is strictly greater or equal to the rhs in an ordered
    /// manner.
    GreaterOrEqual,
    /// Checks if the lhs is strictly not greater than the rhs in an ordered
    /// manner.
    NotGreater,
    /// Checks if lhs is less than rhs in an unordered manner.
    LessUnordered,
    /// Checks if lhs is less than rhs in an ordered manner.
    Less,
    /// Checks if lhs is less than or equal to rhs in an ordered manner.
    LessOrEqual,
    /// Checks if lhs is not less than rhs in an ordered manner.
    NotLess,
    /// Checks if lhs is greater than rhs in an un ordered manner.
    GreaterUnordered,
    /// Checks if two values are not equal.
    NotEqual,
    /// Checks if two floating point values are equal.
    Equal,
}

#[derive(Clone, Debug)]
/// Enumerates a set of non computational operations.
pub enum NonComputational {
    /// Checks if a floating point value is negative.
    IsSignMinus,
    /// Checks if a floating point value is normal.
    IsNormal,
    /// Checks if a floating point value is finite.
    IsFinite,
    /// Checks if a floating point value is zero.
    IsZero,
    /// Checks if a floating point value is sub normal.
    IsSubNormal,
    /// Checks if a floating point value is infinite.
    IsInfinite,
    /// Checks if a floating point value is nan.
    IsNan,
    /// Checks if a floating point value is canonical.
    IsCanonical,
    // Omitted as this is not expected to be in the binary.
    // Radix
}

impl OperandType {
    /// Returns the size of the operand in bits.
    pub const fn size(&self) -> u32 {
        match self {
            Self::Binary16 => 16,
            Self::Binary32 => 32,
            Self::Binary64 => 64,
            Self::Binary128 => 128,
            Self::Integral { size, signed: _ } => *size,
        }
    }
}

impl std::fmt::Display for RoundingMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            Self::Exact => "Exact",
            Self::TiesToEven => "Ties to even",
            Self::TiesToAway => "Ties to away from zero",
            Self::TiesTowardZero => "Ties toward zero",
            Self::TiesTowardPositive => "Ties toward positive infinity",
            Self::TiesTowardNegative => "Ties toward negative infinity",
        })
    }
}
impl OperandType {
    /// Returns the fractional bits in the floating point
    pub const fn fraction(&self) -> u64 {
        match self {
            Self::Binary16 => 10 + 1,
            Self::Binary32 => 23 + 1,
            Self::Binary64 => 53 + 1,
            Self::Binary128 => 113 + 1,
            Self::Integral { size: _, signed: _ } => todo!(),
        }
    }

    /// Returns the exponent bits in the float
    pub const fn exponent(&self) -> u64 {
        match self {
            Self::Binary128 => 128 - self.fraction(),
            Self::Binary64 => 64 - self.fraction(),
            Self::Binary32 => 32 - self.fraction(),
            Self::Binary16 => 16 - self.fraction(),
            Self::Integral { size: _, signed: _ } => todo!(),
        }
    }
}
