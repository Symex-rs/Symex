use crate::smt::SolverError;

/// The number of bits per byte the memory system expects.
pub const BITS_IN_BYTE: u32 = 8;

/// Converts number of bits to bytes, returning an error if `bits` are not a
/// multiple of `[BITS_IN_BYTE]`.
pub const fn to_bytes(size: u64) -> Result<u64, MemoryError> {
    if size.is_multiple_of(BITS_IN_BYTE as u64) {
        Ok(size / 8)
    } else {
        Err(MemoryError::BitsNotMultipleOfBytes(size))
    }
}

pub const fn to_bytes_u32(size: u32) -> Result<u32, MemoryError> {
    if size.is_multiple_of(BITS_IN_BYTE) {
        Ok(size / 8)
    } else {
        Err(MemoryError::BitsNotMultipleOfBytes(size as u64))
    }
}

/// Error representing an issue when performing memory operations.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum MemoryError {
    /// Tried to allocate with a size of zero.
    #[error("Tried to allocate with a size of zero")]
    ZeroSizedAllocation,

    /// When wanting a size in bytes, if the bits don't cleanly map to a certain
    /// amount of bytes.
    #[error("Number of bits {0} is not a multiple of bytes")]
    BitsNotMultipleOfBytes(u64),

    /// The given size is not a power of two.
    #[error("Number of bits {0} is not a power of two")]
    NotPowerOfTwo(u64),

    /// When the address space becomes exhausted.
    #[error("Tried to allocate {0} bits which would overflow the address space")]
    AddressSpaceExhausted(u64),

    /// Possible to try and read/write a null pointer.
    #[error("Null pointer encountered")]
    NullPointer,

    /// Each allocation has a respective size, this is returned when a read
    /// starts inside one allocation and ends outside of it.
    #[error("Out of bounds")]
    OutOfBounds,

    /// Errors passed on from the solver.
    #[error(transparent)]
    Solver(#[from] SolverError),

    #[error("Out of bounds")]
    /// Tried to read a local before it was created.
    TriedToReadLocalBeforeAssign(String),

    #[error("Tried to assign to immediate field")]
    /// Tried to assign to an immediate field.
    TriedToAssignToImmediateField,
}
