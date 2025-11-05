#[cfg(feature = "bitwuzla")]
pub mod bitwuzla;
#[cfg(feature = "boolector")]
#[deprecated(since = "0.2.0", note = "The boolector solver is no longer supported as the solver has no support for lambdas")]
pub mod boolector;
#[cfg(feature = "z3")]
pub mod z3;

pub mod logger;
