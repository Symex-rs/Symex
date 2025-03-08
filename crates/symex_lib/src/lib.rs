#![no_std]
mod any;

use core::mem::size_of;

pub use any::{any, Any};
pub use any_derive::Any;
pub use valid_derive::Validate;

/// Assume the condition.
///
/// Adds a constraint that the passed condition must be true. If the condition
/// can never be true, this will lead to an `Unsat` error.
///
/// # Example
///
/// ```rust
/// # use symex_lib::assume;
/// fn foo(var: i32) -> i32 {
///     // Will add a constraint to the solver for the passed condition.
///     assume(var >= 0);
///     if var < 0 {
///         unreachable!();
///     }
///     var
/// }
/// ```
#[inline(never)]
pub fn assume(condition: bool) {
    let mut condition = condition;
    if condition {
        black_box(&mut condition);
    } else {
        suppress_path();
    }
}

/// Suppresses this path from analysis result
///
/// The path will still be analyzed but no output will be generated for the path
/// unless some other error occur before suppress_path is called.
/// This is a safer option to [`ignore_path`] that will not affect soundness.
///
/// # Example
/// ```rust
/// # use symex_lib::symbolic;
/// # use symex_lib::suppress_path;
/// # fn foo() {
/// #   let mut x = 0;
/// #   symbolic(&mut x);
/// if x == 0 {
///     // This path will be found
/// } else if x > 2 {
///     suppress_path();
///     // This path will be found but ignored.
/// } else {
///     panic!();
///     suppress_path();
///     // This path will result in a error and will be shown in output.
/// }
/// # }
/// ```
#[inline(never)]
pub fn suppress_path() {
    core::panic!()
}

#[inline(never)]
pub fn start_cyclecount() {
    let mut s: i32 = 0;
    black_box(&mut s);
}

#[inline(never)]
pub fn end_cyclecount() {
    let mut s: i64 = 0;
    black_box(&mut s);
}

/// Creates a new symbolic value for `value`. This removes all constraints.
///
/// This creates a new symbolic variable and assigns overwrites the passed
/// `value`. This must be performed since constraints added to the solver cannot
/// be removed, and the previous value may have constraints associated with it.
///
/// # Example
///
/// ```rust
/// # use symex_lib::symbolic;
/// fn foo() {
///     // This will create a symbol with the constraint that x is 0.
///     let mut x = 0;
///     // Removes all constraints from `x`, letting it be an unconstrained symbol
///     // that can be anything.
///     symbolic(&mut x);
///     if x != 0 {
///         // This path will be found
///     }
/// }
/// ```
#[inline(never)]
pub fn symbolic<T>(value: &mut T) {
    let mut size = size_of::<T>();
    black_box(&mut size);
    symbolic_size(value, size_of::<T>());
}

#[doc(hidden)]
#[inline(never)]
pub extern "C" fn symbolic_size<T>(value: &mut T, mut size: usize) {
    black_box(value);
    black_box(&mut size);
}

/// Assume the passed value contains a valid representation.
///
/// # Example
///
/// ```rust
/// # use symex_lib::{Validate, valid, symbolic};
/// #[derive(Validate)]
/// enum E {
///     A,
///     B,
/// }
///
/// fn assume_valid() {
///     let mut e = E::A;
///     symbolic(&mut e); // `e` does not necessarily contain a valid discriminant.
///     valid(&e); // only allows `e` to contain valid discriminants.
/// }
/// ```
pub fn valid<T: Valid>(value: &T) {
    assume(value.is_valid());
}

pub trait Valid {
    fn is_valid(&self) -> bool {
        true
    }
}

impl<T> Valid for &T {
    fn is_valid(&self) -> bool {
        true
    }
}

/// Suppresses this path from the executor.
///
/// Note that this affects the completeness of the analysis and can prevent
/// certain errors from being found.
#[inline(never)]
pub fn ignore_path() -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}

/// Try and trick the optimizer.
///
/// It is hard to create a "can be anything" value in pure rust, this function
/// tries to trick the optimizer into not optimizing `value`.
#[doc(hidden)]
pub fn black_box<T>(value: &mut T) {
    *value = unsafe { core::ptr::read_volatile(value as *mut T) }
}
