use general_assembly::shift::Shift;

use super::{state::GAState, AddWithCarryResult};
use crate::{
    smt::{SmtExpr, SmtMap},
    Composition,
};

pub fn count_ones<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: u32) -> C::SmtExpression {
    let mut count = ctx.memory.from_u64(0, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in 0..word_size {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask);
        count = count.add(&to_add);
    }
    count
}

pub fn count_zeroes<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: u32) -> C::SmtExpression {
    let input = input.not();
    let mut count = ctx.memory.from_u64(0, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in 0..word_size {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask);
        count = count.add(&to_add);
    }
    count
}

pub fn count_leading_ones<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: u32) -> C::SmtExpression {
    let mut count = ctx.memory.from_u64(0, word_size);
    let mut stop_count_mask = ctx.memory.from_u64(1, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in (0..word_size).rev() {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask).and(&stop_count_mask);
        stop_count_mask = to_add.clone();
        count = count.add(&to_add);
    }
    count
}

pub fn count_leading_zeroes<C: Composition>(input: &C::SmtExpression, ctx: &GAState<C>, word_size: u32) -> C::SmtExpression {
    let input = input.not();
    let mut count = ctx.memory.from_u64(0, word_size);
    let mut stop_count_mask = ctx.memory.from_u64(1, word_size);
    let mask = ctx.memory.from_u64(1, word_size);
    for n in (0..word_size).rev() {
        let symbolic_n = ctx.memory.from_u64(n as u64, word_size);
        let to_add = input.shift(&symbolic_n, Shift::Lsr).and(&mask).and(&stop_count_mask);
        stop_count_mask = to_add.clone();
        count = count.add(&to_add);
    }
    count
}

/// Does an add with carry and returns result, carry out and overflow like a
/// hardware adder.
pub fn add_with_carry<E: SmtExpr>(op1: &E, op2: &E, carry_in: &E, word_size: u32) -> AddWithCarryResult<E> {
    let carry_in = carry_in.resize_unsigned(1);
    let c1 = op2.uaddo(&carry_in.zero_ext(word_size));
    let op2 = op2.add(&carry_in.zero_ext(word_size));
    let result = op1.add(&op2);
    let carry = op1.uaddo(&op2).or(&c1);
    let overflow = op1.saddo(&op2);
    AddWithCarryResult {
        carry_out: carry,
        overflow,
        result,
    }
}
