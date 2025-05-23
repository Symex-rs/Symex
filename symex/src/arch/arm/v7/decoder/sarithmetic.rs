use disarmv7::{
    arch::Register,
    operation::{Smla, Smlad, Smlal, SmlalSelective, Smlald, Smlaw, Smlsd, Smlsld, Smmla, Smmls, Smmul, Smuad, Smul, Smull, Smulw, Smusd, Ssat, SubSpMinusRegister, Sxth},
};
use object::elf::R_PPC_DTPREL16_HA;
use transpiler::pseudo;

use super::Decode;
use crate::arch::arm::v7::decoder::sealed::Into;

impl Decode for Sxth {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Sxth { rd, rm, rotation } = self;
        let rd = rd.local_into();
        let rm = rm.local_into();
        let rotation = rotation.unwrap_or(0).local_into();

        pseudo!([
            rm:u32;
            let rotated = Ror(rm,rotation) & (u16::MAX as u32).local_into();
            rd = SignExtend(rotated, 16,32);
        ])
    }
}

impl Decode for Smla {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { n_high, m_high, rd, rn, rm, ra } = self;
        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let ra = ra.local_into();

        pseudo!([
            rd:u32;rn:u32;rm:u32;ra:i32;

            let operand1:i128 = Resize(rn<15:0>,i128);
            let operand2:i128 = Resize(rm<15:0>,i128);

            if (*n_high) {
                    operand1 = Resize(rn<31:16>,i128);
            }
            if (*m_high) {
                    operand2 = Resize(rm<31:16>,i128);
            }

            let result = operand1 * operand2;
            result = result + Resize(ra,i128);

            let lower = Resize(result<31:0>,u128);
            let result2 = Resize(result,u128);
            let new:u1 = result2 != lower;
            let old_q = Resize(Flag("APSR.Q"),u1);
            Flag("APSR.Q") = old_q | Resize(new,u1);
            rd = lower<31:0>;
        ])
    }
}

impl Decode for Smlad {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { x, rd, rn, rm, ra } = self;
        let m_swap = x.unwrap_or(false);
        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let ra = ra.local_into();

        let rot = 16u32.local_into();
        pseudo!([
            rd:u32;rn:u32;rm:u32;ra:i32;

            let operand2 = rm;
            if (m_swap) {
                operand2 = Ror(rm,rot);
            }
            let product1:i32 = Resize(rn<15:0>,i32) * Resize(operand2<15:0>,i32);
            let product2:i32 = Resize(rn<31:16>,i32) * Resize(operand2<31:16>,i32);
            let result:i128= Resize(product1,i128) + Resize(product2,i128);
            result +=  Resize(ra,i128);

            let lower = Resize(result<31:0>,u128);
            let result2 = Resize(result,u128);
            let new = result2 != lower;
            Flag("APSR.Q") |= new;

            rd = lower<31:0>;
        ])
    }
}

impl Decode for Smlal {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { rdlo, rdhi, rn, rm } = self;
        let rdlo = rdlo.local_into();
        let rdhi = rdhi.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();

        pseudo!([
            rdlo:u32; rdhi:u32; rn:i32; rm:i32;
            let add:u64 = Resize(rdlo,u64);
            let upper:u64 = Resize(rdhi, u64) << 32u32;
            add |= upper;
            let mul = Resize(rn,i128) * Resize(rm,i128);
            let result = mul + Resize(add,i128);
            rdhi = Resize(result<63:32>,u32);
            rdlo = Resize(result<31:0>,u32);
        ])
    }
}

impl Decode for SmlalSelective {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self {
            n_high,
            m_high,
            rdlo,
            rdhi,
            rn,
            rm,
        } = self;
        let rdlo = rdlo.local_into();
        let rdhi = rdhi.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();

        pseudo!([
            rdlo:u32; rdhi:u32; rn:i32; rm:i32;
            let add:u64 = Resize(rdlo,u64);
            let upper:u64 = Resize(rdhi, u64) << 32u32;
            add |= upper;

            let operand1 = Resize(rn<15:0>,i128);
            if (*n_high) {
                operand1 = Resize(rn<31:16>,i128);
            }

            let operand2 = Resize(rm<15:0>,i128);
            if (*m_high) {
                operand2 = Resize(rm<31:16>,i128);
            }


            let mul = Resize(operand2,i128) * Resize(operand2,i128);
            let result = mul + Resize(add,i128);
            rdhi = Resize(result<63:32>,u32);
            rdlo = Resize(result<31:0>,u32);
        ])
    }
}

impl Decode for Smlald {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { x, rdlo, rdhi, rn, rm } = self;
        let m_swap = x.unwrap_or(false);

        let rdlo = rdlo.local_into();
        let rdhi = rdhi.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();

        let rot = 16u32.local_into();
        pseudo!([
            rdhi:u32; rdlo:u32; rm:u32; rn:u32;
            let operand2 = rm;
            if (m_swap) {
                operand2 = Ror(rm,rot);
            }

            let product1 = Resize(rn<15:0>,i128) * Resize(operand2<15:0>,i128);
            let product2 = Resize(rn<31:16>,i128) * Resize(operand2<31:16>,i128);

            let result = product1 + product2;
            let add = Resize(rdlo,u64);
            let upper:u64 = Resize(rdhi,u64) << 32u32;
            add |= upper;

            result += Resize(add,i128);
            rdhi = result<63:32>;
            rdlo = result<63:32>;
        ])
    }
}

impl Decode for Smlaw {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { m_high, rd, rn, rm, ra } = self;

        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let ra = ra.local_into();

        pseudo!([
            rm:u32; ra:u32; rn:u32; rd:u32;
            let operand2:i128 = Resize(rm<15:0>,i128);
            if (*m_high) {
                operand2 = Resize(rm<31:16>,i128);
            }

            let add = Resize(ra,i128) << 16u32;
            let mul = Resize(rn,i128) * operand2;
            let result = mul + add;

            rd = result<47:16>;

            let compare = Resize(result,i128) >> 16u32;
            let new = compare != Resize(rd,i128);

            Flag("ASPR.Q") |=  new;
        ])
    }
}

impl Decode for Smlsd {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { m_swap, rd, rn, rm, ra } = self;
        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let ra = ra.local_into();
        let rot = 16u32.local_into();
        pseudo!([
            rm:u32; rn:u32; ra:u32;rd:u32;
            let operand2 = rm;
            if (m_swap.unwrap_or(false)) {
                operand2 = Ror(rm,rot);
            }
            let product1 = Resize(rn<15:0>,i128) * Resize(operand2<15:0>,i128);
            let product2 = Resize(rn<31:16>,i128) * Resize(operand2<31:16>,i128);
            let result = product1 - product2;
            result = result + Resize(ra, i128);
            rd = result<31:0>;
            let new = result != Resize(rd,i128);
            Flag("ASPR.Q") |= new;
        ])
    }
}

impl Decode for Smlsld {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { m_swap, rdlo, rdhi, rn, rm } = self;
        let m_swap = m_swap.unwrap_or(false);
        let rdlo = rdlo.local_into();
        let rdhi = rdhi.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let rot = 16u32.local_into();
        pseudo!([
            rm:u32; rn:u32; ra:u32;rdlo:u32;rdhi:u32;
            let operand2 = rm;
            if (m_swap) {
                operand2 = Ror(rm,rot);
            }
            let product1 = Resize(rn<15:0>,i128) * Resize(operand2<15:0>,i128);
            let product2 = Resize(rn<31:16>,i128) * Resize(operand2<31:16>,i128);

            let result = product1 - product2;
            let add = Resize(rdlo,u128);
            let upper = Resize(rdhi,u128) << 32u32;
            add |= upper;

            result += Resize(add,i128);

            rdhi = result<63:32>;
            rdlo = result<31:0>;
        ])
    }
}

impl Decode for Smmla {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { round, rd, rn, rm, ra } = self;
        let round = round.unwrap_or(false);
        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let ra = ra.local_into();

        let immediate = general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word64(0x80000000));
        pseudo!([
            rd:u32; rn:u32; rm:u32; ra:u32;
            immediate:i32;
            let result = Resize(ra,i128) << 32u32;
            let mul = Resize(rn,i128) * Resize(rm, i128);
            result += mul;
            if (round) {
                result += ZeroExtend(immediate,128);
            }
            rd = result<63:32>;
        ])
    }
}

impl Decode for Smmls {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { round, rd, rn, rm, ra } = self;
        let round = round.unwrap_or(false);
        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let ra = ra.local_into();

        let immediate = general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word64(0x80000000));
        pseudo!([
            rd:u32; rn:u32; rm:u32; ra:u32;
            immediate:i32;
            let result = Resize(ra,i128) << 32u32;
            let mul = Resize(rn,i128) * Resize(rm, i128);
            result -= mul;
            if (round) {
                result += ZeroExtend(immediate,128);
            }
            rd = result<63:32>;
        ])
    }
}

impl Decode for Smmul {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { round, rd, rn, rm } = self;
        let round = round.unwrap_or(false);
        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();

        let immediate = general_assembly::operand::Operand::Immediate(general_assembly::prelude::DataWord::Word64(0x80000000));
        pseudo!([
            rn:u32;rm:u32;rd:u32;
            immediate:i32;
            let result = Resize(rn,i128) * Resize(rm,i128);
            if (round) {
                result += ZeroExtend(immediate,128);
            }
            rd =  result<63:32>;
        ])
    }
}

impl Decode for Smuad {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { m_swap, rd, rn, rm } = self;
        let m_swap = m_swap.unwrap_or(false);
        let rd = rd.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let rot = 16u32.local_into();
        pseudo!([
            rd:u32; rn:u32; rm:u32;

            let operand2 = rm;
            if (m_swap) {
                operand2 = Ror(rm,rot);
            }
            let product1 = Resize(rn<15:0>,i128) * Resize(operand2<15:0>,i128);
            let product2 = Resize(rn<31:16>,i128) * Resize(operand2<31:16>,i128);
            let result = product1 + product2;
            rd = result<31:0>;
            let new = result != Resize(result<31:0>,i128);
            Flag("APSR.Q") |= new;
        ])
    }
}

impl Decode for Smul {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { n_high, m_high, rd, rn, rm } = self;

        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        pseudo!([
            rn:u32;rm:u32;rd:u32;
            let operand1 = rn<15:0>;
            if (*n_high) {
                operand1 = rn<31:16>;
            }
            let operand2 = rm<15:0>;
            if (*m_high) {
                operand2 = rm<31:16>;
            }
            let result = Resize(operand1,i128) * Resize(operand2,i128);
            rd = result<31:0>;
        ])
    }
}

impl Decode for Smull {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { rdlo, rdhi, rn, rm } = self;
        let rdlo = rdlo.local_into();
        let rdhi = rdhi.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        pseudo!([
            rdlo:u32;rdhi:u32;rn:u32;rm:u32;
            let result = Resize(rn,i64) * Resize(rm,i64);
            rdhi = result<63:32>;
            rdlo = result<31:0>;
        ])
    }
}

impl Decode for Smulw {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { m_high, rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();
        pseudo!([
            rd:u32; rn:u32; rm:u32;
            let operand2 = rm<15:0>;

            if (*m_high) {
                operand2 = rm<31:16>;
            }

            let product = Resize(rn,i128) * Resize(operand2,i128);
            rd = product<47:16>;
        ])
    }
}

impl Decode for Smusd {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { m_swap, rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();
        let rot = 16u32.local_into();
        pseudo!([
            rm:u32; rd:u32; rn:u32;
            let operand2 = rm;
            if (m_swap.unwrap_or(false)) {
                operand2 = Ror(rm,rot);
            }
            let product1 = Resize(rn<15:0>,i128) * Resize(operand2<15:0>,i128);
            let product2 = Resize(rn<31:16>,i128) * Resize(operand2<31:16>,i128);
            let result = product1 - product2;
            rd = result<31:0>;
        ])
    }
}
