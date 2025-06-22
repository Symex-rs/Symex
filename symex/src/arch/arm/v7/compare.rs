#![allow(clippy::all)]
use armv6_m_instruction_parser::{
    conditions::Condition as V6Condition,
    instructons::{Instruction as V6Instruction, Operation as V6Operation},
    registers::Register as V6Register,
};
use disarmv7::prelude::{Condition as V7Condition, Operation as V7Operation, Register as V7Register};

pub(crate) trait LocalEq<T: Sized> {
    fn equal(&self, other: &T) -> bool;
}
pub(crate) trait LocalInto<T: Sized> {
    fn into(self) -> T;
    fn local_into(self) -> T
    where
        Self: Sized,
    {
        self.into()
    }
    fn into_option(self) -> Option<T>
    where
        Self: Sized,
    {
        Some(self.into())
    }
}

impl LocalInto<V7Condition> for V6Condition {
    fn into(self) -> V7Condition {
        match self {
            V6Condition::EQ => V7Condition::Eq,
            V6Condition::NE => V7Condition::Ne,
            V6Condition::CS => V7Condition::Cs,
            V6Condition::CC => V7Condition::Cc,
            V6Condition::MI => V7Condition::Mi,
            V6Condition::PL => V7Condition::Pl,
            V6Condition::VS => V7Condition::Vs,
            V6Condition::VC => V7Condition::Vc,
            V6Condition::HI => V7Condition::Hi,
            V6Condition::LS => V7Condition::Ls,
            V6Condition::GE => V7Condition::Ge,
            V6Condition::LT => V7Condition::Lt,
            V6Condition::GT => V7Condition::Gt,
            V6Condition::LE => V7Condition::Le,
            V6Condition::None => V7Condition::None,
        }
    }
}

impl LocalInto<V7Register> for V6Register {
    fn into(self) -> V7Register {
        match self {
            V6Register::R0 => V7Register::R0,
            V6Register::R1 => V7Register::R1,
            V6Register::R2 => V7Register::R2,
            V6Register::R3 => V7Register::R3,
            V6Register::R4 => V7Register::R4,
            V6Register::R5 => V7Register::R5,
            V6Register::R6 => V7Register::R6,
            V6Register::R7 => V7Register::R7,
            V6Register::R8 => V7Register::R8,
            V6Register::R9 => V7Register::R9,
            V6Register::R10 => V7Register::R10,
            V6Register::R11 => V7Register::R11,
            V6Register::R12 => V7Register::R12,
            V6Register::SP => V7Register::SP,
            V6Register::PC => V7Register::PC,
            V6Register::LR => V7Register::LR,
        }
    }
}

impl LocalEq<V7Condition> for V6Condition {
    fn equal(&self, other: &V7Condition) -> bool {
        match (self, other) {
            (Self::EQ, V7Condition::Eq)
            | (Self::NE, V7Condition::Ne)
            | (Self::CS, V7Condition::Cs)
            | (Self::CC, V7Condition::Cc)
            | (Self::MI, V7Condition::Mi)
            | (Self::PL, V7Condition::Pl)
            | (Self::VS, V7Condition::Vs)
            | (Self::VC, V7Condition::Vc)
            | (Self::HI, V7Condition::Hi)
            | (Self::LS, V7Condition::Ls)
            | (Self::GE, V7Condition::Ge)
            | (Self::LT, V7Condition::Lt)
            | (Self::GT, V7Condition::Gt)
            | (Self::LE, V7Condition::Le)
            | (Self::None, V7Condition::None) => true,
            _ => false,
        }
    }
}

impl LocalEq<V7Register> for V6Register {
    fn equal(&self, other: &V7Register) -> bool {
        match (self, other) {
            (Self::R0, V7Register::R0)
            | (Self::R1, V7Register::R1)
            | (Self::R2, V7Register::R2)
            | (Self::R3, V7Register::R3)
            | (Self::R4, V7Register::R4)
            | (Self::R5, V7Register::R5)
            | (Self::R6, V7Register::R6)
            | (Self::R7, V7Register::R7)
            | (Self::R8, V7Register::R8)
            | (Self::R9, V7Register::R9)
            | (Self::R10, V7Register::R10)
            | (Self::R11, V7Register::R11)
            | (Self::R12, V7Register::R12)
            | (Self::SP, V7Register::SP)
            | (Self::PC, V7Register::PC)
            | (Self::LR, V7Register::LR) => true,
            _ => false,
        }
    }
}

fn eq_trampoline(lhs: &V6Instruction, rhs: &(usize, V7Operation)) -> bool {
    let size = match lhs.is_16bit() {
        true => 16,
        _ => 32,
    };

    if size != rhs.0 {
        return false;
    }
    match (&lhs.operation, &rhs.1) {
        (V6Operation::ADCReg { m, n, d }, V7Operation::AdcRegister(adc)) => {
            let rd = adc.rd.unwrap_or(adc.rn.clone());
            m.equal(&adc.rm) && n.equal(&adc.rn) && d.equal(&rd)
        }
        (V6Operation::ADDImm { imm, n, d }, V7Operation::AddImmediate(add)) => {
            let rd = add.rd.unwrap_or(add.rn.clone());
            (*imm == add.imm) && n.equal(&add.rn) && d.equal(&rd)
        }
        (V6Operation::ADDReg { m, n, d }, V7Operation::AddRegister(add)) => {
            let rd = add.rd.unwrap_or(add.rn.clone());
            m.equal(&add.rm) && n.equal(&add.rn) && d.equal(&rd)
        }
        (V6Operation::ADDImmSP { d, imm }, V7Operation::AddSPImmediate(add)) => {
            let rd = add.rd.unwrap_or(V7Register::SP);
            (*imm == add.imm) && d.equal(&rd)
        }
        (V6Operation::ADDRegSP { d, m }, V7Operation::AddSPRegister(add)) => {
            let rd = add.rd.unwrap_or(V7Register::SP);
            (m.equal(&add.rm)) && d.equal(&rd)
        }
        (V6Operation::ADR { d, imm }, V7Operation::Adr(adr)) => (*imm == adr.imm) && d.equal(&adr.rd),
        (V6Operation::ANDReg { m, dn }, V7Operation::AndRegister(and)) => {
            if and.rd.is_some() {
                return false;
            }
            m.equal(&and.rm) && dn.equal(&and.rn)
        }
        (V6Operation::ASRImm { imm, m, d }, V7Operation::AsrImmediate(asr)) => (*imm == asr.imm) && m.equal(&asr.rm) && d.equal(&asr.rd),
        (V6Operation::ASRReg { m, dn }, V7Operation::AsrRegister(asr)) => m.equal(&asr.rm) && dn.equal(&asr.rn) && dn.equal(&asr.rd),
        (V6Operation::B { cond, imm }, V7Operation::B(b)) => cond.equal(&b.condition) && (*imm == b.imm),
        (V6Operation::BICReg { m, dn }, V7Operation::BicRegister(bic)) => {
            let rd = bic.rd.unwrap_or(bic.rn.clone());
            m.equal(&bic.rm) && dn.equal(&rd) && dn.equal(&bic.rn)
        }
        (V6Operation::BKPT { imm }, V7Operation::Bkpt(bkpt)) => *imm == bkpt.imm,
        (V6Operation::BL { imm }, V7Operation::Bl(bl)) => bl.imm == *imm,
        (V6Operation::BLXReg { m }, V7Operation::Blx(blx)) => m.equal(&blx.rm),
        (V6Operation::BX { m }, V7Operation::Bx(bx)) => m.equal(&bx.rm),
        (V6Operation::CMNReg { m, n }, V7Operation::CmnRegister(cmn)) => m.equal(&cmn.rm) && n.equal(&cmn.rn) && cmn.shift.is_none(),
        (V6Operation::CMPImm { n, imm }, V7Operation::CmpImmediate(cmp)) => n.equal(&cmp.rn) && (*imm == cmp.imm),
        (V6Operation::CMPReg { m, n }, V7Operation::CmpRegister(cmp)) => m.equal(&cmp.rm) && n.equal(&cmp.rn) && cmp.shift.is_none(),
        (V6Operation::CPS { im: _ }, V7Operation::Cps(_cps)) => {
            todo!();
        }
        (V6Operation::CPY, _) => unimplemented!("Deprecated"),
        (V6Operation::DMB { option }, _) => todo!("sync"),
        (V6Operation::DSB { option }, _) => todo!("sync"),
        (V6Operation::EORReg { m, dn }, V7Operation::EorRegister(eor)) => {
            let rd = eor.rd.unwrap_or(eor.rn.clone());
            m.equal(&eor.rm) && dn.equal(&rd) && dn.equal(&eor.rn)
        }
        (V6Operation::ISB { option }, _) => todo!("sync"),
        (V6Operation::LDM { n, reg_list }, V7Operation::Ldm(ldm)) => {
            if !n.equal(&ldm.rn) {
                return false;
            }
            reg_list.iter().zip(ldm.registers.registers.iter()).all(|(lhs, rhs)| lhs.equal(rhs))
        }
        (V6Operation::LDRImm { imm, n, t }, V7Operation::LdrImmediate(ldr)) => (*imm == ldr.imm) && n.equal(&ldr.rn) && t.equal(&ldr.rt),
        (V6Operation::LDRLiteral { t, imm }, V7Operation::LdrLiteral(ldr)) => t.equal(&ldr.rt) && (*imm == ldr.imm),
        (V6Operation::LDRReg { m, n, t }, V7Operation::LdrRegister(ldr)) => m.equal(&ldr.rm) && n.equal(&ldr.rn) && t.equal(&ldr.rt),
        (V6Operation::LDRBImm { imm, n, t }, V7Operation::LdrbImmediate(ldrb)) => (*imm == ldrb.imm.unwrap_or(0)) && n.equal(&ldrb.rn) && t.equal(&ldrb.rt),
        (V6Operation::LDRBReg { m, n, t }, V7Operation::LdrbRegister(ldrb)) => m.equal(&ldrb.rm) && n.equal(&ldrb.rn) && t.equal(&ldrb.rt),
        (V6Operation::LDRHImm { imm, n, t }, V7Operation::LdrhImmediate(ldrh)) => (*imm == ldrh.imm) && n.equal(&ldrh.rn) && t.equal(&ldrh.rt),
        (V6Operation::LDRHReg { m, n, t }, V7Operation::LdrhRegister(ldrh)) => m.equal(&ldrh.rm) && n.equal(&ldrh.rn) && t.equal(&ldrh.rt),
        (V6Operation::LDRSBReg { m, n, t }, V7Operation::LdrsbRegister(ldrsb)) => m.equal(&ldrsb.rm) && n.equal(&ldrsb.rn) && t.equal(&ldrsb.rt),
        (V6Operation::LDRSH { m, n, t }, V7Operation::LdrshRegister(ldrsh)) => m.equal(&ldrsh.rm) && n.equal(&ldrsh.rn) && t.equal(&ldrsh.rt),
        (V6Operation::LSLImm { imm, m, d }, V7Operation::LslImmediate(lsl)) => (*imm == lsl.imm.into()) && m.equal(&lsl.rm) && d.equal(&lsl.rd),
        (V6Operation::LSLReg { m, dn }, V7Operation::LslRegister(lsl)) => m.equal(&lsl.rm) && dn.equal(&lsl.rd) && dn.equal(&lsl.rn),
        (V6Operation::LSRImm { imm, m, d }, V7Operation::LsrImmediate(lsr)) => (*imm == lsr.imm.into()) && m.equal(&lsr.rm) && d.equal(&lsr.rd),
        (V6Operation::LSRReg { m, dn }, V7Operation::LsrRegister(lsr)) => m.equal(&lsr.rm) && dn.equal(&lsr.rd) && dn.equal(&lsr.rn),
        (V6Operation::MOVImm { d, imm }, V7Operation::MovImmediate(mv)) => d.equal(&mv.rd) && (*imm == mv.imm),
        (V6Operation::MOVReg { m, d, set_flags }, V7Operation::MovRegister(mv)) => m.equal(&mv.rm) && d.equal(&mv.rd) && (*set_flags == mv.s.unwrap_or(false)),
        (V6Operation::MRS { d, sysm }, V7Operation::Mrs(mrs)) => {
            todo!("sys calls")
        }
        (V6Operation::MSRReg { n, sysm }, _) => todo!("sys calls"),
        (V6Operation::MUL { n, dm }, V7Operation::Mul(mul)) => n.equal(&mul.rn) && dm.equal(&mul.rd.unwrap_or(mul.rm.clone())) && dm.equal(&mul.rm),
        (V6Operation::MVNReg { m, d }, V7Operation::MvnRegister(mvn)) => m.equal(&mvn.rm) && d.equal(&mvn.rd),
        (V6Operation::NOP, V7Operation::Nop(_)) => true,
        (V6Operation::ORRReg { m, dn }, V7Operation::OrrRegister(orr)) => m.equal(&orr.rm) && dn.equal(&orr.rn) && dn.equal(&orr.rd.unwrap_or(orr.rn.clone())),
        (V6Operation::POP { reg_list }, V7Operation::Pop(pop)) => reg_list.iter().zip(pop.registers.registers.iter()).all(|(lhs, rhs)| lhs.equal(rhs)),
        (V6Operation::PUSH { reg_list }, V7Operation::Push(push)) => reg_list.iter().zip(push.registers.registers.iter()).all(|(lhs, rhs)| lhs.equal(rhs)),
        (V6Operation::REV { m, d }, V7Operation::Rev(rev)) => m.equal(&rev.rm) && d.equal(&rev.rd),
        (V6Operation::REV16 { m, d }, V7Operation::Rev16(rev)) => m.equal(&rev.rm) && d.equal(&rev.rd),
        (V6Operation::REVSH { m, d }, V7Operation::Revsh(rev)) => m.equal(&rev.rm) && d.equal(&rev.rd),
        (V6Operation::RORReg { m, dn }, V7Operation::RorRegister(ror)) => m.equal(&ror.rm) && dn.equal(&ror.rn) && dn.equal(&ror.rd),
        (V6Operation::RSBImm { n, d }, V7Operation::RsbImmediate(rsb)) => n.equal(&rsb.rn) && d.equal(&rsb.rd.unwrap_or(rsb.rn.clone())),
        (V6Operation::SBCReg { m, dn }, V7Operation::SbcRegister(sbc)) => m.equal(&sbc.rm) && dn.equal(&sbc.rn) && dn.equal(&sbc.rd.unwrap_or(sbc.rn.clone())),
        (V6Operation::SEV, _) => todo!(),
        (V6Operation::STM { n, reg_list }, V7Operation::Stm(stm)) => n.equal(&stm.rn) && reg_list.iter().zip(stm.registers.registers.iter()).all(|(lhs, rhs)| lhs.equal(rhs)),
        (V6Operation::STRImm { imm, n, t }, V7Operation::StrImmediate(str)) => (*imm == str.imm) && n.equal(&str.rn) && t.equal(&str.rt),
        (V6Operation::STRReg { m, n, t }, V7Operation::StrRegister(str)) => m.equal(&str.rm) && n.equal(&str.rm) && t.equal(&str.rt),
        (V6Operation::STRBImm { imm, n, t }, V7Operation::StrbImmediate(strb)) => (*imm == strb.imm) && n.equal(&strb.rn) && t.equal(&strb.rt),
        (V6Operation::STRBReg { m, n, t }, V7Operation::StrbRegister(el)) => m.equal(&el.rm) && n.equal(&el.rm) && t.equal(&el.rt),
        (V6Operation::STRHImm { imm, n, t }, V7Operation::StrhImmediate(el)) => (*imm == el.imm.unwrap_or(0)) && n.equal(&el.rn) && t.equal(&el.rt),
        (V6Operation::STRHReg { m, n, t }, V7Operation::StrhRegister(el)) => m.equal(&el.rm) && n.equal(&el.rm) && t.equal(&el.rt),
        (V6Operation::SUBImm { imm, n, d }, V7Operation::SubImmediate(sub)) => (*imm == sub.imm) && n.equal(&sub.rn) && d.equal(&sub.rd.unwrap_or(sub.rn.clone())),
        (V6Operation::SUBReg { m, n, d }, V7Operation::SubRegister(sub)) => m.equal(&sub.rm) && n.equal(&sub.rn) && d.equal(&sub.rd.unwrap_or(sub.rn.clone())),
        (V6Operation::SUBImmSP { imm }, V7Operation::SubSpMinusImmediate(sub)) => *imm == sub.imm && sub.rd.unwrap_or(V7Register::SP) == V7Register::SP,
        (V6Operation::SVC { imm }, _) => todo!("sys calls"),
        (V6Operation::SXTB { m, d }, V7Operation::Sxtb(sxtb)) => m.equal(&sxtb.rm) && d.equal(&sxtb.rd),
        (V6Operation::SXTH { m, d }, V7Operation::Sxth(sxth)) => m.equal(&sxth.rm) && d.equal(&sxth.rd),
        (V6Operation::TSTReg { m, n }, V7Operation::TstRegister(tst)) => m.equal(&tst.rm) && n.equal(&tst.rn),
        (V6Operation::UDF { imm }, _) => unimplemented!("no need for undefined"),
        (V6Operation::UXTB { m, d }, V7Operation::Uxtb(uxtb)) => m.equal(&uxtb.rm) && d.equal(&uxtb.rd),
        (V6Operation::UXTH { m, d }, V7Operation::Uxth(uxth)) => m.equal(&uxth.rm) && d.equal(&uxth.rd),
        (V6Operation::WFE, _) => todo!(),
        (V6Operation::WFI, _) => todo!(),
        (V6Operation::YIELD, _) => todo!(),
        _ => false,
    }
}
impl LocalEq<(usize, V7Operation)> for V6Instruction {
    fn equal(&self, other: &(usize, V7Operation)) -> bool {
        let ret = eq_trampoline(self, other);
        if !ret {
            println!("Instruction mismatch : \n\tV6 : {self:?}\n\tV7 {other:?}");
        }
        ret
    }
}

impl LocalEq<V6Instruction> for (usize, V7Operation) {
    fn equal(&self, other: &V6Instruction) -> bool {
        other.equal(self)
    }
}
