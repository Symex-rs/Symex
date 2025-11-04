//! Provides cycle counting for the armv6-m instruction set.

use armv6_m_instruction_parser::{instructons::Operation, registers::Register};

use crate::{
    executor::{instruction::CycleCount, state::GAState},
    smt::{SmtExpr, SmtMap},
};

#[allow(clippy::match_same_arms, clippy::too_many_lines)]
pub(crate) fn cycle_count_m0plus_core<C: crate::Composition>(operation: &Operation) -> CycleCount<C> {
    // SIO based on the rp2040 make this configurable later
    let address_max_cycle_function = |state: &mut GAState<C>| {
        let Some(address) = state.memory.get_register("LastAddr").unwrap().get_constant() else {
            return 2;
        };

        if (0xd000_0000..=0xdfff_ffff).contains(&address) {
            1
        } else {
            2
        }
    };
    match operation {
        Operation::ADCReg { m: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::ADDImm { imm: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::ADDReg { m: _, n: _, d } => {
            let max_cycle = if *d == Register::PC { 2 } else { 1 };
            CycleCount::Value(max_cycle)
        }
        Operation::ADDImmSP { d: _, imm: _ } => CycleCount::Value(1),
        Operation::ADDRegSP { d: _, m: _ } => CycleCount::Value(1),
        Operation::ADR { d: _, imm: _ } => CycleCount::Value(1),
        Operation::ANDReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::ASRImm { imm: _, m: _, d: _ } => CycleCount::Value(1),
        Operation::ASRReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::B { cond: _, imm: _ } => {
            let max_cycle = |state: &mut GAState<C>| {
                if state.get_has_jumped() {
                    2
                } else {
                    1
                }
            };
            CycleCount::Function(max_cycle)
        }
        Operation::BICReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::BKPT { imm: _ } => CycleCount::Value(0),
        Operation::BL { imm: _ } => CycleCount::Value(3),
        Operation::BLXReg { m: _ } => CycleCount::Value(2),
        Operation::BX { m: _ } => CycleCount::Value(2),
        Operation::CMNReg { m: _, n: _ } => CycleCount::Value(1),
        Operation::CMPImm { n: _, imm: _ } => CycleCount::Value(1),
        Operation::CMPReg { m: _, n: _ } => CycleCount::Value(1),
        Operation::CPS { im: _ } => CycleCount::Value(1),
        Operation::CPY => {
            // this is not a real instruction is equvelatn to mov
            unreachable!()
        }
        Operation::DMB { option: _ } => CycleCount::Value(3),
        Operation::DSB { option: _ } => CycleCount::Value(3),
        Operation::EORReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::ISB { option: _ } => CycleCount::Value(3),
        Operation::LDM { n: _, reg_list } => {
            let max_cycle = 1 + reg_list.len();
            CycleCount::Value(max_cycle)
        }

        // \/\/\/\/ Can be one depending on core implementation and address \/\/\/\/
        Operation::LDRImm { imm: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRLiteral { t: _, imm: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRReg { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRBImm { imm: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRBReg { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRHImm { imm: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRHReg { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRSBReg { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::LDRSH { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        // /\/\/\/\ Can be one depending on core implementation and address /\/\/\/\
        Operation::LSLImm { imm: _, m: _, d: _ } => CycleCount::Value(1),
        Operation::LSLReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::LSRImm { imm: _, m: _, d: _ } => CycleCount::Value(1),
        Operation::LSRReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::MOVImm { d: _, imm: _ } => CycleCount::Value(1),
        Operation::MOVReg { m: _, d, set_flags: _ } => {
            let max_cycle = if *d == Register::PC { 2 } else { 1 };
            CycleCount::Value(max_cycle)
        }
        Operation::MRS { d: _, sysm: _ } => CycleCount::Value(3),
        Operation::MSRReg { n: _, sysm: _ } => CycleCount::Value(3),
        Operation::MUL { n: _, dm: _ } => {
            CycleCount::Value(32) // Can be one depending on core
                                  // implementation
                                  // might be able to read this from somewhere.
        }
        Operation::MVNReg { m: _, d: _ } => CycleCount::Value(1),
        Operation::NOP => CycleCount::Value(1),
        Operation::ORRReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::POP { reg_list } => {
            let max_cycle = if reg_list.contains(&Register::PC) { 3 } else { 1 } + reg_list.len();
            CycleCount::Value(max_cycle)
        }
        Operation::PUSH { reg_list } => CycleCount::Value(1 + reg_list.len()),
        Operation::REV { m: _, d: _ } => CycleCount::Value(1),
        Operation::REV16 { m: _, d: _ } => CycleCount::Value(1),
        Operation::REVSH { m: _, d: _ } => CycleCount::Value(1),
        Operation::RORReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::RSBImm { n: _, d: _ } => CycleCount::Value(1),
        Operation::SBCReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::SEV => CycleCount::Value(1),
        Operation::STM { n: _, reg_list } => CycleCount::Value(1 + reg_list.len()),

        // \/\/\/\/ Can be one depending on core implementation and address \/\/\/\/
        Operation::STRImm { imm: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::STRReg { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::STRBImm { imm: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::STRBReg { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::STRHImm { imm: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        Operation::STRHReg { m: _, n: _, t: _ } => CycleCount::Function(address_max_cycle_function),
        // /\/\/\/\ Can be one depending on core implementation and address /\/\/\/\
        Operation::SUBImm { imm: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::SUBReg { m: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::SUBImmSP { imm: _ } => CycleCount::Value(1),
        Operation::SVC { imm: _ } => CycleCount::Value(0),
        Operation::SXTB { m: _, d: _ } => CycleCount::Value(1),
        Operation::SXTH { m: _, d: _ } => CycleCount::Value(1),
        Operation::TSTReg { m: _, n: _ } => CycleCount::Value(1),
        Operation::UXTB { m: _, d: _ } => CycleCount::Value(1),
        Operation::UXTH { m: _, d: _ } => CycleCount::Value(1),
        Operation::WFE => todo!(),
        Operation::WFI => todo!(),
        Operation::YIELD => todo!(),
        Operation::UDF { imm: _imm } => unimplemented!(),
    }
}

#[allow(dead_code, clippy::match_same_arms, clippy::too_many_lines)]
pub(crate) fn cycle_count_m0_core<C: crate::Composition>(operation: &Operation) -> CycleCount<C> {
    match operation {
        Operation::ADCReg { m: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::ADDImm { imm: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::ADDReg { m: _, n: _, d } => {
            let max_cycle = if *d == Register::PC { 3 } else { 1 };
            CycleCount::Value(max_cycle)
        }
        Operation::ADDImmSP { d: _, imm: _ } => CycleCount::Value(1),
        Operation::ADDRegSP { d: _, m: _ } => CycleCount::Value(1),
        Operation::ADR { d: _, imm: _ } => CycleCount::Value(1),
        Operation::ANDReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::ASRImm { imm: _, m: _, d: _ } => CycleCount::Value(1),
        Operation::ASRReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::B { cond: _, imm: _ } => {
            let max_cycle = |state: &mut GAState<C>| {
                if state.get_has_jumped() {
                    3
                } else {
                    1
                }
            };
            CycleCount::Function(max_cycle)
        }
        Operation::BICReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::BKPT { imm: _ } => CycleCount::Value(0),
        Operation::BL { imm: _ } => CycleCount::Value(4),
        Operation::BLXReg { m: _ } => CycleCount::Value(3),
        Operation::BX { m: _ } => CycleCount::Value(3),
        Operation::CMNReg { m: _, n: _ } => CycleCount::Value(1),
        Operation::CMPImm { n: _, imm: _ } => CycleCount::Value(1),
        Operation::CMPReg { m: _, n: _ } => CycleCount::Value(1),
        Operation::CPS { im: _ } => CycleCount::Value(1),
        Operation::CPY => {
            // this is not a real instruction is equvelatn to mov
            unreachable!()
        }
        Operation::DMB { option: _ } => CycleCount::Value(4),
        Operation::DSB { option: _ } => CycleCount::Value(4),
        Operation::EORReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::ISB { option: _ } => CycleCount::Value(4),
        Operation::LDM { n: _, reg_list } => {
            let max_cycle = 1 + reg_list.len();
            CycleCount::Value(max_cycle)
        }
        Operation::LDRImm { imm: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LDRLiteral { t: _, imm: _ } => CycleCount::Value(2),
        Operation::LDRReg { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LDRBImm { imm: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LDRBReg { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LDRHImm { imm: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LDRHReg { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LDRSBReg { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LDRSH { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::LSLImm { imm: _, m: _, d: _ } => CycleCount::Value(1),
        Operation::LSLReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::LSRImm { imm: _, m: _, d: _ } => CycleCount::Value(1),
        Operation::LSRReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::MOVImm { d: _, imm: _ } => CycleCount::Value(1),
        Operation::MOVReg { m: _, d, set_flags: _ } => {
            let max_cycle = if *d == Register::PC { 3 } else { 1 };
            CycleCount::Value(max_cycle)
        }
        Operation::MRS { d: _, sysm: _ } => CycleCount::Value(4),
        Operation::MSRReg { n: _, sysm: _ } => CycleCount::Value(4),
        Operation::MUL { n: _, dm: _ } => {
            CycleCount::Value(32) // Can be one depending on core
                                  // implementation
                                  // might be able to read this from somewhere.
        }
        Operation::MVNReg { m: _, d: _ } => CycleCount::Value(1),
        Operation::NOP => CycleCount::Value(1),
        Operation::ORRReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::POP { reg_list } => {
            let max_cycle = if reg_list.contains(&Register::PC) { 4 } else { 1 } + reg_list.len();
            CycleCount::Value(max_cycle)
        }
        Operation::PUSH { reg_list } => CycleCount::Value(1 + reg_list.len()),
        Operation::REV { m: _, d: _ } => CycleCount::Value(1),
        Operation::REV16 { m: _, d: _ } => CycleCount::Value(1),
        Operation::REVSH { m: _, d: _ } => CycleCount::Value(1),
        Operation::RORReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::RSBImm { n: _, d: _ } => CycleCount::Value(1),
        Operation::SBCReg { m: _, dn: _ } => CycleCount::Value(1),
        Operation::SEV => CycleCount::Value(1),
        Operation::STM { n: _, reg_list } => CycleCount::Value(1 + reg_list.len()),
        Operation::STRImm { imm: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::STRReg { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::STRBImm { imm: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::STRBReg { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::STRHImm { imm: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::STRHReg { m: _, n: _, t: _ } => CycleCount::Value(2),
        Operation::SUBImm { imm: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::SUBReg { m: _, n: _, d: _ } => CycleCount::Value(1),
        Operation::SUBImmSP { imm: _ } => CycleCount::Value(1),
        Operation::SVC { imm: _ } => CycleCount::Value(0),
        Operation::SXTB { m: _, d: _ } => CycleCount::Value(1),
        Operation::SXTH { m: _, d: _ } => CycleCount::Value(1),
        Operation::TSTReg { m: _, n: _ } => CycleCount::Value(1),
        Operation::UXTB { m: _, d: _ } => CycleCount::Value(1),
        Operation::UXTH { m: _, d: _ } => CycleCount::Value(1),
        Operation::WFE => todo!(),
        Operation::WFI => todo!(),
        Operation::YIELD => todo!(),
        Operation::UDF { imm: _imm } => unimplemented!(),
    }
}
