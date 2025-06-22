#![allow(clippy::unnecessary_cast)]
use disarmv7::prelude::{arch::set_flags::LocalUnwrap, Condition as ARMCondition, Operation as V7Operation, Register, Shift};
use general_assembly::{
    condition::Condition,
    operand::{DataWord, Operand},
    operation::Operation,
    shift::Shift as GAShift,
};
use paste::paste;
use transpiler::pseudo;

use crate::warn;

trait Decode {
    fn decode(&self, in_it_block: bool) -> Vec<Operation>;
}

macro_rules! consume {
    (($($id:ident$($(.$e:expr_2021)+)?),*) from $name:ident) => {
        #[allow(unused_parens)]
        let ($($id),*) = {
            paste!(
                let consumer = $name.consumer();
                $(
                    let ($id,consumer) = consumer.[<consume_ $id>]();
                    $(let $id = $id$(.$e)+;)?
                )*
                consumer.consume();
            );
            ($($id),*)
        };
    };
}
macro_rules! shift {
    ($ret:ident.$shift:ident $reg:ident -> $target:ident $(set c for $reg_flag:ident)?) => {
       if let Some(shift) = $shift {
            let (shift_t, shift_n) = (
                    shift.shift_t.clone().local_into(),
                    (shift.shift_n as u32).local_into(),
            );

            $(
                if shift.shift_n as u32 != 0 {
                    $ret.push( match shift_t{
                    general_assembly::shift::Shift::Lsl => general_assembly::operation::Operation::SetCFlagShiftLeft { operand: $reg_flag.clone(), shift: shift_n.clone() },
                    general_assembly::shift::Shift::Asr => general_assembly::operation::Operation::SetCFlagSra { operand: $reg_flag.clone(), shift: shift_n.clone() },
                    general_assembly::shift::Shift::Lsr => general_assembly::operation::Operation::SetCFlagSrl { operand: $reg_flag.clone(), shift: shift_n.clone() },
                    general_assembly::shift::Shift::Rrx => todo!(),
                    general_assembly::shift::Shift::Ror => todo!()
                    });
                }
            )?
            $ret.push(
                general_assembly::operation::Operation::Shift {
                    destination: $target.clone(),
                    operand: $reg.clone(),
                    shift_n: shift_n.clone(),
                    shift_t: shift_t.clone(),
            });
       }
       else {

            $ret.push(
                general_assembly::operation::Operation::Move{
                    destination:$target.clone(),
                    source:$reg.clone()
                });

       }
    };
}
macro_rules! shift_imm {
    ($ret:ident.($shift_t:ident,$($shift_n_const:literal)?$($shift_n:ident)?) $reg:ident -> $target:ident $(set c for $reg_flag:ident)?) => {
        {
            let (shift_t, shift_n) = (
                    $shift_t,
                    $($shift_n)?$($shift_n_const)?,
            );
            $($ret.push( match shift_t{
                general_assembly::shift::Shift::Lsl => general_assembly::operation::Operation::SetCFlagShiftLeft { operand: $reg_flag.clone(), shift: shift_n.clone() },
                general_assembly::shift::Shift::Asr => general_assembly::operation::Operation::SetCFlagSra { operand: $reg_flag.clone(), shift: shift_n.clone() },
                general_assembly::shift::Shift::Lsr => general_assembly::operation::Operation::SetCFlagSrl { operand: $reg_flag.clone(), shift: shift_n.clone() },
                general_assembly::shift::Shift::Rrx => todo!(),
                general_assembly::shift::Shift::Ror => todo!()
            });)?
            $ret.push(
                Operation::Shift {
                    destination: $target.clone(),
                    operand: $reg.clone(),
                    shift_n,
                    shift_t,
            })
        }
    };
}

macro_rules! local {
    ($($id:ident),*) => {
        $(
            let $id = general_assembly::operand::Operand::Local(stringify!($id).to_owned());
        )*
    };
}
mod branch;
mod fp;
mod memory_access;
mod sarithmetic;
mod ssimd;
mod test;
mod uarithmetic;
mod usimd;

/// Simply forces the least significant bit to zero.
const REMOVE_LAST_BIT_MASK: u32 = !0b1;
/// Removes the GE fields from APSR.
const APSR_GE_CLEAR: u32 = !(0b1111 << 16);
pub trait Convert {
    fn convert(self, in_it_block: bool) -> Vec<Operation>;
}

impl Convert for (usize, V7Operation) {
    fn convert(self, in_it_block: bool) -> Vec<Operation> {
        crate::debug!("INSTRUCTION: {}", self.1.name());
        match self.1 {
            V7Operation::AdcImmediate(adc) => {
                // Ensure that all fields are used
                consume!((s.unwrap_or(false),rd,rn,imm) from adc);
                let (rd, rn, imm): (Option<Operand>, Operand, Operand) = (rd.local_into(), rn.local_into(), imm.local_into());
                let rd = rd.unwrap_or(rn.clone());
                pseudo!([
                    let result: u32 = rn adc imm;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        SetCFlag(rn, imm, adc);
                        SetVFlag(rn, imm, adc);
                    }
                    rd = result;
                ])
            }
            V7Operation::AdcRegister(adc) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd,
                        rn,
                        rm,
                        shift
                    ) from adc
                );
                let (rd, rn, rm) = (rd.local_into(), rn.local_into(), rm.local_into());
                let rd = rd.unwrap_or(rn.clone());
                local!(shifted);
                let mut ret = vec![];
                shift!(ret.shift rm -> shifted);
                pseudo!(ret.extend[
                    let result: u32 = rn adc shifted;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        SetCFlag(rn,shifted,adc);
                        SetVFlag(rn,shifted,adc);
                    }
                    rd = result;
                ]);
                ret
            }
            V7Operation::AddImmediate(add) => {
                consume!(
                    (
                      s.local_unwrap(in_it_block),
                      rd,
                      rn,
                      imm
                    ) from add
                );

                let (rd, rn, imm) = (rd.unwrap_or(rn).local_into(), rn.local_into(), imm.local_into());
                pseudo!([
                    let result:u32 = imm + rn;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        SetCFlag(imm,rn,add);
                        SetVFlag(imm,rn,add);
                    }
                    rd = result;
                ])
            }
            V7Operation::AddRegister(add) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd,
                        rn,
                        rm,
                        shift
                    ) from add
                );
                let should_jump = match rd {
                    Some(Register::PC) => true,
                    None => matches!(rn, Register::PC),
                    _ => false,
                };

                let (rd, rn, rm) = (rd.local_into(), rn.local_into(), rm.local_into());
                let rd = rd.unwrap_or(rn.clone());

                let mut ret = vec![];
                local!(shifted);
                shift!(ret.shift rm -> shifted);
                pseudo!(ret.extend[
                    let result:u32 = shifted + rn;
                    if (should_jump) {
                        // NOTE: Likely clears the pipeline.
                        result = result & REMOVE_LAST_BIT_MASK.local_into();
                        Jump(result);
                    } else {
                        if (s) {
                            SetNFlag(result);
                            SetZFlag(result);
                            SetCFlag(shifted,rn,add);
                            SetVFlag(shifted,rn,add);
                        }
                        rd = result;
                    }
                ]);
                ret
            }
            V7Operation::AddSPImmediate(add) => {
                consume!((
                        s.unwrap_or(false),
                        rd,
                        imm
                    ) from add
                );
                let (rd, imm) = (rd.unwrap_or(Register::SP).local_into(), imm.local_into());

                pseudo!([
                    let result = Register("SP") + imm;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        SetCFlag(Register("SP&"),imm,add);
                        SetVFlag(Register("SP&"),imm,add);
                    }
                    rd = result;
                ])
            }
            V7Operation::AddSPRegister(add) => {
                consume!(
                    (
                        s.unwrap_or(false),
                        rm,
                        rd,
                        shift
                    ) from add
                );
                let rd = rd.unwrap_or(rm);
                let s = match rd {
                    Register::PC => false,
                    _ => s,
                };
                let (rd, rm) = (rd.local_into(), rm.local_into());
                let mut ret = vec![];
                local!(shifted);
                shift!(ret.shift rm -> shifted);
                pseudo!(ret.extend[
                    let result = Register("SP&") + shifted;

                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        SetCFlag(Register("SP&"),shifted,add);
                        SetVFlag(Register("SP&"),shifted,add);
                    }
                    rd = result;
                ]);
                ret
            }
            V7Operation::Adr(adr) => {
                consume!((rd,imm,add) from adr);
                let (rd, imm) = (rd.local_into(), imm.local_into());
                pseudo!([
                    let aligned = Register("PC+") & 0xFFFFFFFC.local_into();

                    let result = aligned - imm;
                    if (add) {
                        result = aligned + imm;
                    }
                    rd = result;
                ])
            }
            V7Operation::AndImmediate(and) => {
                consume!(
                    (
                        s.unwrap_or(false),
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        imm.local_into(),
                        carry
                    ) from and
                );
                pseudo!([

                        let result:u32 = rn & imm;
                        rd:u32 = result;
                        if (s) {
                            SetNFlag(result);
                            SetZFlag(result);
                            Flag("C"):u1 = (carry.unwrap_or(false) as u32).local_into();
                        }
                ])
            }
            V7Operation::AndRegister(and) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd,
                        rn,
                        rm,
                        shift
                    ) from and
                );
                let (rd, rn, rm) = (rd.unwrap_or(rn).local_into(), rn.local_into(), rm.local_into());
                let mut ret = vec![];
                local!(shifted);
                if s {
                    shift!(ret.shift rm -> shifted set c for rm);
                } else {
                    shift!(ret.shift rm -> shifted);
                }
                pseudo!(ret.extend[
                    let result:u32 = rn & shifted;
                    rd:u32 = result;

                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                    }
                ]);
                ret
            }
            V7Operation::AsrImmediate(asr) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd,
                        rm,
                        imm
                    ) from asr
                );
                let (rd, rm, imm) = (rd.local_into(), rm.local_into(), imm.local_into());
                pseudo!([
                    rm:u32;
                    imm:u32;
                    let result:u32 = rm asr imm;

                    if (s) {
                        SetZFlag(result);
                        SetNFlag(result);
                        SetCFlag(rm,imm,rsa);
                    }
                    rd = result;
                ])
            }
            V7Operation::AsrRegister(asr) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd,
                        rm,
                        rn
                    ) from asr
                );
                let (rd, rm, rn) = (rd.local_into(), rm.local_into(), rn.local_into());
                let mut ret = vec![];
                pseudo!(ret.extend[
                    rm:u32 = rm;
                    let shift_n:u32 = Resize(rm<7:0>,u32);
                    let result = rn asr shift_n;
                    if (s) {
                        SetZFlag(result);
                        SetNFlag(result);
                        SetCFlag(rn,shift_n,rsa);
                    }
                    rd = result;
                ]);

                ret
            }
            V7Operation::B(b) => {
                consume!((condition,imm) from b);
                let (condition, imm): (general_assembly::condition::Condition, _) = (condition.local_into(), imm.local_into());
                pseudo!([
                    //let pc = Register("PC") + 4u32;
                    let target = Register("PC+") + imm;
                    target = target & REMOVE_LAST_BIT_MASK.local_into();
                    Jump(target,condition);
                ])
            }
            V7Operation::Bfc(bfc) => {
                consume!((rd,lsb,msb) from bfc);
                let rd = rd.local_into();
                let mask = !mask_dyn(lsb, msb);
                vec![Operation::And {
                    destination: rd.clone(),
                    operand1: rd,
                    operand2: Operand::Immediate(DataWord::Word32(mask)),
                }]
            }
            V7Operation::Bfi(bfi) => {
                consume!((rd,rn,lsb,msb) from bfi);
                let (rd, rn) = (rd.local_into(), rn.local_into());
                let diff = msb - lsb;
                let nmask = (!(mask_dyn(lsb, msb) << lsb)).local_into();
                assert!(msb >= lsb, "would be unpredictable");
                pseudo!([
                    rd:u32 = rd;
                    rn:u32 = rn;
                    rd = rd & nmask;
                    // Assume happy case here
                    // NOTE: These are assumed to be checked by the calle.
                    let intermediate:u32 = Resize(Resize(rn<diff:0>,u31),u32) << lsb.local_into();
                    rd |= intermediate;
                ])
            }
            V7Operation::BicImmediate(bic) => {
                consume!((s.unwrap_or(false),rd,rn,imm,carry) from bic);
                let (rd, rn, imm) = (rd.unwrap_or(rn).local_into(), rn.local_into(), imm.local_into());
                let mut ret = vec![];
                pseudo!(ret.extend[
                        let result:u32 = !imm;
                        result = rn & result;
                        rd = result;
                        if (s) {
                            SetNFlag(result);
                            SetZFlag(result);
                        }
                ]);
                if s {
                    if let Some(flag) = carry {
                        let flag: u32 = flag as u32;
                        pseudo!(ret.extend[
                            Flag("C"):u1 = flag.local_into();
                        ]);
                    }
                }
                ret
            }
            V7Operation::BicRegister(bic) => {
                consume!((
                        s.local_unwrap(in_it_block),
                        rd,
                        rn,
                        rm,
                        shift
                    ) from bic
                );

                let (rd, rn, rm) = (rd.unwrap_or(rn).local_into(), rn.local_into(), rm.local_into());
                let mut ret = vec![];
                local!(shifted);

                if s {
                    shift!(ret.shift rm -> shifted set c for rm);
                } else {
                    shift!(ret.shift rm -> shifted);
                }

                pseudo!(ret.extend[
                   let inv:u32 = !shifted;
                   let result = rn & inv;
                   rd = result;
                   if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                   }
                ]);
                ret
            }
            V7Operation::Bkpt(_) => vec![Operation::Nop],
            V7Operation::Bl(bl) => {
                consume!((imm) from bl);
                let imm = imm.local_into();
                pseudo!([
                        let next_instr_addr = Register("PC");
                        Register("LR") = next_instr_addr & REMOVE_LAST_BIT_MASK.local_into();
                        Register("LR") |= 0b1u32;
                        next_instr_addr += imm;
                        next_instr_addr = next_instr_addr & REMOVE_LAST_BIT_MASK.local_into();
                        Register("PC") = next_instr_addr;
                ])
            }
            V7Operation::Blx(blx) => {
                consume!((rm) from blx);
                let rm = rm.local_into();
                pseudo!([
                    let target:u32 = rm;
                    let next_instr_addr = Register("PC+") - 2.local_into();

                    Register("LR") = next_instr_addr & REMOVE_LAST_BIT_MASK.local_into();
                    Register("LR") |= 1.local_into();
                    Register("EPSR") = Register("EPSR") | (1 << 27).local_into();
                    target = target & REMOVE_LAST_BIT_MASK.local_into();
                    Register("PC+") = target;
                ])
            }

            V7Operation::Bx(bx) => {
                let rm = bx.rm.local_into();
                pseudo!([
                    let next_addr:u32 = rm;
                    next_addr = next_addr & REMOVE_LAST_BIT_MASK.local_into();
                    Register("PC+") = next_addr;
                ])
            }
            V7Operation::Cbz(cbz) => {
                consume!((
                    non.unwrap_or(false),
                    rn.local_into(),
                    imm
                    ) from cbz);
                let imm = imm.local_into();
                let non = (non as u32).local_into();
                pseudo!([
                    // These simply translate in to no ops
                    rn:u32;non:u32;
                    imm:u32;
                    let cmp:u1 = rn == 0u32;
                    let value:u1 = Resize(non,u1);
                    Ite(cmp != value,
                        {
                        let pc = Register("PC+");
                        let dest:u32 =  pc + imm;
                        dest = dest & REMOVE_LAST_BIT_MASK.local_into();
                        Jump(dest);
                        }, {}
                    );
                ])
            }
            V7Operation::Clrex(_) => todo!("This should not be needed for now"),
            V7Operation::Clz(clz) => {
                vec![Operation::CountLeadingZeroes {
                    destination: clz.rd.local_into(),
                    operand: clz.rm.local_into(),
                }]
            }
            V7Operation::CmnImmediate(cmn) => {
                consume!((rn,imm) from cmn);
                let (rn, imm) = (rn.local_into(), imm.local_into());
                pseudo!([
                    let result:u32 = rn + imm;
                    SetNFlag(result);
                    SetZFlag(result);
                    SetCFlag(rn,imm,add);
                    SetVFlag(rn,imm,add);
                ])
            }
            V7Operation::CmnRegister(cmn) => {
                consume!((rn,rm,shift) from cmn);
                let (rn, rm) = (rn.local_into(), rm.local_into());
                let mut ret = vec![];
                local!(shifted);
                shift!(ret.shift rm -> shifted);
                pseudo!(ret.extend[
                    let result:u32 = rn + shifted;
                    SetNFlag(result);
                    SetZFlag(result);
                    SetCFlag(rn,shifted,add);
                    SetVFlag(rn,shifted,add);
                ]);
                ret
            }
            V7Operation::CmpImmediate(cmp) => {
                consume!((rn,imm) from cmp);
                let (rn, imm) = (rn.local_into(), imm.local_into());
                pseudo!([
                    let result:u32 = rn - imm;
                    SetNFlag(result);
                    SetZFlag(result);
                    SetCFlag(rn,imm,sub);
                    SetVFlag(rn,imm,sub);
                ])
            }
            V7Operation::CmpRegister(cmp) => {
                consume!((rn,rm,shift) from cmp);
                let (rn, rm) = (rn.local_into(), rm.local_into());
                let mut ret = vec![];
                local!(shifted);
                shift!(ret.shift rm -> shifted);
                pseudo!(ret.extend[
                    let result:u32 = rn - shifted;
                    SetNFlag(result);
                    SetZFlag(result);
                    SetCFlag(rn,shifted,sub);
                    SetVFlag(rn,shifted,sub);
                ]);
                ret
            }
            V7Operation::Cps(cps) => {
                consume!((enable,disable,affect_pri,affect_fault) from cps);
                assert!(enable != disable);
                let mut ret = Vec::with_capacity(1);
                if enable {
                    if affect_pri {
                        // force lsb to 0
                        ret.push(Operation::Move {
                            destination: SpecialRegister::PRIMASK.local_into(),
                            source: ((0b0u32).local_into()),
                        })
                    }
                    if affect_fault {
                        // force lsb to 0
                        ret.push(Operation::Move {
                            destination: SpecialRegister::FAULTMASK.local_into(),
                            source: ((0b0u32).local_into()),
                        })
                    }
                } else {
                    if affect_pri {
                        // force lsb to 1
                        ret.push(Operation::Move {
                            destination: SpecialRegister::PRIMASK.local_into(),
                            source: ((0b1u32).local_into()),
                        })
                    }
                    if affect_fault {
                        ret.push(Operation::Move {
                            destination: SpecialRegister::FAULTMASK.local_into(),
                            source: ((0b1u32).local_into()),
                        })
                    }
                }
                ret
            }
            // TODO! Decide whether or not to use this
            V7Operation::Dbg(_) => vec![],
            V7Operation::Dmb(_) => {
                crate::warn!("DMB: This requires an exhaustive rewrite of the system to allow memory barriers");
                vec![]
            }
            V7Operation::Dsb(_) => {
                crate::warn!("DSB: This requires an exhaustive rewrite of the system to allow memory barriers");
                vec![]
            }
            V7Operation::EorImmediate(eor) => {
                consume!(
                    (
                        s.unwrap_or(false),
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        imm.local_into(),
                        carry
                    ) from eor
                );
                pseudo!([
                    let result:u32 = rn ^ imm;
                    rd = result;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        Flag("C") = (carry.unwrap_or(false) as u32).local_into();
                    }
                ])
            }
            V7Operation::EorRegister(eor) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd,
                        rn,
                        rm,
                        shift
                    ) from eor
                );
                let (rd, rn, rm) = (rd.unwrap_or(rn).local_into(), rn.local_into(), rm.local_into());
                let mut ret = Vec::with_capacity(10);
                local!(shifted);
                match s {
                    true => shift!(ret.shift rm -> shifted set c for rm),
                    false => shift!(ret.shift rm -> shifted),
                };
                pseudo!(ret.extend[
                    let result:u32 = rn ^ shifted;
                    rd = result;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                    }
                ]);
                ret
            }
            // NOTE: This is used in unanalyzable code. If the barrier fails we cannot loop
            // for ever.
            V7Operation::Isb(_) => {
                crate::warn!("Encountered ISB instruction. This cannot be analyzed, using a noop instead.");
                vec![]
            }
            V7Operation::It(it) => {
                // let bits = (it.conds.initial_bit_pattern as u32).local_into();
                // let drop_mask = (!0b1111_1111u32).local_into();
                let bits = (it.bit_pattern as u32).local_into();
                pseudo!([
                    // bits:u32;
                    // let it:u32 = Register("ITSTATE.IT") & drop_mask ;
                    Register("ITSTATE.IT") = bits;
                ])

                // vec![Operation::ConditionalExecution {
                // conditions: it.conds.conditions.into_iter().map(|el|
                // el.local_into()).collect(), }]
            }
            V7Operation::Ldm(ldm) => {
                consume!((
                        rn,
                        w.unwrap_or(false),
                        registers
                    ) from ldm
                );
                let mut prev: u8 = registers.registers[0].into();
                for el in &registers.registers {
                    let new: u8 = (*el).into();
                    assert!(new >= prev, "Register are not sorted!");
                    prev = new;
                }

                let w = w && !registers.registers.contains(&rn);
                let rn = rn.local_into();

                let bc = registers.registers.len() as u32;
                let mut contained = false;
                let mut to_read: Vec<Operand> = vec![];
                for reg in registers.registers.into_iter() {
                    if reg == Register::PC {
                        contained = true;
                    } else {
                        to_read.push(reg.local_into());
                    }
                }
                pseudo!([
                    rn:u32;
                    let address = rn;

                    for reg in to_read.into_iter() {
                        reg:u32 = LocalAddress(address,32);
                        address += 4.local_into();
                    }

                    if (contained) {
                        let target:u32 = LocalAddress(address,32);
                        target = target & REMOVE_LAST_BIT_MASK.local_into();
                        Jump(target);
                    }
                    if (w) {
                        rn += (4*bc).local_into();
                    }
                ])
            }
            V7Operation::Ldmdb(ldmdb) => {
                consume!(
                    (
                        rn,
                        w.unwrap_or(false),
                        registers
                    ) from ldmdb
                );

                let w = w && !registers.registers.contains(&rn);
                let rn = rn.local_into();

                let bc = registers.registers.len() as u32;
                let mut contained = false;
                let mut to_read: Vec<Operand> = vec![];
                for reg in registers.registers.into_iter() {
                    if reg == Register::PC {
                        contained = true;
                    } else {
                        to_read.push(reg.local_into());
                    }
                }

                pseudo!([
                    let address:u32 = rn - (4*bc).local_into();

                    for reg in to_read.into_iter() {
                        reg = LocalAddress(address,32);
                        address += 4.local_into();
                    }

                    if (contained) {
                        let target = LocalAddress(address,32);
                        target = target & REMOVE_LAST_BIT_MASK.local_into();
                        Jump(target);
                    }
                    if (w) {
                        rn -= (4*bc).local_into();
                    }
                ])
            }
            V7Operation::LdrImmediate(ldr) => {
                consume!((index,add,w.unwrap_or(false),rt,rn,imm) from ldr);
                let old_rt = rt;
                let is_pc = old_rt == Register::PC;
                let (rt, rn, imm) = (rt.local_into(), rn.local_into(), imm.local_into());

                pseudo!([
                    let offset_addr:u32 = rn - imm;
                    if (add) {
                        offset_addr = rn + imm;
                    }

                    let address = rn;
                    if (index) {
                        address = offset_addr;
                    }

                    let data:u32 = LocalAddress(address,32);

                    if (w) {
                        rn = offset_addr;
                    }

                    if (is_pc) {
                        data = data & REMOVE_LAST_BIT_MASK.local_into();
                        Jump(data);
                    }
                    else {
                        rt:u32 = data;
                    }
                ])
            }
            V7Operation::LdrLiteral(ldr) => {
                consume!(
                    (
                        rt,
                        imm.local_into(),
                        add
                    ) from ldr
                );
                let new_t = rt.local_into();
                pseudo!([
                    // Alling to 4
                    let base:u32 = Register("PC+")& 0xFFFFFFFC.local_into();

                    let address:u32 = base - imm;
                    if (add) {
                        address = base + imm;
                    }

                    let data:u32 = LocalAddress(address,32);
                    if (rt == Register::PC){
                        data = data & REMOVE_LAST_BIT_MASK.local_into();
                        Jump(data);
                    }
                    else {
                        new_t = data;
                    }
                ])
            }
            V7Operation::LdrRegister(ldr) => {
                consume!(
                    (
                        w.unwrap_or(false),
                        rt,
                        rn,
                        rm,
                        shift
                    ) from ldr
                );
                let _w = w;
                let rt_old = rt;
                let (rt, rn, rm) = (rt.local_into(), rn.local_into(), rm.local_into());
                let should_shift = shift.is_some();
                let shift = match shift {
                    Some(shift) => shift.shift_n as u32,
                    None => 0u32,
                }
                .local_into();
                pseudo!([
                   let offset:u32 = rm;
                   if (should_shift) {
                        offset = rm << shift;
                   }

                   let address = rn + offset;
                   let data = LocalAddress(address,32) ;

                   if (w) {
                        rn = address;
                   }

                   if (rt_old == Register::PC){
                       data = data & REMOVE_LAST_BIT_MASK.local_into();
                       Jump(data);
                   }
                   else {
                       rt = data;
                   }
                ])
            }
            V7Operation::LdrbImmediate(ldrb) => {
                consume!(
                    (
                        index,
                        add.unwrap_or(false),
                        w.unwrap_or(false),
                        rt,
                        rn,
                        imm
                    ) from ldrb
                );
                let imm = imm.unwrap_or(0);
                let (rt, rn, imm) = (rt.local_into(), rn.local_into(), imm.local_into());
                pseudo!([
                    let offset_addr:u32 = rn - imm;
                    if (add) {
                        offset_addr = rn + imm;
                    }

                    let address = rn;
                    if (index) {
                        address = offset_addr;
                    }

                    rt = ZeroExtend(LocalAddress(address,8),32);
                    if (w){
                        rn = offset_addr;
                    }
                ])
            }
            V7Operation::LdrbLiteral(ldrb) => {
                consume!((
                    add.unwrap_or(false),
                    rt.local_into(),
                    imm.local_into()
                    ) from ldrb);
                pseudo!([
                    let base = Register("PC+") & 0xFFFFFFFC.local_into();

                    let address = base - imm;
                    if (add) {
                        address = base + imm;
                    }

                    rt = ZeroExtend(LocalAddress(address,8),32);
                ])
            }
            V7Operation::LdrbRegister(ldrb) => {
                consume!((rt,rn,rm,shift,add.unwrap_or(false)) from ldrb);
                let (rt, rn, rm) = (rt.local_into(), rn.local_into(), rm.local_into());
                let shift = match shift {
                    Some(shift) => shift.shift_n as u32,
                    _ => 0,
                }
                .local_into();
                pseudo!([
                    let offset:u32 = rm << shift;
                    let offset_addr:u32 = rn - offset;
                    if (add) {
                        offset_addr = rn + offset;
                    }
                    // NOTE: Index is true in all encodings as of writing.
                    let address = offset_addr;
                    rt = ZeroExtend(LocalAddress(address,8),32);
                ])
            }
            V7Operation::Ldrbt(ldrbt) => {
                consume!((rt,rn,imm) from ldrbt);
                let (rt, rn, imm) = (rt.local_into(), rn.local_into(), imm.unwrap_or(0).local_into());
                pseudo!([
                    let address:u32 = rn + imm;
                    rt = ZeroExtend(LocalAddress(address,8),32);
                ])
            }
            V7Operation::LdrdImmediate(ldrd) => {
                consume!((
                    rt.local_into(),
                    rt2.local_into(),
                    rn.local_into(),
                    imm.local_into(),
                    add.unwrap_or(false),
                    index.unwrap_or(false),
                    w.unwrap_or(false)
                    ) from ldrd);
                pseudo!([
                    let offset_addr:u32 = rn - imm;
                    if (add) {
                        offset_addr = rn + imm;
                    }

                    let address = rn;
                    if (index) {
                        address = offset_addr;
                    }

                    rt = LocalAddress(address,32);
                    address += 4.local_into();
                    rt2 = LocalAddress(address,32);

                    if (w) {
                        rn = offset_addr;
                    }
                ])
            }
            V7Operation::LdrdLiteral(ldrd) => {
                consume!((
                    rt.local_into(),
                    rt2.local_into(),
                    imm.local_into(),
                    add.unwrap_or(false),
                    w.unwrap_or(false),
                    index.unwrap_or(false)) from ldrd);
                // These are not used in the pseudo code
                let (_w, _index) = (w, index);
                pseudo!([
                    let address:u32 = Register("PC+") - imm;
                    if (add) {
                        address = Register("PC+") + imm;
                    }
                    rt = LocalAddress(address,32);
                    address = address + 4.local_into();
                    rt2 = LocalAddress(address,32);
                ])
            }
            V7Operation::Ldrex(_) => todo!("Hardware semaphores"),
            V7Operation::Ldrexb(_) => todo!("Hardware semaphores"),
            V7Operation::Ldrexh(_) => todo!("Hardware semaphores"),
            V7Operation::LdrhImmediate(ldrh) => {
                consume!((
                        rt.local_into(),
                        rn.local_into(),
                        imm.local_into(),
                        add.unwrap_or(false),
                        w.unwrap_or(false),
                        index.unwrap_or(false)
                    ) from ldrh
                );
                pseudo!([
                    let offset_addr:u32 = rn - imm;
                    if (add) {
                        offset_addr = rn + imm;
                    }

                    let address = rn;
                    if (index) {
                        address = offset_addr;
                    }

                    let data = LocalAddress(address,16);
                    if (w){
                        rn = offset_addr;
                    }
                    rt = ZeroExtend(data,32);
                ])
            }
            V7Operation::LdrhLiteral(ldrh) => {
                consume!(
                    (
                        rt.local_into(),
                        imm.local_into(),
                        add.unwrap_or(false)
                    ) from ldrh
                );

                pseudo!([
                    let aligned:u32 = Register("PC+") & 0xFFFFFFFC.local_into();

                    let address:u32 = aligned - imm;
                    if (add) {
                        address = aligned + imm;
                    }

                    let data = LocalAddress(address,16);
                    rt = ZeroExtend(data,32);
                ])
            }
            V7Operation::LdrhRegister(ldrh) => {
                consume!(
                    (
                        rt.local_into(),
                        rn.local_into(),
                        rm.local_into(),
                        shift
                    ) from ldrh
                );

                let mut ret = Vec::with_capacity(10);
                let offset = Operand::Local("offset".to_owned());

                shift!(ret.shift rm -> offset);
                pseudo!(ret.extend[
                    let offset_addr:u32 = rn + offset;
                    let address = offset_addr;
                    let data:u32 = ZeroExtend(LocalAddress(address,16),32);
                    rt = data;
                ]);
                ret
            }
            V7Operation::Ldrht(ldrht) => {
                consume!(
                    (
                        rt.local_into(),
                        rn.local_into(),
                        imm.unwrap_or(0).local_into()
                    ) from ldrht
                );
                pseudo!([
                    let address:u32 = rn + imm;
                    let data = LocalAddress(address,16);
                    rt = ZeroExtend(data,32);
                ])
            }
            V7Operation::LdrsbImmediate(ldrsb) => {
                consume!((
                        rt.local_into(),
                        rn.local_into(),
                        imm.unwrap_or(0).local_into(),
                        add,
                        index,
                        wback
                    ) from ldrsb
                );
                pseudo!([
                    let offset_addr:u32 = rn - imm;
                    if (add) {
                        offset_addr = rn + imm;
                    }

                    let address = rn;
                    if (index) {
                        address = offset_addr;
                    }

                    rt = SignExtend(LocalAddress(address,8),8,32);
                    if (wback) {
                        rn = offset_addr;
                    }
                ])
            }
            V7Operation::LdrsbLiteral(ldrsb) => {
                consume!((
                        rt.local_into(),
                        imm.local_into(),
                        add
                    ) from ldrsb
                );
                pseudo!([
                    let base = Register("PC+") & 0xFFFFFFFC.local_into();

                    let address = base - imm;
                    if (add) {
                        address = base + imm;
                    }

                    rt = SignExtend(LocalAddress(address,8),8,32);
                ])
            }
            V7Operation::LdrsbRegister(ldrsb) => {
                consume!(
                    (
                        rt.local_into(),
                        rn.local_into(),
                        rm.local_into(),
                        shift
                    ) from ldrsb
                );
                let mut ret = Vec::with_capacity(10);
                let offset = Operand::Local("offset".to_owned());
                shift!(ret.shift rm -> offset);
                pseudo!(ret.extend[
                    let address:u32 = rn + offset;
                    rt = SignExtend(LocalAddress(address,8),8,32);
                ]);

                ret
            }
            V7Operation::Ldrsbt(ldrsbt) => {
                consume!(
                    (
                        rt.local_into(),
                        rn.local_into(),
                        imm.local_into()
                    ) from ldrsbt
                );

                let address_setter = Operand::Local("address".to_owned());
                let address = Operand::AddressInLocal("address".to_owned(), 8);

                vec![
                    Operation::Add {
                        destination: address_setter,
                        operand1: rn,
                        operand2: imm,
                    },
                    Operation::SignExtend {
                        destination: rt,
                        operand: address,
                        sign_bit: 8,
                        target_size: 32,
                    },
                ]
            }
            V7Operation::LdrshImmediate(ldrsh) => {
                consume!((rt.local_into(), rn.local_into(), imm.unwrap_or(0).local_into(), add, index, wback ) from ldrsh);
                let mut ret = Vec::with_capacity(10);
                let address_setter = Operand::Local("address".to_owned());
                let offset_address = Operand::Local("offset_address".to_owned());
                let address = Operand::AddressInLocal("address".to_owned(), 16);

                ret.push(match add {
                    true => Operation::Add {
                        destination: offset_address.clone(),
                        operand1: rn.clone(),
                        operand2: imm,
                    },
                    _ => Operation::Sub {
                        destination: offset_address.clone(),
                        operand1: rn.clone(),
                        operand2: imm,
                    },
                });

                ret.push(match index {
                    true => Operation::Move {
                        destination: address_setter.clone(),
                        source: offset_address.clone(),
                    },
                    _ => Operation::Move {
                        destination: address_setter.clone(),
                        source: rn.clone(),
                    },
                });

                if wback {
                    ret.push(Operation::Move {
                        destination: rn,
                        source: offset_address,
                    })
                }

                ret.extend([Operation::SignExtend {
                    destination: rt,
                    operand: address,
                    sign_bit: 16,
                    target_size: 32,
                }]);

                ret
            }
            V7Operation::LdrshLiteral(ldrsh) => {
                consume!(
                    (
                        rt.local_into(),
                        imm.local_into(),
                        add
                    ) from ldrsh
                );
                pseudo!([
                    let base:u32 = Register("PC+") & 0xFFFFFFFC.local_into();

                    let address:u32 = base - imm;
                    if (add) {
                        address = base + imm;
                    }

                    let data = LocalAddress(address,16);
                    rt = SignExtend(data,16,32);
                ])
            }
            V7Operation::LdrshRegister(ldrsh) => {
                consume!(
                    (
                        rt.local_into(),
                        rn.local_into(),
                        rm.local_into(),
                        shift
                    ) from ldrsh
                );
                let mut ret = Vec::with_capacity(10);
                let offset = Operand::Local("offset".to_owned());
                let address_setter = Operand::Local("address".to_owned());
                let offset_address = Operand::Local("offset_address".to_owned());
                let address = Operand::AddressInLocal("address".to_owned(), 16);

                shift!(ret.shift rm -> offset);

                ret.extend([
                    Operation::Add {
                        destination: offset_address.clone(),
                        operand1: rn,
                        operand2: offset,
                    },
                    Operation::Move {
                        destination: address_setter.clone(),
                        source: offset_address,
                    },
                    Operation::Move {
                        destination: rt.clone(),
                        source: address,
                    },
                    Operation::SignExtend {
                        destination: rt.clone(),
                        operand: rt,
                        sign_bit: 16,
                        target_size: 32,
                    },
                ]);
                ret
            }
            V7Operation::Ldrsht(ldrsht) => {
                consume!(
                    (
                        rt.local_into(),
                        rn.local_into(),
                        imm.unwrap_or(0).local_into()
                    ) from ldrsht
                );
                let address_setter = Operand::Local("address".to_owned());
                let address = Operand::AddressInLocal("address".to_owned(), 16);
                vec![
                    Operation::Add {
                        destination: address_setter,
                        operand1: rn,
                        operand2: imm,
                    },
                    Operation::SignExtend {
                        destination: rt,
                        operand: address,
                        sign_bit: 16,
                        target_size: 32,
                    },
                ]
            }
            V7Operation::Ldrt(ldrt) => {
                consume!(
                    (
                        rt.local_into(),
                        rn.local_into(),
                        imm.unwrap_or(0).local_into()
                    ) from ldrt
                );
                let address_setter = Operand::Local("address".to_owned());
                let address = Operand::AddressInLocal("address".to_owned(), 32);
                vec![
                    Operation::Add {
                        destination: address_setter,
                        operand1: rn,
                        operand2: imm,
                    },
                    Operation::Move { destination: rt, source: address },
                ]
            }
            V7Operation::LslImmediate(lsl) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd.local_into(),
                        rm.local_into(),
                        imm
                    ) from lsl
                );
                let imm = (imm as u32).local_into();

                pseudo!([
                    let result:u32 = rm << imm;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        SetCFlag(rm, imm, lsl);
                    }
                    rd = result;
                ])
            }
            V7Operation::LslRegister(lsl) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from lsl
                );
                local!(shift_n);

                let mut ret = vec![Operation::And {
                    destination: shift_n.clone(),
                    operand1: rm,
                    operand2: 0xff.local_into(),
                }];
                let shift_t = Shift::Lsl.local_into();
                match s {
                    true => shift_imm!(ret.(shift_t,shift_n) rn -> rd set c for rn),
                    false => shift_imm!(ret.(shift_t,shift_n) rn -> rd),
                };

                pseudo!(
                    ret.extend[if (s) {
                        rd:u32 = rd;
                        SetNFlag(rd);
                        SetZFlag(rd);
                    }]
                );
                ret
            }
            V7Operation::LsrImmediate(lsr) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd.local_into(),
                        rm.local_into(),
                        imm
                    ) from lsr
                );
                let imm = (imm as u32).local_into();

                pseudo!([
                    let result:u32 = rm >> imm;

                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                        SetCFlag(rm, imm, rsl);
                    }

                    rd = result;
                ])
            }
            V7Operation::LsrRegister(lsr) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from lsr
                );
                local!(shift_n);
                let mut ret = vec![Operation::And {
                    destination: shift_n.clone(),
                    operand1: rm,
                    operand2: 0xff.local_into(),
                }];
                let shift_t = Shift::Lsr.local_into();
                match s {
                    true => shift_imm!(ret.(shift_t,shift_n) rn -> rd set c for rn),
                    false => shift_imm!(ret.(shift_t,shift_n) rn -> rd),
                };
                pseudo!(
                    ret.extend[if (s) {
                        rd:u32 = rd;
                        SetNFlag(rd);
                        SetZFlag(rd);
                    }]
                );
                ret
            }
            V7Operation::Mla(mla) => {
                consume!(
                    (
                        rn.local_into(),
                        ra.local_into(),
                        rd.local_into(),
                        rm.local_into()
                    ) from mla
                );
                let mut ret = Vec::with_capacity(3);
                pseudo!(
                    ret.extend[
                        rn:u32 = rn;
                        rm:u32 = rm;
                        ra:u32 = ra;
                        let operand1 = SignExtend(rn,32,64);
                        let operand2 = SignExtend(rm,32,64);
                        let add = SignExtend(ra,32,64);
                        let result = operand1*operand2;
                        result += add;
                        rd = Resize(result<31:0>, u32);
                    ]
                );
                ret
            }
            V7Operation::Mls(mls) => {
                consume!(
                    (
                        rn.local_into(),
                        ra.local_into(),
                        rd.local_into(),
                        rm.local_into()
                    ) from mls
                );
                let mut ret = Vec::with_capacity(3);
                pseudo!(
                    ret.extend[
                        rn:u32 = rn;
                        rm:u32 = rm;
                        ra:u32 = ra;
                        let operand1 = SignExtend(rn,32,64);
                        let operand2 = SignExtend(rm,32,64);
                        let add = SignExtend(ra,32,64);
                        let result = operand1*operand2;
                        result = add - result;
                        rd = Resize(result<31:0>, u32);
                    ]
                );
                ret
            }
            // One single encoding, this needs to be revisited once it is needed
            V7Operation::MovImmediate(mov) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd.local_into(),
                        imm.local_into(),
                        carry
                    ) from mov
                );
                pseudo!([
                    rd:u32 = imm;
                    if (s) {
                        SetNFlag(imm);
                        SetZFlag(imm);
                    }
                    if (s && carry.is_some()) {
                        Register("APSR.C") = (carry.expect("The if check is broken") as u32).local_into();
                    }
                ])
            }
            V7Operation::MovRegister(mov) => {
                consume!((s,rd, rm.local_into()) from mov);
                let is_pc = rd == Register::PC;
                let rd = rd.local_into();
                pseudo!([
                    rd:u32;rm:u32;
                    // NOTE: This likely clears the pipeline!
                    //
                    // see ALUWritePC
                    if (is_pc) {
                       let dest:u32 = rm & REMOVE_LAST_BIT_MASK.local_into();
                       Jump(dest);
                    }

                    let result = rm;
                    rd:u32 = result;
                    if (s.is_some_and(|el| el)) {
                        Flag("N") = result<31>;
                        Flag("Z") = result == 0u32;
                    }
                ])
            }
            V7Operation::Movt(movt) => {
                consume!((rd.local_into(),imm) from movt);
                let imm = (imm as u32).local_into();
                let shift = 16.local_into();
                pseudo!([
                    let intermediate:u32 = imm << shift;
                    // Preserve the lower half word
                    rd:u32 = rd;
                    rd = intermediate | Resize(rd<15:0>,u32);
                ])
            }
            V7Operation::Mrs(mrs) => {
                consume!(
                (
                    rd.local_into(),
                    sysm
                ) from mrs
                );
                pseudo!([
                rd:u32 = 0.local_into();

                if (((sysm>>3) & 0b11111) == 0 && (sysm&0b1 == 0)) {
                    rd = Register("IPSR");
                    rd = Resize(rd<8:0>,u32);
                }
                // Ignoring the Epsr read as it evaluates to the same as RD already
                // contains
                if (((sysm>>3) & 0b11111) == 0 && (sysm & 0b10 == 0)) {
                    let intermediate = Register("APSR");
                    intermediate <<= 27.local_into();
                    rd |= intermediate;
                    // TODO! Add in DSP extension
                }
                if (((sysm>>3) & 0b11111) == 1 && (sysm & 0b100 == 0)) {
                    // TODO! Need to track whether or not the mode is priv
                }

                let primask = Register("PRIMASK");
                let basepri = Register("BASEPRI");
                let faultmask = Register("FAULTMASK");

                if (((sysm>>3) & 0b11111) == 2 && (sysm & 0b111 == 0)) {
                    // TODO! Add in priv checks
                    let intermediate:u32 = (!1u32).local_into();
                    rd &= intermediate;
                    rd |= Resize(primask<0:0>,u32);
                }

                if (((sysm>>3) & 0b11111) == 2 && (sysm & 0b111 == 1)) {
                    // TODO! Add in priv checks
                    let intermediate:u32 = (!0b1111111u32).local_into();
                    rd &= intermediate;
                    rd |= Resize(basepri<7:0>,u32);
                }

                if (((sysm>>3) & 0b11111) == 2 && (sysm & 0b111 == 2)) {
                    // TODO! Add in priv checks
                    let intermediate:u32 = (!0b1111111u32).local_into();
                    rd &= intermediate;
                    rd |= Resize(basepri<7:0>,u32);
                }

                if (((sysm>>3) & 0b11111) == 2 && (sysm & 0b111 == 3)) {
                    // TODO! Add in priv checks
                    let intermediate:u32 = (!1u32).local_into();
                    rd &= intermediate;
                    rd |= Resize(faultmask<0:0>,u32);
                }

                if (((sysm>>3) & 0b11111) == 2 && (sysm & 0b111 == 4)) {
                    // TODO! Add in floating point support
                }
                ])
            }
            V7Operation::Msr(msr) => {
                consume!(
                (
                    rn.local_into(),
                    sysm,
                    mask
                ) from msr
                );
                let mask: u32 = mask.into();
                let apsr = SpecialRegister::APSR.local_into();
                let primask = SpecialRegister::PRIMASK.local_into();
                let basepri = SpecialRegister::BASEPRI.local_into();
                let faultmask = SpecialRegister::FAULTMASK.local_into();

                pseudo!([
                    sysm:u32 = sysm;
                    apsr:u32 = apsr;
                    rn:u32 = rn;
                    primask:u32 = primask;
                    basepri:u32;
                    faultmask:u32 = faultmask;
                    if (((sysm>>3) & 0b11111) == 0 && (sysm&0b100 == 0)) {
                        if (mask & 0b10 == 2) {
                            apsr = Resize(apsr<27:0>,u32);
                            let intermediate = Resize(rn<31:27>,u32)<<27.local_into();
                            apsr |= intermediate;
                        }
                    }
                    // Discarding the SP things for now
                    // TODO! add in SP things, it is worth noting that this is
                    // for privileged execution only.
                    if (((sysm>>3) & 0b11111) == 2 && (sysm & 0b111 == 0)) {
                        // TODO! Add in priv checks
                        let primask_intermediate = primask & REMOVE_LAST_BIT_MASK.local_into();
                        let intermediate = Resize(rn<0:0>,u32);
                        apsr = primask_intermediate | intermediate;
                    }
                    if (((sysm>>3) & 0b11111) == 2 && (sysm&0b111 == 1)) {
                        // TODO! Add in priv checks
                        let basepri_intermediate= Resize(basepri<31:8>,u32) << 8.local_into();
                        let intermediate = Resize(rn<7:0>,u32);
                        basepri = basepri_intermediate | intermediate;
                    }
                    if (((sysm>>3) & 0b11111) == 2 && (sysm&0b111 == 2)) {
                        // TODO! Add in priv checks
                        let cond = rn<7:0> < basepri<7:0>;
                        let cond2 = basepri<7:0> == 0u8;
                        cond |= cond2;
                        Ite( cond == true ,
                            {
                                let basepri_intermediate = Resize(basepri<31:8>,u32) << 8.local_into();
                                let intermediate = Resize(rn<7:0>,u32);
                                basepri = basepri_intermediate | intermediate;
                            },
                            {}
                        );
                    }
                    if (((sysm>>3) & 0b11111) == 2 && (sysm&0b111 == 2)) {
                        // TODO! Add om priv and priority checks here
                        let faultmask_intermediate = faultmask & REMOVE_LAST_BIT_MASK.local_into();
                        let intermediate = Resize(rn<0:0>,u32);
                        faultmask = faultmask_intermediate | intermediate;
                    }
                ])
            }
            V7Operation::Mul(mul) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rn,
                        rd.unwrap_or(rn).local_into(),
                        rm.local_into()
                    ) from mul
                );
                let rn = rn.local_into();
                pseudo!(
                    [
                     rd:u32 = rn * rm;
                     if (s) {
                        SetZFlag(rd);
                        SetNFlag(rd);
                    }]
                )
            }
            V7Operation::MvnImmediate(mvn) => {
                consume!(
                    (
                        s.unwrap_or(false),
                        rd.local_into(),
                        imm.local_into(),
                        carry
                    ) from mvn
                );
                pseudo!([
                    let result:u32 = !imm;
                    rd  = result;
                    if (s) {
                        SetNFlag(result);
                        SetZFlag(result);
                    }
                    if (s && carry.is_some()){
                        let flag:u1 = (carry.unwrap() as u32).local_into();
                        Flag("C") = flag;
                    }
                ])
            }
            V7Operation::MvnRegister(mvn) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd.local_into(),
                        rm.local_into(),
                        shift
                    ) from mvn
                );
                let mut ret = Vec::with_capacity(5);
                local!(shifted);
                match s {
                    true => shift!(ret.shift rm -> shifted set c for rm),
                    false => shift!(ret.shift rm -> shifted),
                }
                pseudo!(ret.extend[
                    rd:u32 = !shifted;
                    if (s) {
                        SetNFlag(rd);
                        SetZFlag(rd);
                    }
                ]);
                ret
            }
            V7Operation::Nop(_) => vec![Operation::Nop],
            V7Operation::OrnImmediate(orn) => {
                consume!((
                    rn.local_into(),
                    rd.local_into().unwrap_or(rn.clone()),
                    imm.local_into(),
                    carry,
                    s.unwrap_or(false)
                    ) from orn);
                pseudo!([
                        let n_imm:u32 = !imm;
                        let result:u32 = rn | n_imm;
                        rd = result;

                        if (s) {
                            SetNFlag(result);
                            SetZFlag(result);
                        }
                        if (s && carry.is_some()){
                            let flag:u1 = (carry.unwrap() as u32).local_into();
                            Flag("C") = flag;
                        }
                ])
            }
            V7Operation::OrnRegister(orn) => {
                consume!(
                    (
                        s.unwrap_or(false),
                        rd,
                        rm.local_into(),
                        rn,
                        shift
                    ) from orn
                );
                let (rd, rn) = (rd.unwrap_or(rn).local_into(), rn.local_into());
                let mut ret = Vec::with_capacity(5);
                local!(shifted);
                match s {
                    true => shift!(ret.shift rm -> shifted set c for rm),
                    false => shift!(ret.shift rm -> shifted),
                }
                pseudo!(ret.extend[
                    shifted:u32 = !shifted;
                    rd = rn | shifted;

                    if (s) {
                        SetNFlag(rd);
                        SetZFlag(rd);
                    }
                ]);
                ret
            }
            V7Operation::OrrImmediate(orr) => {
                consume!((
                    rn.local_into(),
                    rd.local_into().unwrap_or(rn.clone()),
                    imm.local_into(),
                    carry,
                    s.unwrap_or(false)
                    ) from orr);
                pseudo!([
                        let result:u32 = rn | imm;
                        rd = result;

                        if (s) {
                            SetNFlag(result);
                            SetZFlag(result);
                        }
                        if (s && carry.is_some()){
                            let flag:u1 = (carry.unwrap() as u32).local_into();
                            Flag("C") = flag;
                        }

                ])
            }
            V7Operation::OrrRegister(orr) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd,
                        rm.local_into(),
                        rn,
                        shift
                    ) from orr
                );
                let (rd, rn) = (rd.unwrap_or(rn).local_into(), rn.local_into());
                let mut ret = Vec::with_capacity(10);
                local!(shifted);
                match s {
                    true => shift!(ret.shift rm -> shifted set c for rm),
                    false => shift!(ret.shift rm -> shifted),
                }
                pseudo!(ret.extend[
                    let result:u32 = rn | shifted;
                    rd:u32 = result;
                    if (s) {
                        Flag("APSR.N") = result<31>;
                        Flag("APSR.Z") = result == 0u32;
                    }
                ]);
                ret
            }
            V7Operation::Pkh(pkh) => {
                consume!((rd,shift,rn,rm.local_into(),tb) from pkh);
                let mut ret = Vec::with_capacity(5);
                let (rd, rn) = (rd.unwrap_or(rn).local_into(), rn.local_into());
                local!(shifted);
                shift!(ret.shift rm -> shifted);
                let (msh, lsh) = match tb {
                    true => (rn, shifted),
                    _ => (shifted, rn),
                };
                pseudo!(
                    ret.extend[
                        lsh:u32 = lsh & (u16::MAX as u32).local_into();
                        msh:u32 = msh & (!(u16::MAX as u32)).local_into();
                        rd = msh | lsh;
                    ]
                );
                ret
            }
            V7Operation::PldImmediate(_pld) => {
                // NOTE:
                // This should be logged in the ARMv7 struct so we can know that the address
                // was preloaded in the cycle estimates.
                todo!("We need some speciality pre load instruction here")
            }
            V7Operation::PldLiteral(_) => unimplemented!(" We need some speciality pre load instruction here"),
            V7Operation::PldRegister(_) => unimplemented!(" We need some speciality pre load instruction here"),
            V7Operation::PliImmediate(_) => unimplemented!(" We need some speciality pre load instruction here"),
            V7Operation::PliRegister(_) => unimplemented!(" We need some speciality pre load instruction here"),
            V7Operation::Pop(pop) => {
                consume!((registers) from pop);

                let mut jump = false;
                let mut to_pop = Vec::with_capacity(registers.registers.len());
                let bc = registers.registers.len() as u32;
                for reg in registers.registers {
                    if reg == Register::PC {
                        jump = true;
                    } else {
                        to_pop.push(reg.local_into());
                    }
                }

                let ret = pseudo!([
                    let address = Register("SP");

                    for reg in to_pop.into_iter(){
                        reg = LocalAddress(address,32);
                        address += 4.local_into();
                    }
                    if (jump) {
                        address = LocalAddress(address,32);
                        address = Resize(address<31:1>,u32) << 1u32;
                        Register("PC") = address;
                    }

                    // NOTE: This is not according to the spec. The spec breaks memory safety
                    // for non atomic operations. As we do not model GA as atomic we need to
                    // correct this.
                    Register("SP") += (4*bc).local_into();
                ]);
                ret
            }
            V7Operation::Push(push) => {
                consume!((registers) from push);
                assert!(!registers.registers.contains(&Register::SP), "Cannot push SP");
                assert!(!registers.registers.contains(&Register::PC));

                let n = registers.registers.len() as u32;
                pseudo!([
                    let address = Register("SP") - (4*n).local_into();
                    // NOTE: This is not according to the spec. The spec breaks memory safety
                    // for non atomic operations. As we do not model GA as atomic we need to
                    // correct this.
                    Register("SP") -= (4*n).local_into();

                    for reg in registers.registers {
                        LocalAddress(address,32) = reg.local_into();
                        address += 4.local_into();
                    }
                ])
            }
            V7Operation::Qadd(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qadd16(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qadd8(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qasx(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qdadd(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qdsub(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qsax(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qsub(_) => {
                todo!("Need to add in the flags APSR.Q");
            }
            V7Operation::Qsub16(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Qsub8(_) => todo!("Need to figure out how to do saturating operations"),
            V7Operation::Rbit(rbit) => {
                consume!((rd.local_into(),rm.local_into()) from rbit);
                pseudo!([
                    rd:u32;
                    rm:u32;
                    let result = 0u32;
                    let source = rm;
                    for _ignored in 0..32u32 {
                        let val = source<0>;
                        source >>= 1u32;
                        result <<= 1u32;
                        result |= Resize(val,u32);
                    }
                    rd = result;
                ])
            }
            V7Operation::Rev(rev) => {
                consume!((rd.local_into(),rm.local_into()) from rev);
                local!(int1, int2, int3, int4);
                let mut ret = vec![];
                let zero = 0.local_into();
                pseudo!(
                ret.extend[
                rm:u32 = rm;
                rd:u32 = rd;
                int1 = Resize(rm<7:0>,u32);
                int2 = Resize(rm<15:8>,u32);
                int3 = Resize(rm<23:16>,u32);
                int4 = Resize(rm<31:24>,u32);
                int1 = int1 << (24).local_into();
                int2 = int2 << (16).local_into();
                int3 = int3 << 8.local_into();
                int4 = int4;
                rd = zero;
                rd = rd | int1;
                rd = rd | int2;
                rd = rd | int3;
                rd = rd | int4;
                ]
                );

                ret
            }
            V7Operation::Rev16(rev) => {
                consume!((rd.local_into(),rm.local_into()) from rev);
                pseudo!([
                        rm:u32;
                        rd:u32;
                        let r1 = Resize(rm<23:16>,u32) << 24.local_into();
                        let r2 = Resize(rm<31:24>,u32) << 16.local_into();
                        let r3 = Resize(rm<7:0>,u32) << 8.local_into();
                        let r4 = Resize(rm<15:8>,u32);
                        let result = r1 | r2;
                        result |= r3;
                        result |= r4;
                        rd = result;
                ])
            }
            V7Operation::Revsh(revsh) => {
                consume!((rd.local_into(),rm.local_into()) from revsh);
                pseudo!([
                    rd:i32;
                    rm:i32;
                    let result:i32 = SignExtend(rm<7:0>, 7,32) << 8.local_into();
                    let intermediate = Resize(rm<15:8>,i32);
                    result |= intermediate;
                    rd = result;
                ])
            }
            V7Operation::RorImmediate(ror) => {
                consume!((s,rd.local_into(), rm.local_into(),imm) from ror);
                let shift_n = imm.local_into();
                let mut ret = vec![Operation::Sror {
                    destination: rd.clone(),
                    operand: rm.clone(),
                    shift: shift_n.clone(),
                }];
                if let Some(true) = s {
                    ret.extend([Operation::SetZFlag(rd.clone()), Operation::SetNFlag(rd.clone()), Operation::SetCFlagRor(rd.clone())]);
                }
                ret
            }
            V7Operation::RorRegister(ror) => {
                consume!(
                    (
                        s.local_unwrap(in_it_block),
                        rd.local_into(),
                        rm.local_into(),
                        rn.local_into()
                    ) from ror
                );
                local!(shift_n);
                let mask = (u8::MAX as u32).local_into();

                let mut ret = vec![
                    Operation::And {
                        destination: shift_n.clone(),
                        operand1: rm.clone(),
                        operand2: mask,
                    },
                    Operation::Sror {
                        destination: rd.clone(),
                        operand: rn.clone(),
                        shift: shift_n.clone(),
                    },
                ];
                if s {
                    ret.extend([Operation::SetZFlag(rd.clone()), Operation::SetNFlag(rd.clone()), Operation::SetCFlagRor(rd.clone())]);
                }
                ret
            }
            V7Operation::Rrx(rrx) => {
                consume!((s,rd.local_into(), rm.local_into()) from rrx);
                // Let's fulhacka
                let mask = (u32::MAX >> 1).local_into();
                let lsb_mask = (1).local_into();
                local!(lsb, result, msb);
                let carry = Operand::Flag("C".to_owned());
                let mut ret = Vec::with_capacity(10);
                pseudo!(
                ret.extend[
                    rm:u32;
                    lsb_mask:u32;
                    msb:u32;
                    lsb = rm & lsb_mask;
                    result = rm >> 1.local_into();
                    msb = carry << 31.local_into();
                    // Clear the bit first
                    result = result & mask;
                    result = result | msb;
                    rd = result;
                ]
                );

                if let Some(true) = s {
                    ret.extend([Operation::SetNFlag(result.clone()), Operation::SetZFlag(result.clone()), Operation::Move {
                        destination: carry,
                        source: lsb,
                    }]);
                }
                ret
            }
            V7Operation::RsbImmediate(rsb) => {
                consume!((s,rd,rn,imm.local_into()) from rsb);
                let (rd, rn) = (rd.unwrap_or(rn).local_into(), rn.local_into());
                let s = s.local_unwrap(in_it_block);

                pseudo!([
                    let result:u32 = imm - rn;

                    if (s) {
                        SetZFlag(result);
                        SetNFlag(result);
                        SetVFlag(imm,rn,sub);
                        SetCflag(imm,rn,sub);
                    }

                    // In case rn == rd
                    rd = result;

                ])
            }
            V7Operation::RsbRegister(rsb) => {
                consume!((s,rd,rn,rm.local_into(), shift) from rsb);
                let (rd, rn) = (rd.unwrap_or(rn).local_into(), rn.local_into());
                let mut ret = Vec::with_capacity(10);
                let carry = Operand::Flag("C".to_owned());
                let one = 1.local_into();

                local!(shifted, intermediate, old_carry);
                shift!(ret.shift rm -> shifted);

                pseudo!(
                ret.extend[
                // Backup carry bit
                old_carry:u32 = carry;
                // Set carry  bit to 1
                carry:u32 = one;

                intermediate:u32 = !rn;

                // add with carry
                rd = intermediate adc shifted;
                ]
                );
                ret.extend(match s {
                    Some(true) => {
                        vec![Operation::SetZFlag(rd.clone()), Operation::SetNFlag(rd.clone()), Operation::SetCFlag {
                            operand1: intermediate,
                            operand2: shifted,
                            sub: false,
                            carry: true,
                        }]
                    }
                    _ => pseudo!([carry:u1 = old_carry;]),
                });

                ret
            }
            V7Operation::Sadd16(sadd) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from sadd);
                pseudo!(
                    [
                        rm:i32 = rm;
                        rn:i32 = rn;
                        let inner = Resize(rn<15:0>,i16) + Resize(rm<15:0>,i16);
                        let sum1 = ZeroExtend(inner,32);
                        inner = Resize(rn<31:16>,i16) + Resize(rm<31:16>,i16);
                        let sum2 = ZeroExtend(inner,32);
                        rd = ZeroExtend(sum1<15:0>,32);
                        let masked = ZeroExtend(sum2<15:0>,32) << 16.local_into();
                        rd = rd | masked;

                        sum1 = !sum1;
                        sum2 = !sum2;

                        let sign1 = Resize(sum1<15:15>,u32);
                        let sign1_bit2 = Resize(sign1,u32) << 1.local_into();
                        let sign2 = Resize(sum2<15:15>,u32) << 2.local_into();
                        let sign2_bit2 = Resize(sign2,u32) << 1.local_into();

                        let ge:u32 = 0.local_into();
                        ge |= sign1;
                        ge |= sign1_bit2;
                        ge |= sign2;
                        ge |= sign2_bit2;

                        let old_value = Register("APSR");
                        old_value &= APSR_GE_CLEAR.local_into();
                        ge <<= 16.local_into();
                        Register("APSR") = old_value | ge;
                    ]
                )
            }
            V7Operation::Sadd8(sadd) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from sadd);
                pseudo!([
                        rn:u32 = rn;
                        rm:u32 = rm;
                        let inner = Resize(rn<7:0>,i8) + Resize(rm<7:0>,i8);
                        let sum1 = ZeroExtend(inner,32);
                        inner = Resize(rn<15:8>,i8) + Resize(rm<15:8>,i8);
                        let sum2 = ZeroExtend(inner,32);
                        inner =  Resize(rn<23:16>,i8) + Resize(rm<23:16>,i8);
                        let sum3 = ZeroExtend(inner,32);
                        inner = Resize(rn<31:24>,i8) + Resize(rm<31:24>,i8);
                        let sum4 = ZeroExtend(inner,32);
                        rd = ZeroExtend(sum1<7:0>,32);
                        let masked = ZeroExtend(sum2<7:0>,32) << 8.local_into();
                        rd = rd | masked;
                        masked = ZeroExtend(sum3<7:0>,32) << 16.local_into();
                        rd = rd | masked;
                        masked = ZeroExtend(sum4<7:0>,32) << 24.local_into();
                        rd = rd | masked;

                        // Get the inverted sign values to set the ge flag.
                        sum1 = !sum1;
                        sum2 = !sum2;
                        sum3 = !sum3;
                        sum4 = !sum4;
                        let ge = Resize(sum1<7:7>,u32);
                        let sign2 = Resize(sum2<7:7>,u32) << 1.local_into();
                        ge |= sign2;
                        let sign3 = Resize(sum3<7:7>,u32) << 2.local_into();
                        ge |= sign3;
                        let sign4 = Resize(sum4<7:7>,u32) << 3.local_into();
                        ge |= sign4;

                        // Clear and insert the values in to apsr.
                        let old_value = Register("APSR");
                        old_value &= APSR_GE_CLEAR.local_into();
                        ge <<= 16.local_into();
                        Register("APSR") = old_value | ge;
                    ]
                )
            }
            V7Operation::Sasx(sasx) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from sasx);
                pseudo!(
                    [
                        rm:u32;
                        rn:u32;
                        let inner = Resize(rn<15:0>,i16) - Resize(rm<31:16>,i16);
                        let diff = ZeroExtend(inner,32);
                        inner = Resize(rn<31:16>,i16) + Resize(rm<15:0>,i16);
                        let sum  = ZeroExtend(inner,32);
                        rd = ZeroExtend(diff<15:0>,32);
                        let masked = ZeroExtend(sum<15:0>,32) << 16.local_into();
                        rd = rd | masked;

                        let sum1 = !diff;
                        let sum2 = !sum;
                        let sign1 = Resize(sum1<15:15>,u32);
                        let sign1_bit2 = sign1 << 1.local_into();
                        let sign2 = Resize(sum2<15:15>,u32) << 2.local_into();
                        let sign2_bit2 = sign2 << 1.local_into();

                        let ge:u32 = 0.local_into();
                        ge |= sign1;
                        ge |= sign1_bit2;
                        ge |= sign2;
                        ge |= sign2_bit2;

                        let old_value = Register("APSR");
                        old_value &= APSR_GE_CLEAR.local_into();
                        ge <<= 16.local_into();
                        Register("APSR") = old_value | ge;
                    ]
                )
            }
            V7Operation::SbcImmediate(sbc) => {
                consume!((
                        s.unwrap_or(false),
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        imm.local_into()
                        ) from sbc);
                let mut ret = Vec::with_capacity(7);
                pseudo!(ret.extend[
                    let intermediate:u32 = !imm;
                    let result = rn adc intermediate;
                    if (s) {
                        SetZFlag(result);
                        SetNFlag(result);
                        SetCFlag(rn,intermediate,adc);
                        SetVFlag(rn,intermediate,adc);
                    }
                    rd = result;
                ]);
                ret
            }
            V7Operation::SbcRegister(sbc) => {
                consume!((
                        s.local_unwrap(in_it_block),
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into(),
                        shift
                        ) from sbc);
                let mut ret = Vec::with_capacity(10);
                local!(shifted);
                shift!(ret.shift rm -> shifted);
                pseudo!(ret.extend[
                    let intermediate:u32 = !shifted;
                    let result = rn adc intermediate;
                    if (s) {
                        SetZFlag(result);
                        SetNFlag(result);
                        SetCFlag(rn,intermediate,adc);
                        SetVFlag(rn,intermediate,adc);
                    }
                    rd = result;
                ]);
                ret
            }
            V7Operation::Sbfx(sbfx) => {
                consume!((rd.local_into(), rn.local_into(), lsb, width) from sbfx);
                let mut ret = vec![];

                let msb = lsb + (width - 1);
                let mask = ((1 << (msb - lsb)) - 1) << lsb;

                pseudo!(
                ret.extend[
                let intermediate:u32 = rn & mask.local_into();
                intermediate = intermediate >> lsb.local_into();
                rd = SignExtend(intermediate,width,32);
                ]
                );
                ret
            }
            V7Operation::Sdiv(sdiv) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from sdiv);
                pseudo!([
                        let result:i32 = rn / rm;
                        rd = result;
                ])
            }
            V7Operation::Sel(sel) => sel.decode(in_it_block),
            V7Operation::Sev(_) => vec![],
            V7Operation::Shadd16(shadd) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from shadd);
                // TODO! Check that the overflow here is not problematic
                pseudo!([
                        rn:u32;
                        rm:u32;
                        let inner = Resize(rn<15:0>,i16) + Resize(rm<15:0>,i16);
                        let sum1 = ZeroExtend(inner,32);
                        inner = Resize(rn<31:16>,i16) + Resize(rm<31:16>,i16);
                        let sum2 = ZeroExtend(inner,32);
                        rd = sum1<16:1>;
                        let intemediate_result = sum2<16:1> << 16.local_into();
                        rd = rd | intemediate_result;
                ])
            }
            V7Operation::Shadd8(shadd) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from shadd);
                // TODO! Check that the overflow here is not problematic
                pseudo!([
                        rm:u32;
                        rn:u32;
                        rd:u32;
                        let inner = Resize(rn<7:0>,i8) + Resize(rm<7:0>,i8);
                        let sum1 = ZeroExtend(inner,32);
                        inner = Resize(rn<15:8>,i8) + Resize(rm<15:8>,i8);
                        let sum2 = ZeroExtend(inner,32);
                        inner = Resize(rn<23:16>,i8) + Resize(rm<23:16>,i8);
                        let sum3 = ZeroExtend(inner,32);
                        inner = Resize(rn<31:24>,i8) + Resize(rm<31:24>,i8);
                        let sum4 = ZeroExtend(inner,32);
                        rd = Resize(sum1<8:1>,u32);
                        let intemediate_result = Resize(sum2<8:1>,u32) << 8.local_into();
                        rd = rd | intemediate_result;
                        intemediate_result = Resize(sum3<8:1>,u32) << 16.local_into();
                        rd = rd | intemediate_result;
                        intemediate_result = Resize(sum4<8:1>,u32) << 24.local_into();
                        rd = rd | intemediate_result;
                ])
            }
            V7Operation::Shasx(shasx) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from shasx);
                // TODO! Check that the overflow here is not problematic
                pseudo!([
                        rn:u32 = rn;
                        rm:u32 = rm;
                        let inner = Resize(rn<15:0>,i16) - Resize(rm<31:16>,i16);
                        let diff = ZeroExtend(inner,32);
                        inner = Resize(rn<31:16>,i16) + Resize(rm<15:0>,i16);
                        let sum  = ZeroExtend(inner,32);
                        rd = diff<16:1>;
                        let intemediate_result = sum<16:1> << 16.local_into();
                        rd = rd | intemediate_result;
                ])
            }
            V7Operation::Shsax(shsax) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from shsax);
                // TODO! Check that the overflow here is not problematic
                pseudo!([
                        rn:u32 = rn;
                        rm:u32 = rm;
                        rd:u32 = rd;
                        let inner = Resize(rn<15:0>,i16) + Resize(rm<31:16>,i16);
                        let sum = ZeroExtend(inner,32);
                        inner = Resize(rn<31:16>,i16) - Resize(rm<15:0>,i16);
                        let diff  = ZeroExtend(inner,32);
                        rd = Resize(diff<16:1>,u32);
                        let intemediate_result = Resize(sum<16:1>,u32) << 16.local_into();
                        rd = rd | intemediate_result;
                ])
            }
            V7Operation::Shsub16(shsub) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from shsub);
                // TODO! Check that the overflow here is not problematic
                pseudo!([
                        rn:u32 = rn;
                        rm:u32 = rm;
                        rd:u32 = rd;
                        let inner = Resize(rn<15:0>,i16) - Resize(rm<15:0>,i16);
                        let diff1 = ZeroExtend(inner,32);
                        inner = Resize(rn<31:16>,i16) - Resize(rm<31:16>,i16);
                        let diff2 = ZeroExtend(inner,32);
                        rd = Resize(diff1<16:1>,u32);
                        let intemediate_result = Resize(diff2<16:1>,u32) << 16.local_into();
                        rd = rd | intemediate_result;
                ])
            }
            V7Operation::Shsub8(shsub) => {
                consume!((
                        rn.local_into(),
                        rd.local_into().unwrap_or(rn.clone()),
                        rm.local_into()
                        ) from shsub);
                // TODO! Check that the overflow here is not problematic
                //
                // // SInt()
                // // ======
                //integer SInt(bits(N) x)
                //result = 0;
                //for i = 0 to N-1
                //if x<i> == ‘1’ then result = result + 2^i;
                //if x<N-1> == ‘1’ then result = result - 2^N;
                //return result;
                //UInt(x) is the integer whose unsigned representation is x:
                // // UInt()
                // // ======
                //integer UInt(bits(N) x)
                //result = 0;
                //for i = 0 to N-1
                //if x<i> == ‘1’ then result = result + 2^i;
                //return result;
                pseudo!([
                        rn:u32 = rn;
                        rm:u32 = rm;
                        rd:u32 = rd;

                        let inner = Resize(rn<7:0>,i8) - Resize(rm<7:0>,i8);
                        let diff1 = ZeroExtend(inner,32);
                        inner = Resize(rn<15:8>,i8) - Resize(rm<15:8>,i8);
                        let diff2 = ZeroExtend(inner,32);
                        inner = Resize(rn<23:16>,i8) - Resize(rm<23:16>,i8);
                        let diff3 = ZeroExtend(inner,32);
                        inner = Resize(rn<31:24>,i8) - Resize(rm<31:24>,i8);
                        let diff4 = ZeroExtend(inner,32);
                        rd = Resize(diff1<8:1>,u32);
                        let intemediate_result = Resize(diff2<8:1>,u32) << 8.local_into();
                        rd = rd | intemediate_result;
                        intemediate_result = Resize(diff3<8:1>,u32) << 16.local_into();
                        rd = rd | intemediate_result;
                        intemediate_result = Resize(diff4<8:1>,u32) << 24.local_into();
                        rd = rd | intemediate_result;
                ])
            }
            V7Operation::Smla(smla) => smla.decode(in_it_block),
            V7Operation::Smlad(smlad) => smlad.decode(in_it_block),
            V7Operation::Smlal(smlal) => smlal.decode(in_it_block),
            V7Operation::SmlalSelective(smlal) => smlal.decode(in_it_block),
            V7Operation::Smlald(smlald) => smlald.decode(in_it_block),
            V7Operation::Smlaw(smlaw) => smlaw.decode(in_it_block),
            V7Operation::Smlsd(smlsd) => smlsd.decode(in_it_block),
            V7Operation::Smlsld(smlsld) => smlsld.decode(in_it_block),
            V7Operation::Smmla(smmla) => smmla.decode(in_it_block),
            V7Operation::Smmls(smmls) => smmls.decode(in_it_block),
            V7Operation::Smmul(smmul) => smmul.decode(in_it_block),
            V7Operation::Smuad(smuad) => smuad.decode(in_it_block),
            V7Operation::Smul(smul) => smul.decode(in_it_block),
            V7Operation::Smull(smull) => smull.decode(in_it_block),
            V7Operation::Smulw(smulw) => smulw.decode(in_it_block),
            V7Operation::Smusd(smusd) => smusd.decode(in_it_block),
            V7Operation::Ssat(_) => todo!("Need to revisit SInt"),
            V7Operation::Ssat16(_) => todo!("Need to revisit SInt"),
            V7Operation::Ssax(_) => todo!("Need to revisit SInt"),
            V7Operation::Ssub16(_) => todo!("Need to revisit SInt"),
            V7Operation::Ssub8(_) => todo!("Need to revisit SInt"),
            V7Operation::Stm(stm) => stm.decode(in_it_block),
            V7Operation::Stmdb(stmdb) => stmdb.decode(in_it_block),
            V7Operation::StrImmediate(str) => str.decode(in_it_block),
            V7Operation::StrRegister(str) => str.decode(in_it_block),
            V7Operation::StrbImmediate(strb) => strb.decode(in_it_block),
            V7Operation::StrbRegister(strb) => strb.decode(in_it_block),
            V7Operation::Strbt(strbt) => strbt.decode(in_it_block),
            V7Operation::StrdImmediate(strd) => strd.decode(in_it_block),
            V7Operation::Strex(strex) => strex.decode(in_it_block),
            V7Operation::Strexb(strexb) => strexb.decode(in_it_block),
            V7Operation::Strexh(strexh) => strexh.decode(in_it_block),
            V7Operation::StrhImmediate(strh) => strh.decode(in_it_block),
            V7Operation::StrhRegister(strh) => strh.decode(in_it_block),
            V7Operation::Strht(strht) => strht.decode(in_it_block),
            V7Operation::Strt(strt) => strt.decode(in_it_block),
            V7Operation::SubImmediate(sub) => sub.decode(in_it_block),
            V7Operation::SubRegister(sub) => sub.decode(in_it_block),
            V7Operation::SubSpMinusImmediate(sub) => sub.decode(in_it_block),
            V7Operation::SubSpMinusRegister(sub) => sub.decode(in_it_block),
            V7Operation::Sxtab(sxtab) => sxtab.decode(in_it_block),
            V7Operation::Sxtab16(sxtab) => sxtab.decode(in_it_block),
            V7Operation::Sxtah(sxtah) => sxtah.decode(in_it_block),
            V7Operation::Sxtb(sxtb) => sxtb.decode(in_it_block),
            V7Operation::Sxtb16(sxtb) => sxtb.decode(in_it_block),
            V7Operation::Sxth(sxth) => sxth.decode(in_it_block),
            V7Operation::Tb(tb) => tb.decode(in_it_block),
            V7Operation::TeqImmediate(teq) => teq.decode(in_it_block),
            V7Operation::TeqRegister(teq) => teq.decode(in_it_block),
            V7Operation::TstImmediate(tst) => tst.decode(in_it_block),
            V7Operation::TstRegister(tst) => tst.decode(in_it_block),
            V7Operation::Uadd16(uadd) => uadd.decode(in_it_block),
            V7Operation::Uadd8(uadd) => uadd.decode(in_it_block),
            V7Operation::Uasx(uasx) => uasx.decode(in_it_block),
            V7Operation::Ubfx(ubfx) => ubfx.decode(in_it_block),
            V7Operation::Udf(_) => vec![Operation::Abort {
                error: "Undefined instruction".to_string(),
            }],
            V7Operation::Udiv(udiv) => udiv.decode(in_it_block),
            V7Operation::Uhadd16(uhadd) => uhadd.decode(in_it_block),
            V7Operation::Uhadd8(uhadd) => uhadd.decode(in_it_block),
            V7Operation::Uhasx(uhasx) => uhasx.decode(in_it_block),
            V7Operation::Uhsax(uhsax) => uhsax.decode(in_it_block),
            V7Operation::Uhsub16(uhsub) => uhsub.decode(in_it_block),
            V7Operation::Uhsub8(uhsub) => uhsub.decode(in_it_block),
            V7Operation::Umaal(umaal) => umaal.decode(in_it_block),
            V7Operation::Umlal(umlal) => {
                consume!(
                (
                    rdlo.local_into(),
                    rdhi.local_into(),
                    rn.local_into(),
                    rm.local_into()
                ) from umlal
                );
                pseudo!([
                    rn:u32;
                    rm:u32;
                    rdlo:u32;
                    rdhi:u32;
                    let result = ZeroExtend(rn,64)*ZeroExtend(rm,64);

                    // Compose the rd
                    let thirtytwo:u32 = 32.local_into();
                    let rd_composite = Resize(rdhi,u64) << Resize(thirtytwo, u64);
                    rd_composite = rd_composite | Resize(rdlo,u64);

                    result = result + rd_composite;

                    rdhi = Resize(result<63:32:u64>,u32);
                    rdlo = Resize(result<32:0:u64>,u32);
                ])
            }
            V7Operation::Umull(umull) => {
                consume!(
                (
                    rdlo.local_into(),
                    rdhi.local_into(),
                    rn.local_into(),
                    rm.local_into()
                ) from umull
                );
                pseudo!([
                    rn:u32;
                    rm:u32;
                    rdhi:u32;
                    rdlo:u32;
                    let result = ZeroExtend(rn,64)*ZeroExtend(rm,64);
                    rdhi = Resize(result<63:32>,u32);
                    rdlo = Resize(result<31:0>,u32);
                ])
            }
            V7Operation::Uqadd16(uquadd) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from uquadd
                );

                let rd = rd.unwrap_or(rn.clone());
                let max = (u16::MAX as u32).local_into();
                pseudo!([
                    rd:u32;
                    rn:u32;
                    rm:u32;
                    max:u32;
                    let sum1_small = resize(rn<15:0>,u16) sadd resize(rm<15:0>,u16);
                    let sum2_small = resize(rn<31:16>,u16) sadd resize(rm<31:16>,u16);
                    let sum1 = resize(sum1_small,u32);
                    let sum2 = resize(sum2_small,u32);
                    Ite(sum1 >= max,
                        {
                            sum1 = max;
                        },
                        {
                        }
                    );
                    Ite(sum2 >= max,
                        {
                            sum2 = max;
                        },
                        {
                        }
                    );
                    rd = sum2 << (16.local_into());
                    rd |= sum1;
                ])
            }
            V7Operation::Uqadd8(uquadd) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from uquadd
                );

                let rd = rd.unwrap_or(rn.clone());
                pseudo!([
                    rn:u32;
                    rm:u32;
                    rd:u32;
                    let sum1_small = resize(rn<7:0>,u8) sadd resize(rm<7:0>,u8);
                    let sum1 = resize(sum1_small,u32);
                    let sum2_small = resize(rn<15:8>,u8) sadd resize(rm<15:8>,u8);
                    let sum2 = resize(sum2_small,u32);
                    let sum3_small = resize(rn<23:16>,u8) sadd resize(rm<23:16>,u8);
                    let sum3 = resize(sum3_small,u32);
                    let sum4_small = resize(rn<31:24>,u8) sadd resize(rm<31:24>,u8);
                    let sum4 = resize(sum4_small,u32);

                    rd = sum4 << (24.local_into());
                    sum3 <<= (16.local_into());
                    rd |= sum3;
                    sum2 <<= (8.local_into());
                    rd |= sum2;
                    rd |= sum1;
                ])
            }
            V7Operation::Uqasx(uq) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from uq
                );
                let rd = rd.unwrap_or(rn.clone());

                pseudo!([
                    rn:u32;
                    rm:u32;
                    let diff = resize(rn<15:0>,u16) ssub resize(rm<31:16>,u16);
                    let sum = resize(rn<31:16>,u16) sadd resize(rm<15:0>,u16);
                    let diff_result = resize(diff, u32);
                    let sum_result = resize(sum, u32);
                    sum_result <<= 16.local_into();
                    rd = diff_result | sum_result;
                ])
            }
            V7Operation::Uqsax(uq) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from uq
                );
                let rd = rd.unwrap_or(rn.clone());

                pseudo!([
                    rn:u32;
                    rm:u32;
                    rd:u32;
                    let sum = resize(rn<15:0>,u16) sadd resize(rm<31:16>,u16);
                    let diff = resize(rn<31:16>,u16) ssub resize(rm<15:0>,u16);
                    let diff_result = resize(diff, u32);
                    let sum_result = resize(sum, u32);
                    diff_result = diff_result << 16.local_into();
                    rd = diff_result | sum_result;
                ])
            }
            V7Operation::Uqsub16(uq) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from uq
                );
                let rd = rd.unwrap_or(rn.clone());

                pseudo!([
                    rn:u32;
                    rm:u32;
                    let field1:u32 = Resize(rn<15:0>,u32);
                    let field2:u32 = Resize(rm<15:0>,u32);
                    let diff1:u16 = resize(field1,u16) ssub resize(field2,u16);
                    field1 = Resize(rn<31:16>,u32);
                    field2 = Resize(rm<31:16>,u32);
                    let diff2:u16 = resize(field1,u16) ssub resize(field2,u16);
                    let diff1_result = resize(diff1, u32);
                    let diff2_result = resize(diff2, u32);
                    diff2_result = diff2_result << 16.local_into();
                    rd = diff1_result | diff2_result;
                ])
            }
            V7Operation::Uqsub8(uq) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from uq
                );
                let rd = rd.unwrap_or(rn.clone());

                pseudo!([
                    rn:u32;
                    rm:u32;
                    let field1 = rn<7:0>;
                    let field2 = rm<7:0>;
                    let diff1:u8 = resize(field1,u8) ssub resize(field2,u8);
                    let diff1_result = resize(diff1, u32);

                    field1 = rn<15:8>;
                    field2 = rm<15:8>;
                    let diff2:u8 = resize(field1,u8) ssub resize(field2,u8);
                    let diff2_result = resize(diff2, u32);

                    field1 = rn<23:16>;
                    field2 = rm<23:16>;
                    let diff3:u8 = resize(field1,u8) ssub resize(field2,u8);
                    let diff3_result = resize(diff3, u32);

                    field1 = rn<31:24>;
                    field2 = rm<31:24>;
                    let diff4:u8 = resize(field1,u8) ssub resize(field2,u8);
                    let diff4_result = resize(diff4, u32);


                    diff2_result = diff2_result << 8.local_into();
                    diff3_result = diff3_result << 16.local_into();
                    diff4_result = diff4_result << 24.local_into();
                    let diff = diff1_result | diff2_result;
                    diff |= diff3_result;
                    diff |= diff4_result;
                    rd = diff;
                ])
            }
            V7Operation::Usad8(uq) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into()
                    ) from uq
                );
                let rd = rd.unwrap_or(rn.clone());

                pseudo!([
                    rn:u32;
                    rm:u32;
                    let diff1 = rn<7:0> - rm <7:0>;
                    let diff2 = rn<15:8> - rm <15:8>;
                    let diff3 = rn<23:16> - rm <23:16>;
                    let diff4 = rn<31:24> - rm <31:24>;
                    let result = diff1 + diff2;
                    result += diff3;
                    result += diff4;
                    rd = result;
                ])
            }
            V7Operation::Usada8(uq) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        rm.local_into(),
                        ra.local_into()
                    ) from uq
                );

                pseudo!([
                    rn:u32;
                    rm:u32;
                    let diff1 = rn<7:0> - rm <7:0>;
                    let diff2 = rn<15:8> - rm <15:8>;
                    let diff3 = rn<23:16> - rm <23:16>;
                    let diff4 = rn<31:24> - rm <31:24>;
                    let result = diff1 + diff2;
                    result += diff3;
                    result += diff4;
                    rd = result + ra;
                ])
            }
            V7Operation::Uqsad8(_) => todo!("This does not exist"),
            V7Operation::Usat(usat) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        shift,
                        imm.local_into()
                    ) from usat
                );
                let mut ret = vec![];
                local!(operand);
                shift!(ret.shift rn -> operand);
                pseudo!(ret.extend[
                    operand:u32;
                    imm:u32;
                    Ite(operand >= imm,
                        {
                            rd = imm;
                            Flag("Q") = 1.local_into();
                        },
                        {
                            rd = operand;
                        }
                    );
                ]);
                ret
            }
            V7Operation::Usat16(usat) => {
                consume!(
                    (
                        rd.local_into(),
                        rn.local_into(),
                        imm.local_into()
                    ) from usat
                );

                pseudo!([
                    rn:u32;
                    imm:u32;

                    let lower = Resize(rn<15:0>,u32);
                    Ite(lower >= imm,
                        {
                            lower = imm;
                            Flag("Q") = 1.local_into();
                        },{}
                    );
                    let upper = Resize(rn<15:0>,u32);
                    Ite(upper >= imm,
                        {
                            upper = imm;
                            Flag("Q") = 1.local_into();
                        },{}
                    );
                    let result = upper << 16.local_into();
                    rd = result | lower;

                ])
            }
            V7Operation::Usax(usax) => {
                let (rn, rd, rm) = (usax.rn.local_into(), usax.rd.local_into(), usax.rm.local_into());
                let rd = rd.unwrap_or(rn.clone());
                pseudo!([
                    rn:u32;
                    rm:u32;
                    let sum = rn<15:0> + rm<31:16>;
                    let diff = rn<31:16> - rm<15:0>;
                    rd = sum<15:0>;
                    diff = diff<15:0> << 16.local_into();
                    rd = rd | diff;
                    // TODO! Look in to the GE register setting
                    Abort("Incomplete instruction USAX");
                ])
            }
            V7Operation::Usub16(usub) => {
                let (rn, rd, rm) = (usub.rn.local_into(), usub.rd.local_into(), usub.rm.local_into());
                let rd = rd.unwrap_or(rn.clone());
                pseudo!([
                    rn:u32;
                    rm:u32;
                    let diff1 = rn<15:0> - rm<15:0>;
                    let diff2 = rn<31:16> - rm<31:16>;
                    rd = diff1<15:0>;
                    diff2 = diff2<15:0> << 16.local_into();
                    rd = rd | diff2;
                    // TODO! Look in to the GE register setting
                    Abort("Incomplete instruction USUB16");
                ])
            }
            V7Operation::Usub8(_) => {
                todo!("SIMD needs more work");
            }
            V7Operation::Uxtab(uxtab) => {
                let (rn, rd, rm, rotation) = (uxtab.rn.local_into(), uxtab.rd.local_into(), uxtab.rm.local_into(), uxtab.rotation.unwrap_or(0));
                let rd = rd.unwrap_or(rn.clone());
                pseudo!([
                    rm:u32;
                    let rotated = Ror(rm,rotation.local_into());
                    rd = rn + ZeroExtend(rotated<7:0>,32);
                ])
            }
            V7Operation::Uxtab16(uxtab) => {
                let (rn, rd, rm, rotation) = (uxtab.rn.local_into(), uxtab.rd.local_into(), uxtab.rm.local_into(), uxtab.rotation.unwrap_or(0));
                let rd = rd.unwrap_or(rn.clone());
                pseudo!([
                    rm:u32;
                    rn:u32;
                    let rotated:u32 = Ror(rm,rotation.local_into());
                    rd = Resize(rn<15:0>,u32) + ZeroExtend(rotated<7:0>,32);
                    let intermediate = Resize(rn<31:16>,u32) + ZeroExtend(rotated<23:16>,32);
                    intermediate = Resize(intermediate<15:0>,u32) << 16.local_into();
                    rd = Resize(rd<15:0>,u32) | intermediate;
                ])
            }
            V7Operation::Uxtah(uxtah) => {
                let (rn, rd, rm, rotation) = (uxtah.rn.local_into(), uxtah.rd.local_into(), uxtah.rm.local_into(), uxtah.rotation.unwrap_or(0));
                let rd = rd.unwrap_or(rn.clone());
                pseudo!([
                    rm:u32;
                    let rotated:u32 = Ror(rm,rotation.local_into());
                    rd = rn + ZeroExtend(rotated<15:0>,32);
                ])
            }
            V7Operation::Uxtb(uxtb) => {
                let (rd, rm, rotation) = (uxtb.rd.local_into(), uxtb.rm.local_into(), uxtb.rotation.unwrap_or(0));
                pseudo!([
                    rm:u32;
                    let rotated:u32 = Ror(rm,rotation.local_into());
                    rd = ZeroExtend(rotated<7:0>,32);
                ])
            }
            V7Operation::Uxtb16(uxtb) => uxtb.decode(in_it_block),
            V7Operation::Uxth(uxth) => uxth.decode(in_it_block),
            //Here we have to assume instant return.
            V7Operation::Wfe(_) => {
                warn!("WFE Encountered, this is not trivially modellable. Treating it as a NOP.");
                vec![]
            }
            //Here we have to assume instant return.
            V7Operation::Wfi(_) => {
                warn!("WFI Encountered, this is not trivially modellable. Treating it as a NOP.");
                vec![]
            }
            //Here we have to assume instant return.
            V7Operation::Yield(_) => {
                warn!("YIELD Encountered, this is not modellable by default. Treating it as a NOP.");
                vec![]
            }
            // I think that we should simply write Any here. i.e. they are noops.
            V7Operation::Svc(_) => vec![Operation::Abort {
                error: "Unmodelable Svc operation used.".to_string(),
            }],
            V7Operation::Stc(_) => vec![Operation::Abort {
                error: "Unmodelable Stc operation used.".to_string(),
            }],
            V7Operation::Mcr(_) => vec![Operation::Abort {
                error: "Unmodelable Mcr operation used.".to_string(),
            }],
            V7Operation::Mrc(_) => vec![Operation::Abort {
                error: "Unmodelable Mrc operation used.".to_string(),
            }],
            V7Operation::Mrrc(_) => vec![Operation::Abort {
                error: "Unmodelable Mrrc operation used.".to_string(),
            }],
            V7Operation::Mcrr(_) => vec![Operation::Abort {
                error: "Unmodelable Mcrr operation used.".to_string(),
            }],
            V7Operation::Cdp(_) => vec![Operation::Abort {
                error: "Unmodelable Cdp operation used.".to_string(),
            }],
            V7Operation::LdcLiteral(_) => vec![Operation::Abort {
                error: "Unmodelable LdcLiteral operation used.".to_string(),
            }],
            V7Operation::LdcImmediate(_) => vec![Operation::Abort {
                error: "Unmodelable LdcImmediate operation used.".to_string(),
            }],
            V7Operation::VselF32(vsel_f32) => vsel_f32.decode(in_it_block),
            V7Operation::VselF64(vsel_f64) => vsel_f64.decode(in_it_block),
            V7Operation::VmlF32(vml_f32) => vml_f32.decode(in_it_block),
            V7Operation::VmlF64(vml_f64) => vml_f64.decode(in_it_block),
            V7Operation::VfmxF32(vfmx32) => vfmx32.decode(in_it_block),
            V7Operation::VfmxF64(vfmx64) => vfmx64.decode(in_it_block),
            V7Operation::VnmlF32(vnml_f32) => vnml_f32.decode(in_it_block),
            V7Operation::VnmlF64(vnml_f64) => vnml_f64.decode(in_it_block),
            V7Operation::VnmulF32(vnmul_f32) => vnmul_f32.decode(in_it_block),
            V7Operation::VnmulF64(vnmul_f64) => vnmul_f64.decode(in_it_block),
            V7Operation::VmulF32(vmul_f32) => vmul_f32.decode(in_it_block),
            V7Operation::VmulF64(vmul_f64) => vmul_f64.decode(in_it_block),
            V7Operation::VaddF32(vadd_f32) => vadd_f32.decode(in_it_block),
            V7Operation::VaddF64(vadd_f64) => vadd_f64.decode(in_it_block),
            V7Operation::VsubF32(vsub_f32) => vsub_f32.decode(in_it_block),
            V7Operation::VsubF64(vsub_f64) => vsub_f64.decode(in_it_block),
            V7Operation::VdivF32(vdiv_f32) => vdiv_f32.decode(in_it_block),
            V7Operation::VdivF64(vdiv_f64) => vdiv_f64.decode(in_it_block),
            V7Operation::VmaxF32(vmax_f32) => vmax_f32.decode(in_it_block),
            V7Operation::VmaxF64(vmax_f64) => vmax_f64.decode(in_it_block),
            V7Operation::VminF32(vmin_f32) => vmin_f32.decode(in_it_block),
            V7Operation::VminF64(vmin_f64) => vmin_f64.decode(in_it_block),
            V7Operation::VmovImmediateF32(vmov_immediate_f32) => vmov_immediate_f32.decode(in_it_block),
            V7Operation::VmovImmediateF64(vmov_immediate_f64) => vmov_immediate_f64.decode(in_it_block),
            V7Operation::VmovRegisterF32(vmov_register_f32) => vmov_register_f32.decode(in_it_block),
            V7Operation::VmovRegisterF64(vmov_register_f64) => vmov_register_f64.decode(in_it_block),
            V7Operation::VabsF32(vabs_f32) => vabs_f32.decode(in_it_block),
            V7Operation::VabsF64(vabs_f64) => vabs_f64.decode(in_it_block),
            V7Operation::VnegF32(vneg_f32) => vneg_f32.decode(in_it_block),
            V7Operation::VnegF64(vneg_f64) => vneg_f64.decode(in_it_block),
            V7Operation::VsqrtF32(vsqrt_f32) => vsqrt_f32.decode(in_it_block),
            V7Operation::VsqrtF64(vsqrt_f64) => vsqrt_f64.decode(in_it_block),
            V7Operation::VcvtF32(vcvt_f32) => vcvt_f32.decode(in_it_block),
            V7Operation::VcvtF64(vcvt_f64) => vcvt_f64.decode(in_it_block),
            V7Operation::VcmpF32(vcmp_f32) => vcmp_f32.decode(in_it_block),
            V7Operation::VcmpF64(vcmp_f64) => vcmp_f64.decode(in_it_block),
            V7Operation::VcmpZeroF32(vcmp_zero_f32) => vcmp_zero_f32.decode(in_it_block),
            V7Operation::VcmpZeroF64(vcmp_zero_f64) => vcmp_zero_f64.decode(in_it_block),
            V7Operation::VrintF32(vrint_f32) => vrint_f32.decode(in_it_block),
            V7Operation::VrintF64(vrint_f64) => vrint_f64.decode(in_it_block),
            V7Operation::VcvtF64F32(vcvt_f64_f32) => vcvt_f64_f32.decode(in_it_block),
            V7Operation::VcvtF32F64(vcvt_f32_f64) => vcvt_f32_f64.decode(in_it_block),
            V7Operation::Vcvt(vcvt) => vcvt.decode(in_it_block),
            V7Operation::VrintCustomRoundingF32(vrint_custom_rounding_f32) => vrint_custom_rounding_f32.decode(in_it_block),
            V7Operation::VrintCustomRoundingF64(vrint_custom_rounding_f64) => vrint_custom_rounding_f64.decode(in_it_block),
            V7Operation::VcvtCustomRoundingIntF32(vcvt_custom_rounding_int_f32) => vcvt_custom_rounding_int_f32.decode(in_it_block),
            V7Operation::VcvtCustomRoundingIntF64(vcvt_custom_rounding_int_f64) => vcvt_custom_rounding_int_f64.decode(in_it_block),
            V7Operation::VStmF32(vstm_f32) => vstm_f32.decode(in_it_block),
            V7Operation::VStmF64(vstm_f64) => vstm_f64.decode(in_it_block),
            V7Operation::VStrF32(vstr_f32) => vstr_f32.decode(in_it_block),
            V7Operation::VStrF64(vstr_f64) => vstr_f64.decode(in_it_block),
            V7Operation::VPushF32(vpush_f32) => vpush_f32.decode(in_it_block),
            V7Operation::VPushF64(vpush_f64) => vpush_f64.decode(in_it_block),
            V7Operation::VLdrF32(vldr_f32) => vldr_f32.decode(in_it_block),
            V7Operation::VLdrF64(vldr_f64) => vldr_f64.decode(in_it_block),
            V7Operation::VPopF32(vpop_f32) => vpop_f32.decode(in_it_block),
            V7Operation::VPopF64(vpop_f64) => vpop_f64.decode(in_it_block),
            V7Operation::VLdmF32(vldm_f32) => vldm_f32.decode(in_it_block),
            V7Operation::VLdmF64(vldm_f64) => vldm_f64.decode(in_it_block),
            V7Operation::VmoveF32(vmove_f32) => vmove_f32.decode(in_it_block),
            V7Operation::VmoveF64(vmove_f64) => vmove_f64.decode(in_it_block),
            V7Operation::VmoveHalfWord(_vmove_half_word) => unimplemented!("This does not exist."),
            V7Operation::VmoveDoubleF32(vmove_double_f32) => vmove_double_f32.decode(in_it_block),
            V7Operation::Vmsr(vmsr) => vmsr.decode(in_it_block),
            V7Operation::Vmrs(vmrs) => vmrs.decode(in_it_block),
        }
    }
}

pub(super) mod sealed {
    pub trait Into<T> {
        fn local_into(self) -> T;
    }
    pub trait ToString {
        fn to_string(self) -> String;
    }
}

use sealed::Into;

use self::sealed::ToString;

impl sealed::Into<Operand> for Register {
    fn local_into(self) -> Operand {
        Operand::Register(self.to_string())
    }
}

impl sealed::Into<Condition> for ARMCondition {
    fn local_into(self) -> Condition {
        match self {
            Self::Eq => Condition::EQ,
            Self::Ne => Condition::NE,
            Self::Mi => Condition::MI,
            Self::Pl => Condition::PL,
            Self::Vs => Condition::VS,
            Self::Vc => Condition::VC,
            Self::Hi => Condition::HI,
            Self::Ge => Condition::GE,
            Self::Lt => Condition::LT,
            Self::Gt => Condition::GT,
            Self::Ls => Condition::LS,
            Self::Le => Condition::LE,
            Self::Cs => Condition::CS,
            Self::Cc => Condition::CC,
            Self::None => Condition::None,
        }
    }
}

pub enum SpecialRegister {
    APSR,
    IAPSR,
    EAPSR,
    XPSR,
    IPSR,
    EPSR,
    IEPSR,
    MSP,
    PSP,
    PRIMASK,
    CONTROL,
    FAULTMASK,
    BASEPRI,
}

impl Into<Operand> for SpecialRegister {
    fn local_into(self) -> Operand {
        Operand::Register(match self {
            SpecialRegister::APSR => "APSR".to_owned(),
            SpecialRegister::IAPSR => "IAPSR".to_owned(),
            SpecialRegister::EAPSR => "EAPSR".to_owned(),
            SpecialRegister::XPSR => "XPSR".to_owned(),
            SpecialRegister::IPSR => "IPSR".to_owned(),
            SpecialRegister::EPSR => "EPSR".to_owned(),
            SpecialRegister::IEPSR => "IEPSR".to_owned(),
            SpecialRegister::MSP => "MSP".to_owned(),
            SpecialRegister::PSP => "PSP".to_owned(),
            SpecialRegister::PRIMASK => "PRIMASK".to_owned(),
            SpecialRegister::CONTROL => "CONTROL".to_owned(),
            SpecialRegister::FAULTMASK => "FAULTMASK".to_owned(),
            SpecialRegister::BASEPRI => "BASEPRI".to_owned(),
        })
    }
}

impl sealed::ToString for Register {
    fn to_string(self) -> String {
        match self {
            Register::R0 => "R0".to_owned(),
            Register::R1 => "R1".to_owned(),
            Register::R2 => "R2".to_owned(),
            Register::R3 => "R3".to_owned(),
            Register::R4 => "R4".to_owned(),
            Register::R5 => "R5".to_owned(),
            Register::R6 => "R6".to_owned(),
            Register::R7 => "R7".to_owned(),
            Register::R8 => "R8".to_owned(),
            Register::R9 => "R9".to_owned(),
            Register::R10 => "R10".to_owned(),
            Register::R11 => "R11".to_owned(),
            Register::R12 => "R12".to_owned(),
            Register::SP => "SP&".to_owned(),
            Register::LR => "LR".to_owned(),
            Register::PC => "PC+".to_owned(),
        }
    }
}
impl<T, T2> sealed::Into<Option<T>> for Option<T2>
where
    T2: sealed::Into<T>,
{
    fn local_into(self) -> Option<T> {
        self.map(|val| val.local_into())
    }
}
impl sealed::Into<GAShift> for Shift {
    fn local_into(self) -> GAShift {
        match self {
            Self::Lsl => GAShift::Lsl,
            Self::Lsr => GAShift::Lsr,
            Self::Asr => GAShift::Asr,
            Self::Rrx => GAShift::Rrx,
            Self::Ror => GAShift::Ror,
        }
    }
}

impl Into<Operand> for u32 {
    fn local_into(self) -> Operand {
        Operand::Immediate(DataWord::Word32(self))
    }
}
fn mask_dyn(start: u32, end: u32) -> u32 {
    ((1 << (end - start + 1)) - 1) << start
}

impl<T1, T2, T11: sealed::Into<T1>, T22: sealed::Into<T2>> sealed::Into<(T1, T2)> for (T11, T22) {
    fn local_into(self) -> (T1, T2) {
        (self.0.local_into(), self.1.local_into())
    }
}

impl<T1, T2, T3, T11: sealed::Into<T1>, T22: sealed::Into<T2>, T33: sealed::Into<T3>> sealed::Into<(T1, T2, T3)> for (T11, T22, T33) {
    fn local_into(self) -> (T1, T2, T3) {
        (self.0.local_into(), self.1.local_into(), self.2.local_into())
    }
}

impl<T1, T2, T3, T4, T11: sealed::Into<T1>, T22: sealed::Into<T2>, T33: sealed::Into<T3>, T44: sealed::Into<T4>> sealed::Into<(T1, T2, T3, T4)> for (T11, T22, T33, T44) {
    fn local_into(self) -> (T1, T2, T3, T4) {
        (self.0.local_into(), self.1.local_into(), self.2.local_into(), self.3.local_into())
    }
}
