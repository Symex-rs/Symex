use disarmv7::prelude::{Condition, Operation as V7Operation, Register};

use crate::executor::{instruction::CycleCount, state::GAState};
// use general_assembly::operation::Operation;

impl super::ArmV7EM {
    pub fn memory_access(instr: &V7Operation) -> bool {
        use V7Operation::*;
        match instr {
            AdcImmediate(_) | AdcRegister(_) | AddImmediate(_) | AddRegister(_) | AddSPImmediate(_) | AddSPRegister(_) | Adr(_) | AndImmediate(_) | AndRegister(_)
            | AsrImmediate(_) | AsrRegister(_) | B(_) | Bfc(_) | Bfi(_) | BicImmediate(_) | BicRegister(_) | Bkpt(_) | Bl(_) | Blx(_) | Bx(_) | Cbz(_) | Clrex(_) | Clz(_)
            | CmnImmediate(_) | CmnRegister(_) | CmpImmediate(_) | CmpRegister(_) | Cps(_) | Dbg(_) | Dmb(_) | Dsb(_) | EorImmediate(_) | EorRegister(_) | Isb(_) | It(_) => false,
            Ldm(_) | Ldmdb(_) | LdrImmediate(_) | LdrLiteral(_) | LdrRegister(_) | LdrbImmediate(_) | LdrbLiteral(_) | LdrbRegister(_) | Ldrbt(_) | LdrdImmediate(_)
            | LdrdLiteral(_) | Ldrex(_) | Ldrexb(_) | Ldrexh(_) | LdrhImmediate(_) | LdrhLiteral(_) | LdrhRegister(_) | Ldrht(_) | LdrsbImmediate(_) | LdrsbLiteral(_)
            | LdrsbRegister(_) | Ldrsbt(_) | LdrshImmediate(_) | LdrshLiteral(_) | LdrshRegister(_) | Ldrsht(_) | Ldrt(_) => true,
            /* LdcImmediate(_) | LdcLiteral(_) | */
            LslImmediate(_) | LslRegister(_) | LsrImmediate(_) | LsrRegister(_) => false,
            Mcrr(_) | Mla(_) | Mls(_) | MovImmediate(_) | MovRegister(_) | Movt(_) | Mrrc(_) | Mrs(_) | Msr(_) | Mul(_) | MvnImmediate(_) | MvnRegister(_) | Nop(_)
            | OrnImmediate(_) | OrnRegister(_) | OrrImmediate(_) | OrrRegister(_) | Pkh(_) => false,
            PldImmediate(_) | PldLiteral(_) | PldRegister(_) | PliImmediate(_) | PliRegister(_) => true,
            Pop(_) => true,
            Push(_) => true,
            Qadd(_) | Qadd16(_) | Qadd8(_) | Qasx(_) | Qdadd(_) | Qdsub(_) | Qsax(_) | Qsub(_) | Qsub16(_) | Qsub8(_) | Rbit(_) | Rev(_) | Rev16(_) | Revsh(_)
            | RorImmediate(_) | RorRegister(_) | Rrx(_) | RsbImmediate(_) | RsbRegister(_) | Sadd16(_) | Sadd8(_) | Sasx(_) | SbcImmediate(_) | SbcRegister(_) | Sbfx(_)
            | Sdiv(_) | Sel(_) | Sev(_) | Shadd16(_) | Shadd8(_) | Shasx(_) | Shsax(_) | Shsub16(_) | Shsub8(_) | Smla(_) | Smlad(_) | Smlal(_) | SmlalSelective(_) | Smlald(_)
            | Smlaw(_) | Smlsd(_) | Smlsld(_) | Smmla(_) | Smmls(_) | Smmul(_) | Smuad(_) | Smul(_) | Smull(_) | Smulw(_) | Smusd(_) | Ssat(_) | Ssat16(_) | Ssax(_)
            | Ssub16(_) | Ssub8(_) => false,
            Stm(_) | Stmdb(_) | StrImmediate(_) | StrRegister(_) | StrbImmediate(_) | StrbRegister(_) | Strbt(_) | StrdImmediate(_) | Strex(_) | Strexb(_) | Strexh(_)
            | StrhImmediate(_) | StrhRegister(_) | Strht(_) | Strt(_) => true,
            Stc(_)
            | SubImmediate(_)
            | SubRegister(_)
            | SubSpMinusImmediate(_)
            | SubSpMinusRegister(_)
            | Sxtab(_)
            | Sxtab16(_)
            | Sxtah(_)
            | Sxtb(_)
            | Sxtb16(_)
            | Sxth(_)
            | Tb(_)
            | TeqImmediate(_)
            | TeqRegister(_)
            | TstImmediate(_)
            | TstRegister(_)
            | Uadd16(_)
            | Uadd8(_)
            | Uasx(_)
            | Ubfx(_)
            | Udf(_)
            | Udiv(_)
            | Uhadd16(_)
            | Uhadd8(_)
            | Uhasx(_)
            | Uhsax(_)
            | Uhsub16(_)
            | Uhsub8(_)
            | Umaal(_)
            | Umlal(_)
            | Umull(_)
            | Uqadd16(_)
            | Uqadd8(_)
            | Uqasx(_)
            | Uqsax(_)
            | Uqsub16(_)
            | Uqsub8(_)
            | Uqsad8(_)
            | Usada8(_)
            | Usad8(_)
            | Usat(_)
            | Usat16(_)
            | Usax(_)
            | Usub16(_)
            | Usub8(_)
            | Uxtab(_)
            | Uxtab16(_)
            | Uxtah(_)
            | Uxtb(_)
            | Uxtb16(_)
            | Uxth(_)
            | Wfe(_)
            | Wfi(_)
            | Yield(_)
            | Svc(_)
            | Mcr(_)
            | Mrc(_)
            | Cdp(_)
            | LdcImmediate(_)
            | LdcLiteral(_) => false,
            VselF32(_vsel_f32) => todo!(),
            VselF64(_vsel_f64) => todo!(),
            VmlF32(_vml_f32) => todo!(),
            VmlF64(_vml_f64) => todo!(),
            VnmlF32(_vnml_f32) => todo!(),
            VnmlF64(_vnml_f64) => todo!(),
            VnmulF32(_vnmul_f32) => todo!(),
            VnmulF64(_vnmul_f64) => todo!(),
            VmulF32(_vmul_f32) => todo!(),
            VmulF64(_vmul_f64) => todo!(),
            VaddF32(_vadd_f32) => todo!(),
            VaddF64(_vadd_f64) => todo!(),
            VsubF32(_vsub_f32) => todo!(),
            VsubF64(_vsub_f64) => todo!(),
            VdivF32(_vdiv_f32) => todo!(),
            VdivF64(_vdiv_f64) => todo!(),
            VmaxF32(_vmax_f32) => todo!(),
            VmaxF64(_vmax_f64) => todo!(),
            VminF32(_vmin_f32) => todo!(),
            VminF64(_vmin_f64) => todo!(),
            VmovImmediateF32(_vmov_immediate_f32) => todo!(),
            VmovImmediateF64(_vmov_immediate_f64) => todo!(),
            VmovRegisterF32(_vmov_register_f32) => todo!(),
            VmovRegisterF64(_vmov_register_f64) => todo!(),
            VabsF32(_vabs_f32) => todo!(),
            VabsF64(_vabs_f64) => todo!(),
            VnegF32(_vneg_f32) => todo!(),
            VnegF64(_vneg_f64) => todo!(),
            VsqrtF32(_vsqrt_f32) => todo!(),
            VsqrtF64(_vsqrt_f64) => todo!(),
            VcvtF32(_vcvt_f32) => todo!(),
            VcvtF64(_vcvt_f64) => todo!(),
            VcmpF32(_vcmp_f32) => todo!(),
            VcmpF64(_vcmp_f64) => todo!(),
            VcmpZeroF32(_vcmp_zero_f32) => todo!(),
            VcmpZeroF64(_vcmp_zero_f64) => todo!(),
            VrintF32(_vrint_f32) => todo!(),
            VrintF64(_vrint_f64) => todo!(),
            VcvtF64F32(_vcvt_f64_f32) => todo!(),
            VcvtF32F64(_vcvt_f32_f64) => todo!(),
            Vcvt(_vcvt) => todo!(),
            VrintCustomRoundingF32(_vrint_custom_rounding_f32) => todo!(),
            VrintCustomRoundingF64(_vrint_custom_rounding_f64) => todo!(),
            VcvtCustomRoundingIntF32(_vcvt_custom_rounding_int_f32) => todo!(),
            VcvtCustomRoundingIntF64(_vcvt_custom_rounding_int_f64) => todo!(),
            VStmF32(_vstm_f32) => todo!(),
            VStmF64(_vstm_f64) => todo!(),
            VStrF32(_vstr_f32) => todo!(),
            VStrF64(_vstr_f64) => todo!(),
            VPushF32(_vpush_f32) => todo!(),
            VPushF64(_vpush_f64) => todo!(),
            VLdrF32(_vldr_f32) => todo!(),
            VLdrF64(_vldr_f64) => todo!(),
            VPopF32(_vpop_f32) => todo!(),
            VPopF64(_vpop_f64) => todo!(),
            VLdmF32(_vldm_f32) => todo!(),
            VLdmF64(_vldm_f64) => todo!(),
            VmoveF32(_vmove_f32) => todo!(),
            VmoveHalfWord(_vmove_half_word) => todo!(),
            Vmsr(_vmsr) => todo!(),
            Vmrs(_vmrs) => todo!(),
            VmoveDoubleF32(_vmove_double_f32) => todo!(),
            VmoveF64(_vmove_f64) => todo!(),
        }
    }

    pub fn cycle_count_m4_core<C: crate::Composition>(instr: &V7Operation) -> CycleCount<C> {
        let p = 3;
        let pipeline = |state: &mut GAState<C>| match state.get_last_instruction() {
            Some(instr) => match instr.memory_access {
                true => 1,
                false => 2,
            },
            _ => 2,
        };
        let if_pc = |reg: Register, value: usize| {
            if reg == Register::PC {
                return CycleCount::Value(value + p);
            }
            CycleCount::Value(value)
        };
        match instr {
            V7Operation::AdcImmediate(_) | V7Operation::AdcRegister(_) => CycleCount::Value(1),
            V7Operation::AddImmediate(add) => if_pc(add.rd.unwrap_or(add.rn), 1),
            V7Operation::AddRegister(add) => if_pc(add.rd.unwrap_or(add.rn), 1),
            V7Operation::AddSPImmediate(add) => if_pc(add.rd.unwrap_or(Register::SP), 1),
            V7Operation::AddSPRegister(add) => if_pc(add.rd.unwrap_or(Register::SP), 1),
            V7Operation::Adr(_) => CycleCount::Value(1),
            V7Operation::AndImmediate(_) | V7Operation::AndRegister(_) => CycleCount::Value(1),
            V7Operation::AsrImmediate(_) | V7Operation::AsrRegister(_) => CycleCount::Value(1),
            V7Operation::B(b) => {
                if b.condition != Condition::None {
                    let counter = |state: &mut GAState<C>| {
                        // match (state.get_next_instruction(), state.get_has_jumped()) {
                        //     (
                        //         Ok(crate::general_assembly::state::HookOrInstruction::Instruction(
                        //             instr,
                        //         )),
                        //         true,
                        //     ) => {
                        //         let ops = instr.operations.len();
                        //         match (ops, instr.operations.get(0)) {
                        //             (1, Some(Operation::Nop)) => {
                        //                 return 2;
                        //             }
                        //             _ => {}
                        //         }
                        //     }
                        //
                        //     _ => {}
                        // }
                        //
                        match state.get_has_jumped() {
                            true => 1 + 3,
                            false => 1,
                        }
                    };
                    CycleCount::Function(counter)
                } else {
                    // CycleCount2::Value(1 + 3)

                    // This is a gross over estimation, it should be more like 1+1
                    CycleCount::Value(1 + 3)
                }
            }
            V7Operation::Bfc(_) => CycleCount::Value(1),
            V7Operation::Bfi(_) => CycleCount::Value(1),
            V7Operation::BicImmediate(_) | V7Operation::BicRegister(_) => CycleCount::Value(1),
            V7Operation::Bkpt(_) => CycleCount::Value(0),
            V7Operation::Bl(_) => CycleCount::Value(1 + 3),
            V7Operation::Blx(_) => CycleCount::Value(1 + 3),
            V7Operation::Bx(_) => CycleCount::Value(1 + 3),
            V7Operation::Cbz(_) => {
                let counter = |state: &mut GAState<C>| match state.get_has_jumped() {
                    true => 1 + 3,
                    false => 1,
                };
                CycleCount::Function(counter)
            }
            V7Operation::Clrex(_) => CycleCount::Value(1),
            V7Operation::Clz(_) => CycleCount::Value(1),
            V7Operation::CmnImmediate(_) | V7Operation::CmnRegister(_) => CycleCount::Value(1),
            V7Operation::CmpImmediate(_) | V7Operation::CmpRegister(_) => CycleCount::Value(1),
            V7Operation::Cps(_) => CycleCount::Value(2),
            V7Operation::Dbg(_) => CycleCount::Value(1),
            V7Operation::Dmb(_) => CycleCount::Value(1), /* todo!("This requires a model of */
            // barriers")
            V7Operation::Dsb(_) => todo!("This requires a model of barriers"),
            V7Operation::EorImmediate(_) | V7Operation::EorRegister(_) => CycleCount::Value(1),
            V7Operation::Isb(_) => todo!("This requires a model of barriers"),
            // TODO! Add detection for whether this is folded or not, if it is the value here is 0
            V7Operation::It(_) => {
                let counter = |state: &mut GAState<C>| match state.get_last_instruction() {
                    Some(instr) => match instr.instruction_size {
                        16 => 0,
                        _ => 1,
                    },
                    None => 1,
                };

                CycleCount::Function(counter)
            }
            V7Operation::Ldm(ldm) => {
                let pc = ldm.registers.registers.contains(&Register::PC);
                let n = ldm.registers.registers.len();
                let mut count = 1 + n;
                if pc {
                    // TODO! Model pipeline better
                    count += 3;
                }
                CycleCount::Value(count)
            }
            V7Operation::Ldmdb(ldm) => {
                let pc = ldm.registers.registers.contains(&Register::PC);
                let n = ldm.registers.registers.len();
                let mut count = 1 + n;
                if pc {
                    // TODO! Model pipeline better
                    count += 3;
                }
                CycleCount::Value(count)
            }
            // TODO! Add in pre load hints
            V7Operation::LdrImmediate(el) => match (el.rt, el.rn) {
                (_, Register::PC) => CycleCount::Value(2),
                (Register::PC, _) => CycleCount::Value(2 + 3),
                _ => CycleCount::Function(pipeline),
            },
            V7Operation::LdrLiteral(el) => match el.rt {
                Register::PC => CycleCount::Value(2 + 3),
                _ => CycleCount::Function(pipeline),
            },
            V7Operation::LdrRegister(el) => match (el.rt, el.rn) {
                (Register::PC, Register::PC) => CycleCount::Value(2),
                (Register::PC, _) => CycleCount::Value(2 + 3),
                _ => CycleCount::Function(pipeline),
            },
            V7Operation::LdrbImmediate(_) | V7Operation::LdrbLiteral(_) | V7Operation::LdrbRegister(_) => CycleCount::Value(2),
            V7Operation::Ldrbt(_) => CycleCount::Value(2),
            V7Operation::LdrdImmediate(_ldrd) => CycleCount::Value(1 + 2),
            V7Operation::LdrdLiteral(_) => CycleCount::Value(1 + 2),
            // TODO! This requires a model of semaphores
            V7Operation::Ldrex(_) | V7Operation::Ldrexb(_) | V7Operation::Ldrexh(_) => CycleCount::Value(2),
            // TODO! Add in model of contiguous loads to allow next load to be single cycle
            V7Operation::LdrhImmediate(_)
            | V7Operation::LdrhLiteral(_)
            | V7Operation::LdrhRegister(_)
            | V7Operation::Ldrht(_)
            | V7Operation::LdrsbImmediate(_)
            | V7Operation::LdrsbLiteral(_)
            | V7Operation::LdrsbRegister(_)
            | V7Operation::Ldrsbt(_)
            | V7Operation::LdrshImmediate(_)
            | V7Operation::LdrshLiteral(_)
            | V7Operation::LdrshRegister(_)
            | V7Operation::Ldrsht(_)
            | V7Operation::Ldrt(_) => CycleCount::Function(pipeline),
            V7Operation::LslImmediate(_) | V7Operation::LslRegister(_) => CycleCount::Value(1),
            V7Operation::LsrImmediate(_) | V7Operation::LsrRegister(_) => CycleCount::Value(1),
            V7Operation::Mla(_) | V7Operation::Mls(_) => CycleCount::Value(2),
            V7Operation::MovImmediate(mov) => match mov.rd {
                Register::PC => CycleCount::Value(1 + p),
                _ => CycleCount::Value(1),
            },
            V7Operation::MovRegister(mov) => match mov.rd {
                Register::PC => CycleCount::Value(1 + 3),
                _ => CycleCount::Value(1),
            },
            V7Operation::Movt(_) => CycleCount::Value(1),
            V7Operation::Mrs(_) => CycleCount::Value(2),
            V7Operation::Msr(_) => CycleCount::Value(2),
            V7Operation::Mul(_) => CycleCount::Value(1),
            V7Operation::MvnImmediate(_) | V7Operation::MvnRegister(_) => CycleCount::Value(1),
            V7Operation::Nop(_) => CycleCount::Value(1),
            V7Operation::OrnImmediate(_) | V7Operation::OrnRegister(_) => CycleCount::Value(1),
            V7Operation::OrrImmediate(_) | V7Operation::OrrRegister(_) => CycleCount::Value(1),
            V7Operation::Pkh(_) => CycleCount::Value(1),
            V7Operation::PldImmediate(_) => todo!("Add in preload hints"),
            V7Operation::PldLiteral(_) => todo!("Add in preload hints"),
            V7Operation::PldRegister(_) => todo!("Add in preload hints"),
            V7Operation::PliImmediate(_) => todo!("Add in preload hints"),
            V7Operation::PliRegister(_) => todo!("Add in preload hints"),
            V7Operation::Pop(pop) => {
                // TODO! Validate this, it might be incorrect
                // The documentation gives us
                // POP {<reglist>, PC} => 1 + N + P
                // This seems to count N as the number or registers in <reglist>
                // if we assume this to be the case we can subtract one from P
                // as that is the same as subtracting one from N
                let ret = match pop.registers.registers.contains(&Register::PC) {
                    true => p - 1,
                    _ => 0,
                };
                CycleCount::Value(1 + pop.registers.registers.len() + ret)
            }
            V7Operation::Push(push) => CycleCount::Value(1 + push.registers.registers.len()),
            V7Operation::Qadd(_) => CycleCount::Value(1),
            V7Operation::Qadd16(_) => CycleCount::Value(1),
            V7Operation::Qadd8(_) => CycleCount::Value(1),
            V7Operation::Qasx(_) => CycleCount::Value(1),
            V7Operation::Qdadd(_) => CycleCount::Value(1),
            V7Operation::Qdsub(_) => CycleCount::Value(1),
            V7Operation::Qsax(_) => CycleCount::Value(1),
            V7Operation::Qsub(_) => CycleCount::Value(1),
            V7Operation::Qsub16(_) => CycleCount::Value(1),
            V7Operation::Qsub8(_) => CycleCount::Value(1),
            V7Operation::Rbit(_) => CycleCount::Value(1),
            V7Operation::Rev(_) => CycleCount::Value(1),
            V7Operation::Rev16(_) => CycleCount::Value(1),
            V7Operation::Revsh(_) => CycleCount::Value(1),
            V7Operation::RorImmediate(_) | V7Operation::RorRegister(_) => CycleCount::Value(1),
            V7Operation::Rrx(_) => CycleCount::Value(1),
            V7Operation::RsbImmediate(_) | V7Operation::RsbRegister(_) => CycleCount::Value(1),
            V7Operation::Sadd16(_) => CycleCount::Value(1),
            V7Operation::Sadd8(_) => CycleCount::Value(1),
            V7Operation::Sasx(_) => CycleCount::Value(1),
            V7Operation::SbcImmediate(_) | V7Operation::SbcRegister(_) => CycleCount::Value(1),
            V7Operation::Sbfx(_) => CycleCount::Value(1),
            // TODO! Add way to find whether or not this is 12 or 2
            V7Operation::Sdiv(_) => CycleCount::Value(12),
            V7Operation::Sel(_) => CycleCount::Value(1),
            V7Operation::Sev(_) => CycleCount::Value(1),
            V7Operation::Shadd16(_) => CycleCount::Value(1),
            V7Operation::Shadd8(_) => CycleCount::Value(1),
            V7Operation::Shasx(_) => CycleCount::Value(1),
            V7Operation::Shsax(_) => CycleCount::Value(1),
            V7Operation::Shsub16(_) => CycleCount::Value(1),
            V7Operation::Shsub8(_) => CycleCount::Value(1),
            V7Operation::Smla(_) => CycleCount::Value(1),
            V7Operation::Smlad(_) => CycleCount::Value(1),
            V7Operation::Smlal(_) => CycleCount::Value(1),
            V7Operation::SmlalSelective(_) => CycleCount::Value(1),
            V7Operation::Smlald(_) => CycleCount::Value(1),
            V7Operation::Smlaw(_) => CycleCount::Value(1),
            V7Operation::Smlsd(_) => CycleCount::Value(1),
            V7Operation::Smlsld(_) => CycleCount::Value(1),
            V7Operation::Smmla(_) => CycleCount::Value(1),
            V7Operation::Smmls(_) => CycleCount::Value(1),
            V7Operation::Smmul(_) => CycleCount::Value(1),
            V7Operation::Smuad(_) => CycleCount::Value(1),
            V7Operation::Smul(_) => CycleCount::Value(1),
            V7Operation::Smull(_) => CycleCount::Value(1),
            V7Operation::Smulw(_) => CycleCount::Value(1),
            V7Operation::Smusd(_) => CycleCount::Value(1),
            V7Operation::Ssat(_) | V7Operation::Ssat16(_) => CycleCount::Value(1),
            V7Operation::Ssax(_) => CycleCount::Value(1),
            V7Operation::Ssub16(_) => CycleCount::Value(1),
            V7Operation::Ssub8(_) => CycleCount::Value(1),
            V7Operation::Stm(stm) => CycleCount::Value(1 + stm.registers.registers.len()),
            V7Operation::Stmdb(stm) => CycleCount::Value(1 + stm.registers.registers.len()),
            V7Operation::StrImmediate(_) | V7Operation::StrRegister(_) => CycleCount::Function(pipeline),
            V7Operation::StrbImmediate(_) | V7Operation::StrbRegister(_) => CycleCount::Function(pipeline),
            V7Operation::Strbt(_) => CycleCount::Value(2),
            // N is two here
            V7Operation::StrdImmediate(_strd) => CycleCount::Value(1 + 2),
            V7Operation::Strex(_) => CycleCount::Value(2),
            V7Operation::Strexb(_) => CycleCount::Value(2),
            V7Operation::Strexh(_) => CycleCount::Value(2),
            V7Operation::StrhImmediate(_) | V7Operation::StrhRegister(_) | V7Operation::Strht(_) | V7Operation::Strt(_) => CycleCount::Function(pipeline),
            V7Operation::SubImmediate(_) | V7Operation::SubRegister(_) => CycleCount::Value(1),
            V7Operation::SubSpMinusImmediate(_) => CycleCount::Value(1),
            V7Operation::SubSpMinusRegister(_) => CycleCount::Value(1),

            V7Operation::Sxtab(_) => CycleCount::Value(1),

            V7Operation::Sxtab16(_) => CycleCount::Value(1),
            V7Operation::Sxtah(_) => CycleCount::Value(1),
            V7Operation::Sxtb(_) => CycleCount::Value(1),
            V7Operation::Sxtb16(_) => CycleCount::Value(1),
            V7Operation::Sxth(_) => CycleCount::Value(1),
            V7Operation::Tb(_) => CycleCount::Value(2 + p),
            // TODO!  The docs do not mention any cycle count for this
            // might be incorrect
            V7Operation::TeqImmediate(_) | V7Operation::TeqRegister(_) => CycleCount::Value(1),
            V7Operation::TstImmediate(_) | V7Operation::TstRegister(_) => CycleCount::Value(1),
            V7Operation::Uadd16(_) => CycleCount::Value(1),
            V7Operation::Uadd8(_) => CycleCount::Value(1),
            V7Operation::Uasx(_) => CycleCount::Value(1),
            V7Operation::Ubfx(_) => CycleCount::Value(1),
            V7Operation::Udf(_) => CycleCount::Value(1),
            // TODO! Add way to check if this is 12 or 2
            V7Operation::Udiv(_) => CycleCount::Value(12),
            V7Operation::Uhadd16(_) => CycleCount::Value(1),
            V7Operation::Uhadd8(_) => CycleCount::Value(1),
            V7Operation::Uhasx(_) => CycleCount::Value(1),
            V7Operation::Uhsax(_) => CycleCount::Value(1),
            V7Operation::Uhsub16(_) => CycleCount::Value(1),
            V7Operation::Uhsub8(_) => CycleCount::Value(1),
            V7Operation::Umaal(_) => CycleCount::Value(1),
            V7Operation::Umlal(_) => CycleCount::Value(1),
            V7Operation::Umull(_) => CycleCount::Value(1),
            V7Operation::Uqadd16(_) => CycleCount::Value(1),
            V7Operation::Uqadd8(_) => CycleCount::Value(1),
            V7Operation::Uqasx(_) => CycleCount::Value(1),
            V7Operation::Uqsax(_) => CycleCount::Value(1),
            V7Operation::Uqsub16(_) => CycleCount::Value(1),
            V7Operation::Uqsub8(_) => CycleCount::Value(1),
            V7Operation::Uqsad8(_) => CycleCount::Value(1),
            V7Operation::Usada8(_) => CycleCount::Value(1),
            V7Operation::Usad8(_) => CycleCount::Value(1),
            V7Operation::Usat(_) | V7Operation::Usat16(_) => CycleCount::Value(1),
            V7Operation::Usax(_) => CycleCount::Value(1),
            V7Operation::Usub16(_) => CycleCount::Value(1),
            V7Operation::Usub8(_) => CycleCount::Value(1),
            V7Operation::Uxtab(_) => CycleCount::Value(1),
            V7Operation::Uxtab16(_) => CycleCount::Value(1),
            V7Operation::Uxtah(_) => CycleCount::Value(1),
            V7Operation::Uxtb(_) => CycleCount::Value(1),
            V7Operation::Uxtb16(_) => CycleCount::Value(1),
            V7Operation::Uxth(_) => CycleCount::Value(1),
            V7Operation::Wfe(_) => todo!("This requires a model of events"),
            V7Operation::Wfi(_) => todo!("This requires a model of interrupts"),

            // This assumes that we have no core running
            V7Operation::Yield(_) => CycleCount::Value(1),
            V7Operation::Svc(_) => todo!(),
            V7Operation::Stc(_)
            | V7Operation::Mcr(_)
            | V7Operation::Mrc(_)
            | V7Operation::Mrrc(_)
            | V7Operation::Mcrr(_)
            | V7Operation::Cdp(_)
            | V7Operation::LdcImmediate(_)
            | V7Operation::LdcLiteral(_) => todo!(),
            V7Operation::VselF32(_vsel_f32) => todo!(),
            V7Operation::VselF64(_vsel_f64) => todo!(),
            V7Operation::VmlF32(_vml_f32) => todo!(),
            V7Operation::VmlF64(_vml_f64) => todo!(),
            V7Operation::VnmlF32(_vnml_f32) => todo!(),
            V7Operation::VnmlF64(_vnml_f64) => todo!(),
            V7Operation::VnmulF32(_vnmul_f32) => todo!(),
            V7Operation::VnmulF64(_vnmul_f64) => todo!(),
            V7Operation::VmulF32(_vmul_f32) => todo!(),
            V7Operation::VmulF64(_vmul_f64) => todo!(),
            V7Operation::VaddF32(_vadd_f32) => todo!(),
            V7Operation::VaddF64(_vadd_f64) => todo!(),
            V7Operation::VsubF32(_vsub_f32) => todo!(),
            V7Operation::VsubF64(_vsub_f64) => todo!(),
            V7Operation::VdivF32(_vdiv_f32) => todo!(),
            V7Operation::VdivF64(_vdiv_f64) => todo!(),
            V7Operation::VmaxF32(_vmax_f32) => todo!(),
            V7Operation::VmaxF64(_vmax_f64) => todo!(),
            V7Operation::VminF32(_vmin_f32) => todo!(),
            V7Operation::VminF64(_vmin_f64) => todo!(),
            V7Operation::VmovImmediateF32(_vmov_immediate_f32) => todo!(),
            V7Operation::VmovImmediateF64(_vmov_immediate_f64) => todo!(),
            V7Operation::VmovRegisterF32(_vmov_register_f32) => todo!(),
            V7Operation::VmovRegisterF64(_vmov_register_f64) => todo!(),
            V7Operation::VabsF32(_vabs_f32) => todo!(),
            V7Operation::VabsF64(_vabs_f64) => todo!(),
            V7Operation::VnegF32(_vneg_f32) => todo!(),
            V7Operation::VnegF64(_vneg_f64) => todo!(),
            V7Operation::VsqrtF32(_vsqrt_f32) => todo!(),
            V7Operation::VsqrtF64(_vsqrt_f64) => todo!(),
            V7Operation::VcvtF32(_vcvt_f32) => todo!(),
            V7Operation::VcvtF64(_vcvt_f64) => todo!(),
            V7Operation::VcmpF32(_vcmp_f32) => todo!(),
            V7Operation::VcmpF64(_vcmp_f64) => todo!(),
            V7Operation::VcmpZeroF32(_vcmp_zero_f32) => todo!(),
            V7Operation::VcmpZeroF64(_vcmp_zero_f64) => todo!(),
            V7Operation::VrintF32(_vrint_f32) => todo!(),
            V7Operation::VrintF64(_vrint_f64) => todo!(),
            V7Operation::VcvtF64F32(_vcvt_f64_f32) => todo!(),
            V7Operation::VcvtF32F64(_vcvt_f32_f64) => todo!(),
            V7Operation::Vcvt(_vcvt) => todo!(),
            V7Operation::VrintCustomRoundingF32(_vrint_custom_rounding_f32) => todo!(),
            V7Operation::VrintCustomRoundingF64(_vrint_custom_rounding_f64) => todo!(),
            V7Operation::VcvtCustomRoundingIntF32(_vcvt_custom_rounding_int_f32) => todo!(),
            V7Operation::VcvtCustomRoundingIntF64(_vcvt_custom_rounding_int_f64) => todo!(),
            V7Operation::VStmF32(_vstm_f32) => todo!(),
            V7Operation::VStmF64(_vstm_f64) => todo!(),
            V7Operation::VStrF32(_vstr_f32) => todo!(),
            V7Operation::VStrF64(_vstr_f64) => todo!(),
            V7Operation::VPushF32(_vpush_f32) => todo!(),
            V7Operation::VPushF64(_vpush_f64) => todo!(),
            V7Operation::VLdrF32(_vldr_f32) => todo!(),
            V7Operation::VLdrF64(_vldr_f64) => todo!(),
            V7Operation::VPopF32(_vpop_f32) => todo!(),
            V7Operation::VPopF64(_vpop_f64) => todo!(),
            V7Operation::VLdmF32(_vldm_f32) => todo!(),
            V7Operation::VLdmF64(_vldm_f64) => todo!(),
            V7Operation::VmoveF32(_vmove_f32) => todo!(),
            V7Operation::VmoveHalfWord(_vmove_half_word) => todo!(),
            V7Operation::Vmsr(_vmsr) => todo!(),
            V7Operation::Vmrs(_vmrs) => todo!(),
            V7Operation::VmoveDoubleF32(_vmove_double_f32) => todo!(),
            V7Operation::VmoveF64(_vmove_f64) => todo!(),
        }
    }
}
