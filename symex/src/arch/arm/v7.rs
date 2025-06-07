use std::fmt::Display;

use anyhow::Context;
use decoder::{sealed::Into, Convert};
use disarmv7::prelude::{Operation as V7Operation, *};
use general_assembly::{extension::ieee754::RoundingMode, operation::Operation, shift::Shift};

use crate::{
    arch::{ArchError, Architecture, ArchitectureOverride, ParseError, SupportedArchitecture, InterfaceRegister},
    debug,
    executor::{
        hooks::{HookContainer, PCHook},
        instruction::Instruction,
        state::GAState,
        ResultOrTerminate,
    },
    extract,
    project::dwarf_helper::SubProgramMap,
    smt::{SmtExpr, SmtMap, SmtSolver},
    trace,
    GAError,
    Mask,
};

//#[rustfmt::skip]
pub mod compare;
pub mod decoder;
#[cfg(test)]
pub mod test;
pub mod timing;

/// Type level denotation for the ARMV7-EM ISA.
#[derive(Debug, Default, Clone)]
pub struct ArmV7EM {
    pub in_it_block: bool,
    pub it_instr: bool,
}

impl ArmV7EM {
    fn add_apsr_hooks<C: crate::Composition>(&self, cfg: &mut HookContainer<C>, _map: &mut SubProgramMap) {
        let write_aspr_n = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting APSR.N to {value:?}{:?}", value.get_constant());
            let reg = state.memory.get_register("XPSR")?.replace_part(31, value);
            state.memory.set_register("XPSR", reg);
            Ok(())
        };
        let read_apsr_n = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?;
            let reg_value = reg.slice(31, 31);
            Ok(reg_value)
        };

        let write_aspr = |state: &mut GAState<C>, value: C::SmtExpression| {
            let upper = value.slice(27, 31);
            let lower = value.slice(16, 19);

            let reg = state.memory.get_register("XPSR")?;

            let ret = reg.replace_part(16, lower).replace_part(27, upper);
            state.memory.set_register("XPSR", reg);

            Ok(())
        };
        let read_apsr = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?;
            let upper = reg.slice(27, 31);
            let lower = reg.slice(16, 19);
            let ret = lower.resize_unsigned(32).shift(&state.memory.from_u64(16, 32), Shift::Lsl).replace_part(27, upper);

            Ok(ret)
        };

        cfg.add_register_write_hook("APSR".to_string(), write_aspr);
        cfg.add_register_read_hook("APSR".to_string(), read_apsr);

        cfg.add_flag_write_hook("APSR.N".to_string(), write_aspr_n);
        cfg.add_flag_read_hook("APSR.N".to_string(), read_apsr_n);
        cfg.add_flag_write_hook("N".to_string(), write_aspr_n);
        cfg.add_flag_read_hook("N".to_string(), read_apsr_n);

        let write_apsr_z = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting APSR.Z to {value:?}{:?}", value.get_constant());
            let reg = state.memory.get_register("XPSR")?.replace_part(30, value);
            state.memory.set_register("XPSR", reg)?;
            Ok(())
        };
        let read_apsr_z = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?.slice(30, 30);
            Ok(reg)
        };

        cfg.add_flag_write_hook("APSR.Z".to_string(), write_apsr_z);
        cfg.add_flag_read_hook("APSR.Z".to_string(), read_apsr_z);
        cfg.add_flag_write_hook("Z".to_string(), write_apsr_z);
        cfg.add_flag_read_hook("Z".to_string(), read_apsr_z);

        let write_apsr_c = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting APSR.C to {value:?} {:?}", value.get_constant());
            let reg = state.memory.get_register("XPSR")?.replace_part(29, value);
            state.memory.set_register("XPSR", reg)?;
            Ok(())
        };
        let read_apsr_c = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?.slice(29, 29);
            trace!("READ APSR.C, {:?}", reg.get_constant());

            Ok(reg)
        };

        cfg.add_flag_write_hook("APSR.C".to_string(), write_apsr_c);
        cfg.add_flag_read_hook("APSR.C".to_string(), read_apsr_c);
        cfg.add_flag_write_hook("C".to_string(), write_apsr_c);
        cfg.add_flag_read_hook("C".to_string(), read_apsr_c);

        let write_apsr_v = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting APSR.V to {value:?}{:?}", value.get_constant());
            let reg = state.memory.get_register("XPSR")?.replace_part(28, value);
            state.memory.set_register("XPSR", reg)?;
            Ok(())
        };
        let read_apsr_v = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?;
            let reg = reg.slice(28, 28);
            trace!("READ APSR.V, {:?}", reg.get_constant());

            Ok(reg)
        };

        cfg.add_flag_write_hook("APSR.V".to_string(), write_apsr_v);
        cfg.add_flag_read_hook("APSR.V".to_string(), read_apsr_v);
        cfg.add_flag_write_hook("V".to_string(), write_apsr_v);
        cfg.add_flag_read_hook("V".to_string(), read_apsr_v);

        let write_apsr_q = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting APSR.Q to {value:?} {:?}", value.get_constant());
            let reg = state.memory.get_register("XPSR")?;
            reg.replace_part(27, value);
            trace!("WRITE APSR.Q, {:?}", reg);
            state.memory.set_register("XPSR", reg)?;
            Ok(())
        };
        let read_apsr_q_flag = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?.slice(27, 27);
            trace!("READ APSR.Q, {:?},size{}", reg, reg.size());
            Ok(reg.resize_unsigned(1))
        };

        cfg.add_flag_write_hook("APSR.Q".to_string(), write_apsr_q);
        cfg.add_flag_read_hook("APSR.Q".to_string(), read_apsr_q_flag);
        cfg.add_flag_write_hook("Q".to_string(), write_apsr_q);
        cfg.add_flag_read_hook("Q".to_string(), read_apsr_q_flag);

        let write_apsr_ge = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(4);
            let reg = state.memory.get_register("XPSR")?.replace_part(16, value.clone());
            state.memory.set_register("XPSR", value.or(&reg))?;
            Ok(())
        };
        let read_apsr_ge = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?;
            let reg = reg.slice(16, 19).resize_unsigned(32);
            Ok(reg)
        };

        cfg.add_register_write_hook("APSR.GE".to_string(), write_apsr_ge);
        cfg.add_register_read_hook("APSR.GE".to_string(), read_apsr_ge);
    }

    fn add_itstate_hooks<C: crate::Composition>(&self, cfg: &mut HookContainer<C>, _map: &mut SubProgramMap) {
        let it_read = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("XPSR")?;
            let it_1_0 = reg.slice(25, 26);
            let it = reg.slice(8, 15).replace_part(0, it_1_0);
            trace!("IT : {:?}", it.get_constant());
            Ok(it.resize_unsigned(32))
        };
        cfg.add_register_read_hook("ITSTATE.IT".to_string(), it_read);
        let it_write = |state: &mut GAState<C>, value: C::SmtExpression| {
            let val_7_2 = value.slice(2, 7);
            let val_1_0 = value.slice(0, 1);

            let value = value.get_constant().expect("It state must be deterministic");
            // let val_1_0 = state.memory.from_u64(value.mask::<0, 1>(),
            // 32).resize_unsigned(2); let val_7_2 =
            // state.memory.from_u64(value.mask::<2, 7>(), 32).resize_unsigned(7);

            let reg = state.memory.get_register("XPSR")?;
            let reg = reg.replace_part(25, val_1_0);
            let reg = reg.replace_part(10, val_7_2);

            state.memory.set_register("XPSR", reg);

            Ok(())
        };
        cfg.add_register_write_hook("ITSTATE.IT".to_string(), it_write);
    }

    fn add_fpscr_hooks<C: crate::Composition>(&self, cfg: &mut HookContainer<C>, _map: &mut SubProgramMap) {
        let write_fpscr_n = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting FPSCR.N to {value:?}");
            let reg = state.memory.get_register("FPSCR")?;
            let reg = reg.replace_part(31, value);
            state.memory.set_register("FPSCR", reg)?;
            Ok(())
        };
        let read_fpscr_n = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("FPSCR")?;
            Ok(reg.slice(31, 31))
        };

        cfg.add_flag_write_hook("FPSCR.N".to_string(), write_fpscr_n);
        cfg.add_flag_read_hook("FPSCR.N".to_string(), read_fpscr_n);

        let write_fpscr_z = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting FPSCR.Z to {value:?}");
            let reg = state.memory.get_register("FPSCR")?;
            let reg = reg.replace_part(30, value);
            state.memory.set_register("FPSCR", reg)?;
            Ok(())
        };
        let read_fpscr_z = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("FPSCR")?;
            Ok(reg.slice(30, 30))
        };

        cfg.add_flag_write_hook("FPSCR.Z".to_string(), write_fpscr_z);
        cfg.add_flag_read_hook("FPSCR.Z".to_string(), read_fpscr_z);

        let write_fpscr_c = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting FPSCR.C to {value:?}");
            let reg = state.memory.get_register("FPSCR")?;
            let reg = reg.replace_part(29, value);
            state.memory.set_register("FPSCR", reg)?;
            Ok(())
        };
        let read_fpscr_c = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("FPSCR")?;
            Ok(reg.slice(29, 29))
        };

        cfg.add_flag_write_hook("FPSCR.C".to_string(), write_fpscr_c);
        cfg.add_flag_read_hook("FPSCR.C".to_string(), read_fpscr_c);

        let write_fpscr_v = |state: &mut GAState<C>, value: C::SmtExpression| {
            let value = value.resize_unsigned(1);
            trace!("Setting FPSCR.V to {value:?}");
            let reg = state.memory.get_register("FPSCR")?;
            let reg = reg.replace_part(28, value);
            state.memory.set_register("FPSCR", reg)?;
            Ok(())
        };
        let read_fpscr_v = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("FPSCR")?;
            Ok(reg.slice(28, 28))
        };

        cfg.add_flag_write_hook("FPSCR.V".to_string(), write_fpscr_v);
        cfg.add_flag_read_hook("FPSCR.V".to_string(), read_fpscr_v);

        let write_fpscr_rm = |state: &mut GAState<C>, value: C::SmtExpression| {
            let reg = state.memory.get_register("FPSCR")?;
            let value = value.resize_unsigned(2);
            state.fp_state.rounding_mode = match value.get_constant() {
                Some(0b00) => RoundingMode::TiesToEven,
                Some(0b01) => RoundingMode::TiesTowardPositive,
                Some(0b10) => RoundingMode::TiesTowardNegative,
                Some(0b11) => RoundingMode::TiesTowardZero,
                Some(_) => return Err(GAError::InvalidRoundingMode).context("While writing to FPSCR"),
                None => return Err(GAError::InvalidRoundingMode).context("While writing to FPSCR, non constant."),
            };
            let reg = reg.replace_part(22, value);
            state.memory.set_register("FPSCR", reg)?;
            Ok(())
        };
        let read_fpscr_rm = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("FPSCR")?;
            Ok(reg.slice(22, 23).resize_unsigned(32))
        };

        cfg.add_register_write_hook("FPSCR.RM".to_string(), write_fpscr_rm);
        cfg.add_register_read_hook("FPSCR.RM".to_string(), read_fpscr_rm);
        let read_fpscr = |state: &mut GAState<C>| {
            let reg = state.memory.get_register("FPSCR")?;
            Ok(reg)
        };
        cfg.add_register_read_hook("FPSCR".to_string(), read_fpscr);
    }

    fn current_cond<C: crate::Composition>(state: &mut GAState<C>) -> (u8, Option<u64>) {
        let it = state.get_register("ITSTATE.IT".to_string()).expect("Failed to read itstate");
        let it_3_0 = it.slice(0, 3);
        let pure_zeros = it._eq(&state.memory.from_u64(0, it.size()));
        let pure_zeros = pure_zeros.get_constant_bool();
        // if pure_zeros.is_none() {
        //     panic!()
        // }
        if let Some(true) = pure_zeros {
            return (0b1110, it.resize_unsigned(8).get_constant());
        }
        let pure_zeros = it_3_0._eq(&state.memory.from_u64(0, it_3_0.size()));
        if pure_zeros.get_constant().is_none() {
            unimplemented!("Unpredictable");
        }
        let it_7_4 = it.slice(4, 7).resize_unsigned(8);
        match it_7_4.get_constant() {
            Some(val) => (val as u8, it.resize_unsigned(8).get_constant()),
            _ => unimplemented!("Unpredictable"),
        }
    }

    fn it_advance<C: crate::Composition>(state: &mut GAState<C>) {
        if state.architecture.as_v7().it_instr {
            return;
        }
        trace!("Running IT advance");
        let (cond, it) = Self::current_cond(state);
        if let Some(it) = it {
            trace!("IT STATE WAS ZERO in last 4 bits");
            if it.mask::<0, 3>() == 0 {
                return;
            }
        }
        let it = state.get_register("ITSTATE.IT").expect("Failed to read itstate");
        let it_2_0 = it.slice(0, 2);
        let pure_zeros = it_2_0._eq(&state.memory.from_u64(0, it_2_0.size()));
        let pure_zeros = pure_zeros.get_constant();
        if pure_zeros.is_none() {
            unimplemented!("Unpredictable");
        }

        if let Some(1) = pure_zeros {
            state.set_register("ITSTATE.IT".to_string(), state.memory.from_u64(0, 32));
            return;
        }
        let it_4_0 = it.slice(0, 4).shift(&state.memory.from_u64(1, 5), Shift::Lsl);
        let it = it.replace_part(0, it_4_0);
        state.set_register("ITSTATE.IT".to_string(), it);
    }
}

impl<Override: ArchitectureOverride> Architecture<Override> for ArmV7EM {
    type ISA = disarmv7::operation::Operation;

    fn initiate_state<C>(state: &mut GAState<C>)
    where
        C: crate::Composition<ArchitectureOverride = Override>,
    {
        trace!("Setting XPSR to zeros");
        state.set_register("XPSR".to_string(), state.memory.from_u64(0, 32));

        let rm = state.get_register("FPSCR.RM").expect("RM read to be valid");
        let rm = rm.get_constant().unwrap_or(0b11);
        state.set_register("FPSCR.RM", state.memory.from_u64(rm, 32));
    }

    fn pre_instruction_loading_hook<C>(state: &mut GAState<C>)
    where
        C: crate::Composition<ArchitectureOverride = Override>,
    {
        let rm = state.get_register("FPSCR.RM").expect("RM read to be valid");
        let rm = rm.get_constant().unwrap_or(0b11);
        state.set_register("FPSCR.RM", state.memory.from_u64(rm, 32));

        state.architecture.as_v7().in_it_block = false;
        let (cond, it) = Self::current_cond(state);
        trace!("ITSTATE.IT as {cond}");
        trace!("ITSTATE.IT as {it:?}");
        let cond = Condition::try_from(cond)
            .expect("Internal conditon checks produced invalid instruction condition.")
            .local_into();
        // state.instruction_conditions.clear();
        if general_assembly::condition::Condition::None == cond {
            return;
        }

        if let Some(it) = it {
            if it.mask::<1, 3>() != 0b111 {
                trace!("Pushing CONDITON {cond:?}");
                state.architecture.as_v7().in_it_block = true;
                state.instruction_conditions.push_back(cond);
            }
        }
        trace!("ITSTATE.IT as {cond:?}");
        // debug!("ITSTATE.IT as {:?}", state.instruction_conditions);
    }

    fn post_instruction_execution_hook<C>(state: &mut GAState<C>)
    where
        C: crate::Composition<ArchitectureOverride = Override>,
    {
        Self::it_advance(state);
    }

    fn get_register_name(reg:InterfaceRegister) -> String {
        match reg {
            InterfaceRegister::ProgramCounter => "PC",
            InterfaceRegister::ReturnAddress => "LR"
        }.to_string()
    }

    #[allow(clippy::cast_possible_truncation)]
    fn add_hooks<C: crate::Composition>(&self, cfg: &mut HookContainer<C>, map: &mut SubProgramMap) {
        trace!("Adding armv7em hooks");
        let symbolic_sized = |state: &mut GAState<C>| {
            let value_ptr = match state.memory.get_register("R0") {
                Ok(val) => val,
                Err(e) => return Err(e).context("While resolving address for new symbolic value"),
            };

            let size = (match state.memory.get_register("R1") {
                Ok(val) => val,
                Err(e) => return Err(e).context("While resolving size for new symbolic value"),
            })
            .get_constant()
            .unwrap()
                * 8;
            let name = state.label_new_symbolic("any");
            if size == 0 {
                let lr = state.get_register("LR".to_owned())?;
                state.set_register("PC".to_owned(), lr)?;
                return Ok(());
            }
            let symb_value = state.memory.unconstrained(&name, size as u32);
            // We should be able to do this now!
            // TODO: We need to label this with proper variable names if possible.
            //state.marked_symbolic.push(Variable {
            //    name: Some(name),
            //    value: symb_value.clone(),
            //    ty: ExpressionType::Integer(size as usize),
            //});

            match state.memory.set(&value_ptr, symb_value) {
                Ok(_) => {}
                Err(e) => return Err(e).context("While assigning new symbolic value"),
            };

            let lr = state.get_register("LR".to_owned())?;
            state.set_register("PC".to_owned(), lr)?;
            Ok(())
        };

        if let Err(_) = cfg.add_pc_hook_regex(map, r"^symbolic_size$", PCHook::Intrinsic(symbolic_sized)) {
            debug!("Could not add symoblic hook, must not contain any calls to `symbolic_size`");
        }
        if let Err(_) = cfg.add_pc_hook_regex(map, r"^symbolic_size<.+>$", PCHook::Intrinsic(symbolic_sized)) {
            debug!("Could not add symoblic hook, must not contain any calls to `symbolic_size<.+>`");
        }

        if let Err(_) = cfg.add_pc_hook_regex(map, r"^HardFault.*$", PCHook::EndFailure("Hardfault")) {
            trace!("Could not add hardfault hook");
        }
        // §B1.4 Specifies that R[15] => Addr(Current instruction) + 4
        //
        // This can be translated in to
        //
        // PC - Size(prev instruction) / 8 + 4
        // as PC points to the next instruction, we
        //
        //
        // Or we can simply take the previous PC + 4.
        let read_pc = |state: &mut GAState<C>| {
            let size = state.current_instruction.as_ref().unwrap().instruction_size / 8;
            let register = state.memory.get_pc()?.get_constant().unwrap();
            let new_pc = state.memory.from_u64(register - size as u64 + 4, state.memory.get_word_size()).simplify();
            Ok(new_pc)
        };
        // let read_primask = |state: &mut GAState<C>| {
        //     let primask: C::SmtExpression = state.memory.from_u64(0,
        // state.memory.get_word_size()).simplify();     Ok(primask)
        // };
        //
        // let write_primask = |_state: &mut GAState<C>, _| {
        //     panic!("Cannot write to PRIMASK");
        // };

        let read_any = |state: &mut GAState<C>| Ok(state.memory.unconstrained_unnamed(32));

        let read_sp = |state: &mut GAState<C>| {
            let two = state.memory.from_u64((!(0b11u32)) as u64, 32);
            let sp = state.get_register("SP".to_owned()).unwrap();
            let sp = sp.simplify();
            Ok(sp.and(&two))
        };

        let write_pc = |state: &mut GAState<C>, value| state.set_register("PC".to_owned(), value);
        let write_sp = |state: &mut GAState<C>, value: C::SmtExpression| {
            //state.set_register("SP".to_string(),
            // value.and(&state.memory.from_u64((!(0b11u32)) as u64, 32)))?; let
            // sp = state.get_register("SP".to_owned()).unwrap(); let sp = sp.
            // simplify();
            state.set_register("SP".to_owned(), value)
        };

        cfg.add_register_read_hook("PC+".to_string(), read_pc);
        // cfg.add_register_read_hook("PRIMASK".to_string(), read_primask);
        // cfg.add_register_write_hook("PRIMASK".to_string(), write_primask);
        cfg.add_register_write_hook("PC+".to_owned(), write_pc);
        cfg.add_register_read_hook("SP&".to_owned(), read_sp);
        cfg.add_register_write_hook("SP&".to_owned(), write_sp);
        cfg.add_register_read_hook("ANY".to_owned(), read_any);

        // let assume = |state: &mut GAState<C>| {
        //     // stop counting
        //     state.count_cycles = false;
        //     let r0 = match state.memory.get_register("R0") {
        //         Ok(val) => val,
        //         Err(e) => return ResultOrTerminate::Result(Err(e).context("While
        // resolving condition to assume")),     };
        //
        //     trace!("Assuming that {:?} == 1", r0.get_constant());
        //     let r0 = r0._ne(&state.memory.from_u64(0, r0.size()));
        //     // state.constraints.push();
        //     // if !state.constraints.is_sat_with_constraint(&r0).is_ok_and(|el| el) {
        //     //     return ResultOrTerminate::Failure("Tried to assert unsatisfiable
        //     // formula".to_string()); }
        //     //
        //     // state.constraints.pop();
        //     state.constraints.assert(&r0);
        //
        //     // jump back to where the function was called from
        //     // let lr = state.get_register("LR".to_owned()).unwrap();
        //     // state.set_register("PC".to_owned(), lr)?;
        //     ResultOrTerminate::Result(Ok(()))
        // };
        // cfg.add_pc_precondition_regex(map, r"^assume$", assume);

        self.add_apsr_hooks(cfg, map);
        self.add_fpscr_hooks(cfg, map);
        self.add_itstate_hooks(cfg, map);

        // reset always done
        let read_reset_done = |state: &mut GAState<C>, _addr| {
            let value = state.memory.from_u64(0xffff_ffff, 32);
            Ok(value)
        };
        cfg.add_memory_read_hook(0x4000c008, read_reset_done);
    }

    fn translate<C: crate::Composition>(buff: &[u8], state: &mut GAState<C>) -> Result<Instruction<C>, ArchError> {
        let mut buffer = [0; 4];
        (0..4).zip(buff.iter()).zip(buffer.iter_mut()).for_each(|((_, source), dest)| *dest = *source);
        trace!("decoding, buff : {:?}", buff);
        let mut buff: disarmv7::buffer::PeekableBuffer<u8, _> = buff.iter().cloned().into();

        let instr = V7Operation::parse(&mut buff).map_err(|e| ArchError::ParsingError(e.into(), buffer));
        let v7 = state.architecture.as_v7();
        if let Ok((_, V7Operation::It(_))) = &instr {
            v7.it_instr = true;
        } else {
            v7.it_instr = false;
        }

        debug!("in_it_block: {}", state.get_in_conditional_block());
        debug!("PC{:#x} -> Running {:?}", state.memory.get_pc().unwrap().get_constant().unwrap(), instr);
        let instr = instr?;
        let timing = Self::cycle_count_m4_core(&instr.1);
        let ops: Vec<Operation> = instr.clone().convert(state.get_in_conditional_block());

        Ok(Instruction {
            instruction_size: instr.0 as u32,
            operations: ops,
            max_cycle: timing,
            memory_access: Self::memory_access(&instr.1),
        })
    }

    //fn discover(file: &File<'_>) -> Result<Option<Self>, ArchError> {
    //    let f = match file {
    //        File::Elf32(f) => Ok(f),
    //        _ => Err(ArchError::IncorrectFileType),
    //    }?;
    //    let section = match f.section_by_name(".ARM.attributes") {
    //        Some(section) => Ok(section),
    //        None => Err(ArchError::MissingSection(".ARM.attributes")),
    //    }?;
    //    let isa = arm_isa(&section)?;
    //    match isa {
    //        ArmIsa::ArmV6M => Ok(None),
    //        ArmIsa::ArmV7EM => Ok(Some(ArmV7EM::default())),
    //    }
    //}

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {
            in_it_block: false,
            it_instr: false,
        }
    }

    fn register_number_to_name(idx: u64) -> Option<String> {
        Some(match idx {
            0 => "R0".to_string(),
            1 => "R1".to_string(),
            2 => "R2".to_string(),
            3 => "R3".to_string(),
            4 => "R4".to_string(),
            5 => "R5".to_string(),
            6 => "R6".to_string(),
            7 => "R7".to_string(),
            8 => "R8".to_string(),
            9 => "R9".to_string(),
            10 => "R10".to_string(),
            11 => "R11".to_string(),
            12 => "R12".to_string(),
            13 => "SP".to_string(),
            14 => "LR".to_string(),
            15 => "PC".to_string(),
            0b1_0000 => "XPSR".to_string(),
            16 => "IPSR".to_string(),
            0b10100 => "FAULTMASK".to_string(),
            0b10100 => "PRIMASK".to_string(),
            0b10100 => "BASEPRI".to_string(),
            0b10100 => "CONTROL".to_string(),
            33 => "FPSCR".to_string(),
            idx if (64..(64 + 16)).contains(&idx) => format!("S{}", idx - 64),
            _ => return None,
        })
    }

    fn register_name_to_number(name: &str) -> Option<u64> {
        Some(match name {
            "R0" => 0,
            "R1" => 1,
            "R2" => 2,
            "R3" => 3,
            "R4" => 4,
            "R5" => 5,
            "R6" => 6,
            "R7" => 7,
            "R8" => 8,
            "R9" => 9,
            "R10" => 10,
            "R11" => 11,
            "R12" => 12,
            "SP" => 13,
            "LR" => 14,
            "PC" => 15,
            "XPSR" => 0b1_0000,
            "IPSR" => 16,
            "FAULTMASK" => 0b10100,
            "PRIMASK" => 0b10100,
            "BASEPRI" => 0b10100,
            "CONTROL" => 0b10100,
            "FPSCR" => 33,
            _ if name.starts_with("S") => {
                let num: u64 = name.strip_prefix("S").map(|el| el.parse().ok()).flatten()?;
                64 + num
            }
            _ if name.starts_with("D") => {
                todo!()
            }
            _ => return None,
        })
    }

    fn nan_encoding(ty: general_assembly::extension::ieee754::OperandType) -> u64 {
        match ty {
            general_assembly::extension::ieee754::OperandType::Binary16 => (((0 << 5) | (0x1f)) << 10) | 1 << 9,
            general_assembly::extension::ieee754::OperandType::Binary32 => (((0 << 8) | (0xff)) << 23) | 1 << 22,
            general_assembly::extension::ieee754::OperandType::Binary64 => (((0 << 11) | (0x7ff)) << 52) | 1 << 51,
            _ => unimplemented!("No support for other encodings"),
        }
    }
}

impl Display for ArmV7EM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ARMv7-M")
    }
}

impl From<disarmv7::ParseError> for ParseError {
    fn from(value: disarmv7::ParseError) -> Self {
        match value {
            disarmv7::ParseError::Undefined => ParseError::InvalidInstruction("Undefined instruction".to_string()),
            disarmv7::ParseError::ArchError(aerr) => match aerr {
                disarmv7::prelude::arch::ArchError::InvalidCondition => ParseError::InvalidCondition,
                disarmv7::prelude::arch::ArchError::InvalidRegister(_) => ParseError::InvalidRegister,
                disarmv7::prelude::arch::ArchError::InvalidField(_) => ParseError::MalfromedInstruction,
            },
            disarmv7::ParseError::Unpredictable => ParseError::Unpredictable,
            disarmv7::ParseError::Invalid16Bit(inner) => ParseError::InvalidInstruction(format!("Invalid 16 bit instruction {inner}")),
            disarmv7::ParseError::Invalid32Bit(inner) => ParseError::InvalidInstruction(format!("Invalid 32 bit instruction {inner}")),
            disarmv7::ParseError::InvalidField(_) => ParseError::MalfromedInstruction,
            disarmv7::ParseError::Incomplete32Bit => ParseError::InsufficientInput,
            disarmv7::ParseError::InternalError(info) => ParseError::Generic(info),
            disarmv7::ParseError::IncompleteParser => ParseError::Generic("Encountered instruction that is not yet supported."),
            disarmv7::ParseError::InvalidCondition => ParseError::InvalidCondition,
            disarmv7::ParseError::IncompleteProgram => ParseError::InsufficientInput,
            disarmv7::ParseError::InvalidRegister(_) => ParseError::InvalidRegister,
            disarmv7::ParseError::PartiallyParsed(error, _) => (*error).into(),
            disarmv7::ParseError::InvalidFloatingPointRegister(_) => ParseError::InvalidRegister,
            disarmv7::ParseError::InvalidRoundingMode(_) => ParseError::InvalidRoundingMode,
        }
    }
}

impl<Override: ArchitectureOverride> From<ArmV7EM> for SupportedArchitecture<Override> {
    fn from(val: ArmV7EM) -> SupportedArchitecture<Override> {
        SupportedArchitecture::Armv7EM(val)
    }
}
