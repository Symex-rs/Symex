use disarmv7::{
    arch::{set_flags::LocalUnwrap, Register},
    operation::{SubImmediate, SubRegister, SubSpMinusImmediate, SubSpMinusRegister, Ubfx, Udiv},
};
use general_assembly::prelude::Operand;
use transpiler::pseudo;

use super::{sealed::Into, Decode};

impl Decode for Udiv {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Udiv { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        pseudo!([
            rm:u32 = rm;
            rd:u32 = rd;
            rn:u32 = rn;
            let zero:u32 = 0.local_into();
            Ite(rm == zero,
                {
                    Abort("UsageFault cannot divide by zero.");
                },
                {}
            );
            let result = rn/rm;
            rd = result;
        ])
    }
}

impl Decode for Ubfx {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Ubfx { rd, rn, lsb, width } = self;
        let rn = rn.local_into();
        let rd = rd.local_into();
        let msbit = lsb + (width - 1);
        let lsb = *lsb;
        pseudo!([
            rn:u32 = rn;
            rd = Resize(rn<msbit:lsb>,u32);
        ])
    }
}

impl Decode for SubSpMinusRegister {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { s, rd, rm, shift } = self;
        let s = s.unwrap_or(false);
        let rn = Register::SP.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        let mut ret = vec![];
        local!(shifted);
        shift!(ret.shift rm -> shifted);

        pseudo!(ret.extend[
            rn:u32;
            rm:u32;
            rd:u32;
            let result = rn - shifted;
            if (s) {
                SetNFlag(result);
                SetZFlag(result);
                SetVFlag(rn,shifted,sub);
                SetCFlag(rn,shifted,sub);
            }
            rd = result;
        ]);
        ret
    }
}

impl Decode for SubSpMinusImmediate {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { s, rd, imm } = self;
        let s = s.unwrap_or(false);
        let rd = rd.local_into().unwrap_or(Operand::Register("SP&".to_owned()));
        let imm = imm.local_into();
        let rn = Register::SP.local_into();

        pseudo!([
            rn:u32;
            rd:u32;
            imm:u32;
            let result:u32 = rn - imm;
            if (s) {
                SetNFlag(result);
                SetZFlag(result);
                SetVFlag(rn, imm, sub);
                SetCFlag(rn, imm, sub);
            }
            rd = result;
        ])
    }
}

impl Decode for SubRegister {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { s, rd, rn, rm, shift } = self;
        let s = s.local_unwrap(in_it_block);
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        let mut ret = vec![];
        local!(shifted);
        shift!(ret.shift rm -> shifted);

        pseudo!(ret.extend[
            rm:u32;
            rn:u32;
            rd:u32;
            let result = rn - shifted;

            if (s) {
                SetNFlag(result);
                SetZFlag(result);
                SetCFlag(rn, shifted, sub);
                SetVFlag(rn, shifted, sub);
            }

            rd = result;
        ]);
        ret
    }
}

impl Decode for SubImmediate {
    fn decode(&self, in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { s, rd, rn, imm } = self;
        let s = s.local_unwrap(in_it_block);
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let imm = imm.local_into();
        pseudo!([
            rn:u32;
            rn:u32;
            imm:u32;
            let result = rn - imm;

            if (s) {
                SetNFlag(result);
                SetZFlag(result);
                SetCFlag(rn, imm, sub);
                SetVFlag(rn, imm, sub);
            }

            rd = result;
        ])
    }
}
