use disarmv7::operation::{Sel, Uadd16, Uadd8, Uasx, Uhadd16, Uhadd8, Uhasx, Uhsax, Uhsub16, Uhsub8, Umaal, Uxtb16, Uxth};
use transpiler::pseudo;

use super::Decode;
use crate::arch::arm::v7::decoder::sealed::Into;

impl Decode for Umaal {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Umaal { rdlo, rdhi, rn, rm } = self;

        let rdlo = rdlo.local_into();
        let rdhi = rdhi.local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        pseudo!([
            rn:u32;
            rm:u32;
            rdlo:u32;
            rdhi:u32;
            let result = Resize(rn,u64) * Resize(rm,u64);

            result = Resize(result,u64) + Resize(rdlo,u64);
            result = result + Resize(rdhi,u64);

            rdhi = Resize(result<63:32:u64>,u32);
            rdlo = Resize(result<32:0:u64>,u32);
        ])
    }
}

impl Decode for Uhsub8 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uhsub8 { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        pseudo!([
            rn:u32;
            rd:u32;
            rm:u32;
            let lhs = resize(rn<7:0>,u32);
            let rhs = resize(rm<7:0>,u32);
            let diff1 = lhs - rhs;
            lhs = resize(rn<15:8>,u32);
            rhs = resize(rm<15:8>,u32);
            let diff2 = lhs - rhs;
            lhs = resize(rn<23:16>,u32);
            rhs = resize(rm<23:16>,u32);
            let diff3 = lhs - rhs;
            lhs = resize(rn<31:24>,u32);
            rhs = resize(rm<31:24>,u32);
            let diff4 = lhs - rhs;
            rd = Resize(diff1<8:1>,u32);
            let intermediate = diff2<8:1> << 8.local_into();
            rd = rd | Resize(intermediate,u32);
            intermediate = diff3<8:1> << 16.local_into();
            rd = rd | Resize(intermediate,u32);
            intermediate = diff4<8:1> << 24.local_into();
            rd = rd | Resize(intermediate,u32);
        ])
    }
}

impl Decode for Uhsub16 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uhsub16 { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        pseudo!([
            rn:u32;
            rm:u32;
            rd:u32;
            let diff1 = Resize(rn<15:0>,u32) + Resize(rm<15:0>,u32);
            let diff2 = Resize(rn<31:16>,u32) + Resize(rm<31:16>,u32);
            rd = Resize(diff1<16:1>,u32);
            let diff2_shifted = Resize(diff2<16:1>,u32) << 16.local_into();
            rd = rd | diff2_shifted;
        ])
    }
}

impl Decode for Uhsax {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uhsax { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        pseudo!([
            rn:u32;
            rd:u32;
            rm:u32;
            let diff = Resize(rn<15:0>,u32) + Resize(rm<31:16>,u32);
            let sum = Resize(rn<31:16>,u32) - Resize(rm<15:0>,u32);
            rd = Resize(diff<16:1>,u32);
            let shifted = Resize(sum<16:1>,u32) << 16.local_into();
            rd = rd | shifted;
            Abort("Incomplete instruction UHSAX");
            // TODO! Implement aspr.ge
        ])
    }
}

impl Decode for Uhasx {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uhasx { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        pseudo!([
            rn:u32;
            rd:u32;
            rm:u32;
            let diff = Resize(rn<15:0>,u32) - Resize(rm<31:16>,u32);
            let sum = Resize(rn<31:16>,u32) + Resize(rm<15:0>,u32);
            rd = Resize(diff<16:1>,u32);
            let shifted = Resize(sum<16:1>,u32) << 16.local_into();
            rd = rd | shifted;
            // TODO! Implement aspr.ge
            Abort("Incomplete instruction UHASX");
        ])
    }
}

impl Decode for Uhadd8 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uhadd8 { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();
        pseudo!([
            rn:u32;
            rm:u32;
            rd:u32;

            let sum1 = Resize(rn<7:0>,u32) + Resize(rm<7:0>,u32);
            let sum2 = Resize(rn<15:8>,u32) + Resize(rm<15:8>,u32);
            let sum3 = Resize(rn<23:16>,u32) + Resize(rm<23:16>,u32);
            let sum4 = Resize(rn<31:24>,u32) + Resize(rm<31:24>,u32);

            rd = Resize(sum1<8:1>,u32);

            let sum2_shifted = Resize(sum2<8:1>,u32) << 8.local_into();
            let sum3_shifted = Resize(sum3<8:1>,u32) << 16.local_into();
            let sum4_shifted = Resize(sum4<8:1>,u32) << 24.local_into();

            rd = rd | sum2_shifted;
            rd = rd | sum3_shifted;
            rd = rd | sum4_shifted;
        ])
    }
}

impl Decode for Uhadd16 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uhadd16 { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();
        pseudo!([
            rn:u32;
            rm:u32;
            rd:u32;
            let sum1 = Resize(rn<15:0>,u32) + Resize(rm<15:0>,u32);
            let sum2 = Resize(rn<31:16>,u32) + Resize(rm<31:16>,u32);
            rd = Resize(sum1<16:1>,u32);
            let sum2_half = Resize(sum2<16:1>,u32) << 16.local_into();
            rd = rd | sum2_half;
        ])
    }
}

impl Decode for Uasx {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uasx { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();
        pseudo!([
            rn:u32;
            rm:u32;
            rd:u32;
            let diff = Resize(rn<15:0>,u32) - Resize(rm<31:16>,u32);
            let sum = Resize(rn<31:16>,u32) + Resize(rm<15:0>,u32);
            rd = Resize(diff<15:0>,u32);
            let shifted = Resize(sum<15:0>,u32) << 16.local_into();
            rd = rd | shifted;
            // TODO! Implement aspr.ge
            Abort("Incomplete instruction UASX");
        ])
    }
}

impl Decode for Uadd8 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uadd8 { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();
        pseudo!([
            rn:u32;
            rd:u32;
            rm:u32;

            let sum1 = Resize(rn<7:0>,u32) + Resize(rm<7:0>,u32);
            let sum2 = Resize(rn<15:8>,u32) + Resize(rm<15:8>,u32);
            let sum3 = Resize(rn<23:16>,u32) + Resize(rm<23:16>,u32);
            let sum4 = Resize(rn<31:24>,u32) + Resize(rm<31:24>,u32);
            rd = Resize(sum1<7:0>,u32);
            let intermediate = Resize(sum2<7:0>,u32) << 8.local_into();
            rd = rd | intermediate;
            intermediate = Resize(sum3<7:0>,u32) << 16.local_into();
            rd = rd | intermediate;
            intermediate = Resize(sum4<7:0>,u32) << 24.local_into();
            rd = rd | intermediate;
            // TODO! Add in GE flags
            Abort("Incomplete instruction UADD8");
        ])
    }
}

impl Decode for Uadd16 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uadd16 { rd, rn, rm } = self;
        let rn = rn.local_into();
        let rd = rd.local_into().unwrap_or(rn.clone());
        let rm = rm.local_into();

        pseudo!([
            rn:u32;
            rd:u32;
            rm:u32;
            let lsh_mask:u32 = (u16::MAX as u32).local_into();

            let rn_lsh = rn & lsh_mask;
            let rm_lsh = rm & lsh_mask;

            let sum1 = rn_lsh + rm_lsh;
            sum1 = sum1 & lsh_mask;

            let rn_msh = rn >> 16.local_into();
            rn_msh = rn_msh & lsh_mask;

            let rm_msh = rm >> 16.local_into();
            rm_msh = rm & lsh_mask;

            let sum2 = rn_msh + rm_msh;
            sum2 = sum2 & lsh_mask;
            sum2 = sum2 << 16.local_into();

            rd = sum1 | sum2;

            // TODO! Fix GE flags
            Abort("Incomplete instruction UADD8");
        ])
    }
}

impl Decode for Uxth {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uxth { rd, rm, rotation } = self;
        let rd = rd.local_into();
        let rm = rm.local_into();
        let rotation = rotation.unwrap_or(0);
        pseudo!([
            let rotated:u32 = rm;
            if (rotation != 0) {
                rotated = Ror(rm,rotation.local_into());
            }
            rd = ZeroExtend(rotated<15:0>,32);
        ])
    }
}

impl Decode for Uxtb16 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Uxtb16 { rd, rm, rotation } = self;
        let rm = rm.local_into();
        let rd = rd.local_into().unwrap_or(rm.clone());
        let rotation = rotation.unwrap_or(0);

        pseudo!([
            rm:u32;
            let rotated:u32 = Ror(rm,rotation.local_into());
            rd = ZeroExtend(rotated<7:0>,32);
            rotated = Resize(rotated<23:16>,u32) << 16.local_into();
            rd = rd | rotated;
        ])
    }
}

impl Decode for Sel {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { rd, rn, rm } = self;
        let rd = rd.unwrap_or(*rn).local_into();
        let rn = rn.local_into();
        let rm = rm.local_into();
        let remove_0_mask = (!(u8::MAX as u32)).local_into();
        let remove_1_mask = (!((u8::MAX as u32) << 8)).local_into();
        let remove_2_mask = (!((u8::MAX as u32) << 16)).local_into();
        let remove_3_mask = (!((u8::MAX as u32) << 24)).local_into();
        pseudo!([
            rm:u32;rn:u32;rd:u32;
            let ge = Register("APSR.GE");
            let result = rm;
            let cond:u1 = ge<0>;

            let new_result = 0u32;
            let intermediate = 0u32;
            Ite(cond == true,{
                new_result = result & remove_0_mask;
                result = new_result | Resize(rn<7:0>,u32);
            },{});
            cond:u1 = ge<1>;
            Ite(cond == true,{
                new_result = result & remove_1_mask;
                intermediate  = Resize(rn<15:8>,u32) << 8u32;
                result = new_result | intermediate;
            },{});
            cond:u1 = ge<2>;
            Ite(cond == true,{
                new_result = result & remove_2_mask;
                intermediate  = Resize(rn<23:16>,u32) << 16u32;
                result = new_result | intermediate;
            },{});
            cond:u1 = ge<3>;
            Ite(cond == true,{
                new_result = result & remove_3_mask;
                intermediate  = Resize(rn<31:24>,u32) << 23u32;
                result = new_result | intermediate;
            },{});
            rd = result;
        ])
    }
}
