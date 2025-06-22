use disarmv7::{
    arch::{register::IEEE754RoundingMode, Condition, Register},
    operation::{
        ConversionArgument,
        F32OrF64,
        IntType,
        RegisterOrAPSR,
        VLdmF32,
        VLdmF64,
        VLdrF32,
        VLdrF64,
        VPopF32,
        VPopF64,
        VPushF32,
        VPushF64,
        VStmF32,
        VStmF64,
        VStrF32,
        VStrF64,
        VabsF32,
        VabsF64,
        VaddF32,
        VaddF64,
        VcmpF32,
        VcmpF64,
        VcmpZeroF32,
        VcmpZeroF64,
        Vcvt,
        VcvtCustomRoundingIntF32,
        VcvtCustomRoundingIntF64,
        VcvtF32,
        VcvtF32F64,
        VcvtF64,
        VcvtF64F32,
        VdivF32,
        VdivF64,
        VfmxF32,
        VfmxF64,
        VmaxF32,
        VmaxF64,
        VminF32,
        VminF64,
        VmlF32,
        VmlF64,
        VmovImmediateF32,
        VmovImmediateF64,
        VmovRegisterF32,
        VmovRegisterF64,
        VmoveDoubleF32,
        VmoveF32,
        VmoveF64,
        Vmrs,
        Vmsr,
        VmulF32,
        VmulF64,
        VnegF32,
        VnegF64,
        VnmlF32,
        VnmlF64,
        VnmulF32,
        VnmulF64,
        VrintCustomRoundingF32,
        VrintCustomRoundingF64,
        VrintF32,
        VrintF64,
        VselF32,
        VselF64,
        VsqrtF32,
        VsqrtF64,
        VsubF32,
        VsubF64,
    },
};
use general_assembly::extension::ieee754::{ComparisonMode, Operand, OperandStorage, OperandType, RoundingMode};
use transpiler::pseudo;

use super::{sealed::Into, Decode};

impl Decode for VabsF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sm } = self;
        let sd = sd.local_into();
        let sm = sm.local_into();
        pseudo!([
            sd:f32;
            sm:f32;
            sd = |sm|;
        ])
    }
}

impl Decode for VabsF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dm } = self;
        let dd = dd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dd:f64;
            dm:f64;
            dd = |dm|;
        ])
    }
}

impl Decode for VaddF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm } = self;
        let sn = sn.local_into();
        let sd = sd.local_into().unwrap_or(sn.clone());
        let sm = sm.local_into();
        pseudo!([
            sn:f32;
            sd:f32;
            sm:f32;
            sd = sn + sm;
        ])
    }
}

impl Decode for VaddF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm } = self;
        let dn = dn.local_into();
        let dd = dd.local_into().unwrap_or(dn.clone());
        let dm = dm.local_into();
        pseudo!([
            dn:f64;dd:f64;dm:f64;
            dd = dn + dm;
        ])
    }
}

impl Decode for VselF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { cond, sd, sn, sm } = self;
        let sd = sd.local_into();
        let sn = sn.local_into();
        let sm = sm.local_into();
        let cond: ComparisonMode = cond.clone().expect("Cannot compare without a condition").local_into();

        pseudo!([
            sd:f32;
            sn:f32;
            sm:f32;
            cond:u1;
            Ite(sn cond sm,
                {
                    sd = sn;
                },
                {
                    sd = sm;
                }
            );
        ])
    }
}

impl Decode for VselF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { cond, dd, dn, dm } = self;
        let dd = dd.local_into();
        let dn = dn.local_into();
        let dm = dm.local_into();
        let cond: ComparisonMode = cond.clone().expect("Cannot compare without a condition").local_into();

        pseudo!([
            dd:f64;
            dn:f64;
            dm:f64;
            Ite(dn cond dm,
                {
                    dd = dn;
                },
                {
                    dd = dm;
                }
            );
        ])
    }
}

impl Decode for VmlF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let VmlF32 { add, sd, sn, sm } = self;
        let add = *add;
        let sd = sd.local_into();
        let sn = sn.local_into();
        let sm = sm.local_into();

        pseudo!([
            sn:f32;
            let mul = sn * sm;
            if (add) {
                sd = sd + mul;
            } else {
                // NOTE: Spec says fp neg here, but as we are not time constrained per-se we might as
                // well just sub.
                sd = sd - mul;
            }

        ])
    }
}

impl Decode for VmlF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let VmlF64 { add, dd, dn, dm } = self;
        let add = *add;
        let dd = dd.local_into();
        let dn = dn.local_into();
        let dm = dm.local_into();

        pseudo!([
            dn:f64;
            let mul = dn * dm;
            if (add) {
                dd = dd + mul;
            } else {
                // NOTE: Spec says fp neg here, but as we are not time constrained per-se we might as
                // well just sub.
                dd = dd - mul;
            }

        ])
    }
}

impl Decode for VnmlF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, sd, sn, sm } = self;
        let add = *add;
        let sd = sd.local_into();
        let sn = sn.local_into();
        let sm = sm.local_into();
        let zero = (0., OperandType::Binary32).local_into();
        pseudo!([
            sn:f32;
            sd:f32;
            let prod = sn*sm;
            sd = zero-sd;
            if (add) {
                prod = zero-prod;
                sd += prod;
            } else {
                sd += prod;
            }
        ])
    }
}

impl Decode for VnmlF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, dd, dn, dm } = self;
        let add = *add;
        let dd = dd.local_into();
        let dn = dn.local_into();
        let dm = dm.local_into();
        let zero = (0., OperandType::Binary32).local_into();
        pseudo!([
            dn:f32;
            dd:f32;
            let prod = dn*dm;
            dd = zero-dd;
            if (add) {
                prod = zero-prod;
                dd += prod;
            } else {
                dd += prod;
            }
        ])
    }
}

impl Decode for VnmulF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm } = self;
        let sn = sn.local_into();
        let sd = sd.local_into().unwrap_or(sn.clone());
        let sm = sm.local_into();
        let zero = (0., OperandType::Binary32).local_into();
        pseudo!([
            let prod:f32 = sn*sm;
            sd = zero - prod;
        ])
    }
}

impl Decode for VnmulF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm } = self;
        let dn = dn.local_into();
        let dd = dd.local_into().unwrap_or(dn.clone());
        let dm = dm.local_into();
        let zero = (0., OperandType::Binary32).local_into();
        pseudo!([
            let prod:f64 = dn*dm;
            dd = zero - prod;
        ])
    }
}

impl Decode for VmulF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm } = self;
        let sn = sn.local_into();
        let sd = sd.local_into().unwrap_or(sn.clone());
        let sm = sm.local_into();
        pseudo!([
            sn:f32;
            sd = sn*sm;
        ])
    }
}

impl Decode for VmulF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm } = self;
        let dn = dn.local_into();
        let dd = dd.local_into().unwrap_or(dn.clone());
        let dm = dm.local_into();
        pseudo!([
            dn:f32;
            dd = dn*dm;
        ])
    }
}

impl Decode for VfmxF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm, negate } = self;
        let sn = sn.local_into();
        let sd = sd.local_into();
        let sm = sm.local_into();
        // Issue with bit 4, IOX exception. Not detected.
        pseudo!([
            sn:f32;
            sd:f32;
            sm:f32;
            if (*negate) {
                sn = 0.0f32 - sn;
            }
            sd = fma(sn,sm,sd);
        ])
    }
}

impl Decode for VfmxF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm, negate } = self;
        let dn = dn.local_into();
        let dd = dd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dn:f64;
            dd:f64;
            dm:f64;
            if (*negate) {
                dn = 0.0f64 - dn;
            }
            dd = fma(dn,dm,dd);

            // dd = dd + mul;
        ])
    }
}

impl Decode for VsubF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm } = self;
        let sn = sn.local_into();
        let sd = sd.local_into().unwrap_or(sn.clone());
        let sm = sm.local_into();
        pseudo!([
            sd:f32 = sn - sm;
        ])
    }
}

impl Decode for VsubF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm } = self;
        let dn = dn.local_into();
        let dd = dd.local_into().unwrap_or(dn.clone());
        let dm = dm.local_into();
        pseudo!([
            dd:f32 = dn - dm;
        ])
    }
}

impl Decode for VdivF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm } = self;
        let sn = sn.local_into();
        let sd = sd.local_into().unwrap_or(sn.clone());
        let sm = sm.local_into();
        pseudo!([
            sd:f32 = sn/sm;
        ])
    }
}

impl Decode for VdivF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm } = self;
        let dn = dn.local_into();
        let dd = dd.local_into().unwrap_or(dn.clone());
        let dm = dm.local_into();
        pseudo!([
            // TODO: Look in to is nan checks here? Should we do them at all?
            dd:f64 = dn/dm;
        ])
    }
}

impl Decode for VmaxF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm } = self;
        let sn = sn.local_into();
        let sd = sd.local_into().unwrap_or(sn.clone());
        let sm = sm.local_into();

        pseudo!([
            sn:f32;
            sm:f32;
            // TODO: look in to nan checks here. Do we need them at all?
            Ite(sn > sm,
                {
                    sd = sn;
                },
                {
                    sd = sm;
                }
            );
        ])
    }
}
impl Decode for VmaxF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm } = self;
        let dn = dn.local_into();
        let dd = dd.local_into().unwrap_or(dn.clone());
        let dm = dm.local_into();

        pseudo!([
            dn:f64;
            dm:f64;
            // TODO: look in to nan checks here. Do we need them at all?
            Ite(dn > dm,
                {
                    dd = dn;
                },
                {
                    dd = dm;
                }
            );
        ])
    }
}

impl Decode for VminF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sn, sm } = self;
        let sn = sn.local_into();
        let sd = sd.local_into().unwrap_or(sn.clone());
        let sm = sm.local_into();

        pseudo!([
            sn:f32;
            sm:f32;
            // TODO: look in to nan checks here. Do we need them at all?
            Ite(sn < sm,
                {
                    sd = sn;
                },
                {
                    sd = sm;
                }
            );
        ])
    }
}

impl Decode for VminF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dn, dm } = self;
        let dn = dn.local_into();
        let dd = dd.local_into().unwrap_or(dn.clone());
        let dm = dm.local_into();

        pseudo!([
            dn:f64;
            dm:f64;
            // TODO: look in to nan checks here. Do we need them at all?
            Ite(dn < dm,
                {
                    dd = dn;
                },
                {
                    dd = dm;
                }
            );
        ])
    }
}

impl Decode for VmovImmediateF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, imm } = self;
        let sd = sd.local_into();
        let imm = Wrappedu32(*imm).local_into();
        pseudo!([
            sd:f32 = imm;
        ])
    }
}

impl Decode for VmovImmediateF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, imm } = self;
        let dd = dd.local_into();
        let imm = Wrappedu64(*imm).local_into();
        pseudo!([
            dd:f64 = imm;
        ])
    }
}

impl Decode for VmovRegisterF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sm } = self;
        let sd = sd.local_into();
        let sm = sm.local_into();
        pseudo!([
            sd:f32 = sm;
        ])
    }
}

impl Decode for VmovRegisterF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dm } = self;
        let dd = dd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dd:f64 = dm;
        ])
    }
}

impl Decode for VnegF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sm } = self;
        let sd = sd.local_into();
        let sm = sm.local_into();

        let zero = (0., OperandType::Binary32).local_into();
        pseudo!([
            sd:f32 = zero - sm;
        ])
    }
}

impl Decode for VnegF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dm } = self;
        let dd = dd.local_into();
        let dm = dm.local_into();

        let zero = (0., OperandType::Binary64).local_into();
        pseudo!([
            dd:f64 = zero - dm;
        ])
    }
}

impl Decode for VsqrtF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, sm } = self;
        let sd = sd.local_into();
        let sm = sm.local_into();
        pseudo!([
            sm:f32;
            sd = Sqrt(sm);
        ])
    }
}

impl Decode for VsqrtF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, dm } = self;
        let dd = dd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dm:f64;
            // TODO: This should generate a move from fp to core.
            dd = Sqrt(dm);
        ])
    }
}

impl Decode for VcvtF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { top, convert_from_half, sd, sm } = self;
        let sd = sd.local_into();
        let sm = sm.local_into();
        let (high_bit, low_bit) = match top {
            true => (31, 16),
            false => (15, 0),
        };
        let mask = (!(((1u32 << 16) - 1) << low_bit)).local_into();
        // NOTE: I am not sure that this will work with the smt solver.
        // However, it is unclear if this is used at all.
        pseudo!([
            if (*convert_from_half) {
                sm:f32;
                let local = Cast(sm,u32);
                local = local<high_bit:low_bit>;
                let local_16 = Resize(local,u16);
                let fp_16:f16 = Cast(local_16,f16);
                sd:f32 = Resize(fp_16,f32);
            } else {
                sm:f32;
                sd:f32;
                let bits_of_sd = Cast(sd,u32) & mask;
                let value = Resize(sm,f16);
                let value_bits = Cast(value,u16);
                let value_bits_u32 = Resize(value_bits,u32) << low_bit.local_into();
                bits_of_sd |= value_bits_u32;
                sd = Cast(bits_of_sd,f32);
            }
        ])
    }
}

impl Decode for VcvtF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { top, convert_from_half, dd, dm } = self;
        let dd = dd.clone().local_into();
        let dm = dm.clone().local_into();
        let (high_bit, low_bit) = match top {
            true => (31, 16),
            false => (15, 0),
        };
        let mask = (!(((1u32 << 16) - 1) << low_bit)).local_into();
        // NOTE: I am not sure that this will work with the smt solver.
        // However, it is unclear if this is used at all.
        pseudo!([
            if (*convert_from_half) {
                dm:f32;
                dd:f64;
                let local = Cast(dm,u32);
                local = local<high_bit:low_bit>;
                let local_16 = Resize(local,u16);
                let fp_16:f16 = Cast(local_16,f16);
                dd:f64 = Resize(fp_16,f64);
            } else {
                dm:f64;
                dd:f32;
                let bits_of_dd = Cast(dd,u32) & mask;
                let value = Resize(dm,f16);
                let value_bits = Cast(value,u16);
                let value_bits_u32 = Resize(value_bits,u32) << low_bit.local_into();
                bits_of_dd |= value_bits_u32;
                dd = Cast(bits_of_dd,f32);
            }
        ])
    }
}

impl Decode for VcmpF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        // Default fpscr.
        // 00000’ : FPSCR<26> : ‘11000000000000000000000000
        let Self { e, sd, sm } = self;
        let e = e.unwrap_or(false);
        let sd = sd.local_into();
        let sm = sm.local_into();
        let ret = pseudo!([
            sd:f32;
            sm:f32;
            let conditional:u1 = IsNan(sd) | IsNan(sm);
            if (e) {
                Ite(conditional != false,
                    {
                        Abort("Invalid Operation exception");
                    },
                    {}
                );
            }
            let is_zero = sd == sm;
            let less_than_zero = sd < sm;
            let greater_than_zero =  sd > sm;

            let c = is_zero | greater_than_zero;

            let ncondtional = !conditional;
            Flag("FPSCR.N") = less_than_zero & ncondtional ;
            Flag("FPSCR.Z") = is_zero & ncondtional;
            Flag("FPSCR.C") = c | conditional;
            Flag("FPSCR.V") = false | conditional;
        ]);

        ret
    }
}

impl Decode for VcmpZeroF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { e, sd } = self;
        let sd = sd.local_into();
        let e = e.unwrap_or(false);

        pseudo!([
            sd:f32;
            let conditional:u1 = IsNan(sd);
            if(e) {
                Ite(conditional != false,
                    {
                        Abort("Invalid Operation exception");
                    },
                    {}
                );
            }
            let is_zero = sd == 0.0f32;
            let less_than_zero = sd < 0.0f32;
            let greater_than_zero =  sd > 0.0f32;

            let c = is_zero | greater_than_zero;

            let ncondition = !conditional;

            Flag("FPSCR.N") = less_than_zero & ncondition;
            Flag("FPSCR.Z") = is_zero & ncondition;
            Flag("FPSCR.C") = c | conditional;
            Flag("FPSCR.V") = false | conditional;
        ])
    }
}

impl Decode for VcmpZeroF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { e, dd } = self;
        let dd = dd.local_into();
        let e = e.unwrap_or(false);

        pseudo!([
            dd:f64;
            let conditional:u1 = IsNan(dd);
            if(e) {
                Ite(conditional != false,
                    {
                        Abort("Invalid Operation exception");
                    },
                    {}
                );
            }

            let is_zero = dd == 0.0f64;
            let less_than_zero = dd < 0.0f64;
            let greater_than_zero =  dd > 0.0f64;

            let c = is_zero | greater_than_zero;
            let ncondition = !conditional;

            Flag("FPSCR.N") = less_than_zero & ncondition;
            Flag("FPSCR.Z") = is_zero & ncondition;
            Flag("FPSCR.C") = c | conditional;
            Flag("FPSCR.V") = false | conditional;
        ])
    }
}

impl Decode for VcmpF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        // Default fpscr.
        // 00000’ : FPSCR<26> : ‘11000000000000000000000000
        let Self { e, dd, dm } = self;
        let e = e.unwrap_or(false);
        let dd = dd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dd:f64;
            dm:f64;
            let conditional:u1 = IsNan(dd) | IsNan(dm);

            if (e) {
                Ite(conditional != false,
                    {
                        Abort("Invalid Operation exception");
                    },
                    {}
                );
            }

            let is_zero = dd == dm;
            let less_than_zero = dd < dm;
            let greater_than_zero =  dd > dm;

            let c = is_zero | greater_than_zero;

            let ncondition = !conditional;

            Flag("FPSCR.N") = less_than_zero & ncondition;
            Flag("FPSCR.Z") = is_zero & ncondition;
            Flag("FPSCR.C") = c | conditional;
            Flag("FPSCR.V") = false | conditional;
        ])
    }
}

impl Decode for VrintF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { r, sd, sm } = self;
        let r = r.unwrap_or(false);
        let sd = sd.local_into();
        let sm = sm.local_into();
        pseudo!([
            sm:f32;
            let destination:u32 = 0.local_into();

            if (r) {
                destination = Resize(sm,u32,ToZero);
            } else {
                destination = Resize(sm,u32);
            }

            sd = Cast(destination,f32);
        ])
    }
}

impl Decode for VrintF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { r, dd, dm } = self;
        let r = r.unwrap_or(false);
        let dd = dd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dm:f64;
            let destination:u64 = 0.local_into();

            if (r) {
                destination = Resize(dm,u64,ToZero);
            } else {
                destination = Resize(dm,u64);
            }

            dd = Cast(destination,f64);
        ])
    }
}

impl Decode for Vcvt {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { r, dest, sm, fbits } = self;
        let r = r.unwrap_or(false);
        let round_to_zero: u32 = IEEE754RoundingMode::RZ.to_u32();
        let round_to_zero = round_to_zero.local_into();

        // TODO: Change this to actual R value.
        let base = (2.0f64).powi(fbits.unwrap_or(0) as i32);
        match (dest, sm) {
            (ConversionArgument::F32(f), ConversionArgument::I32(i)) => {
                let i = i.local_into();
                let f = f.local_into();
                let base = (base, OperandType::Binary32).local_into();

                pseudo!([
                    let old_rm = Register("FPSCR.RM");
                    if (r) {
                        Register("FPSCR.RM") = round_to_zero;
                    }
                    f:f32; i:f32; base:f32;
                    let i_signed = Cast(i,i32);
                    Warn("vcvt from i signed to f32",i_signed);
                    let i2 = Resize(i_signed, f32);
                    f = i2/base;
                    if (r) {
                        Register("FPSCR.RM") = old_rm;
                    }
                ])
            }
            (ConversionArgument::F32(f), ConversionArgument::U32(u)) => {
                let u = u.local_into();
                let f = f.local_into();
                let base = (base, OperandType::Binary32).local_into();

                pseudo!([
                    f:f32; u:f32; base:f32;
                    let old_rm = Register("FPSCR.RM");
                    if (r) {
                        Register("FPSCR.RM") = round_to_zero;
                    }
                    let u_unsigned = Cast(u,u32);
                    Warn("vcvt to u",u_unsigned);
                    let u2 = Resize(u_unsigned, f32);
                    f = u2/base;
                    if (r) {
                        Register("FPSCR.RM") = old_rm;
                    }
                ])
            }
            (ConversionArgument::I32(i), ConversionArgument::F32(f)) => {
                let f = f.local_into();
                let i = i.local_into();
                let base = (base, OperandType::Binary32).local_into();
                pseudo!([
                    f:f32; i:f32; base:f32;

                    let old_rm = Register("FPSCR.RM");
                    if (r) {
                        Register("FPSCR.RM") = round_to_zero;
                    }
                    let val = f*base;
                    let rounded:i32 = Resize(val,i32,ToZero);
                    // let rounded_f32:f32 = Resize(rounded,f32);
                    // let err:f32 = val - rounded_f32;
                    // let round_up:u1 = false;
                    // // Intermediates used in ite blocks.
                    // let cond = false;
                    // let cond2 = false;
                    // let cond3 = false;
                    // Register("FPSCR.RM") = 0b01u32;
                    // Ite(Register("FPSCR.RM") == 0b00u32,
                    //     {
                    //         cond:u1 = err > 0.5f32;
                    //         cond2:u1 = err == 0.5f32;
                    //         let intermediate_val:u32 = Resize(rounded<0:0>,u32);
                    //         cond3:u1 = Resize(intermediate_val,u1);
                    //         cond2 = cond2 & cond3;
                    //         cond |= cond2;
                    //         round_up = cond;
                    //     },
                    //     {}
                    // );
                    // Ite(Register("FPSCR.RM") == 0b01u32,
                    //     {
                    //         cond:u1 = err != 0.0f32;
                    //         round_up = cond;
                    //     },
                    //     {}
                    // );
                    // // 0b10 is already handled by setting round up to false.
                    // Ite(Register("FPSCR.RM") == 0b11u32,
                    //     {
                    //         cond:u1 =  err != 0.0f32;
                    //         cond2:u1 =  rounded < 0i32;
                    //         cond &= cond2;
                    //         round_up = cond;
                    //     },
                    //     {}
                    // );
                    // Ite(round_up != false,
                    //     {
                    //         rounded += 1i32;
                    //     },
                    //     {}
                    // );
                    Warn("vcvt to i",rounded);
                    i = Cast(rounded,f32);
                    if (r) {
                        Register("FPSCR.RM") = old_rm;
                    }
                ])
            }
            (ConversionArgument::U32(u), ConversionArgument::F32(f)) => {
                let f = f.local_into();
                let u = u.local_into();
                let base = (base, OperandType::Binary32).local_into();
                pseudo!([
                    f:f32; u:f32; base:f32;
                    let old_rm = Register("FPSCR.RM");
                    if (r) {
                        Register("FPSCR.RM") = round_to_zero;
                    }
                    let val = f*base;
                    let rounded:u32 = Resize(val,u32,ToZero);
                    // let rounded_f32:f32 = Resize(rounded,f32);
                    // let err:f32 = val - rounded_f32;
                    // let round_up:u1 = false;
                    // // Intermediates used in ite blocks.
                    // let cond = false;
                    // let cond2 = false;
                    // let cond3 = false;
                    // Ite(Register("FPSCR.RM") == 0b00u32,
                    //     {
                    //         cond:u1 =  err > 0.5f32;
                    //         cond2:u1 =  err == 0.5f32;
                    //         let intermediate_val:u32 = Resize(rounded<0:0>,u32);
                    //         cond3:u1 = Resize(intermediate_val,u1);
                    //         cond2 = cond2 & cond3;
                    //         cond |= cond2;
                    //         round_up = cond;
                    //     },
                    //     {}
                    // );
                    // Ite(Register("FPSCR.RM") == 0b01u32,
                    //     {
                    //         cond:u1 = err != 0.0f32;
                    //         round_up = cond;
                    //     },
                    //     {}
                    // );
                    // // 0b10 is already handled by setting round up to false.
                    // Ite(Register("FPSCR.RM") == 0b11u32,
                    //     {
                    //         cond:u1 =  err != 0.0f32;
                    //         cond2:u1 =  rounded < 0u32;
                    //         cond &= cond2;
                    //         round_up = cond;
                    //     },
                    //     {}
                    // );
                    // Ite(round_up != false,
                    //     {
                    //         rounded += 1u32;
                    //     },
                    //     {}
                    // );
                    u = Cast(rounded,f32);
                    if (r) {
                        Register("FPSCR.RM") = old_rm;
                    }
                ])
            }
            _ => todo!(),
        }
    }
}

impl Decode for VcvtF32F64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { sd, dm } = self;
        let sd = sd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dm:f64;
            sd:f32;
            dm = Resize(sd,f64);
        ])
    }
}

impl Decode for VcvtF64F32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { dd, sm } = self;
        let dd = dd.local_into();
        let sm = sm.local_into();
        pseudo!([
            sm:f32;
            dd:f64;
            sm = Resize(dd,f32);
        ])
    }
}

impl Decode for VrintCustomRoundingF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { r, sd, sm } = self;
        let r = r.local_into();
        let sd = sd.local_into();
        let sm = sm.local_into();
        pseudo!([
            sm:f32;
            let result:u32 = Resize(sm,u32,r);
            sd = Cast(result,f32);
        ])
    }
}

impl Decode for VrintCustomRoundingF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { r, dd, dm } = self;
        let r = r.local_into();
        let dd = dd.local_into();
        let dm = dm.local_into();
        pseudo!([
            dm:f64;
            dd:f64;
            let result:u64 = Resize(dm,u64,r);
            dd = Cast(result,f64);
        ])
    }
}

impl Decode for VcvtCustomRoundingIntF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { r, sd, sm } = self;
        let r = r.local_into();
        let sd_inner = sd.clone().local_into();
        let sm = sm.local_into();
        pseudo!([
            sm:f32;
            sd_inner:f32;

            if (let IntType::U32(_reg) = sd) {
                let result:u32 = Resize(sm,u32,r);
                sd_inner = Cast(result,f32);
            } else {
                let result:i32 = Resize(sm,i32,r);
                sd_inner = Cast(result,f32);
            }
        ])
    }
}

impl Decode for VcvtCustomRoundingIntF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { r, sd, dm } = self;
        let r = r.local_into();
        let sd_inner = sd.clone().local_into();
        let dm = dm.local_into();
        pseudo!([
            dm:f64;
            sd_inner:f32;

            if (let IntType::U32(_reg) = sd) {
                let result:u32 = Resize(dm,u32,r);
                sd_inner = Cast(result,f32);
            } else {
                let result:i32 = Resize(dm,i32,r);
                sd_inner = Cast(result,f32);
            }
        ])
    }
}

// NOTE: We might want to take endianness in to account here.

impl Decode for VStmF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, wback, imm32, rn, registers } = self;
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        let rn = rn.local_into();
        let imm32 = imm32.local_into();
        pseudo!([
            rn:u32;
            let address:u32 = rn;
            if(*add) {
                address += imm32;
            } else {
                address -= imm32;
            }
            if (*wback) {
                if (*add){
                    rn = rn + imm32;
                }else {
                    rn = rn-imm32;
                }
            }

            for register in registers.into_iter() {
                register:f32;
                LocalAddress(address,32) = Cast(register, u32);
                address += 4.local_into();
            }
        ])
    }
}

impl Decode for VStmF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, wback, imm32, rn, registers } = self;
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        let rn = rn.local_into();
        let imm32 = imm32.local_into();
        pseudo!([
            rn:u32;
            let address:u32 = rn;
            if(*add) {
                address += imm32;
            } else {
                address -= imm32;
            }
            if (*wback) {
                if (*add){
                    rn = rn + imm32;
                }else {
                    rn = rn-imm32;
                }
            }

            for register in registers.into_iter() {
                register:f64;
                LocalAddress(address,64) = Cast(register, u64);
                address += 8.local_into();
            }
        ])
    }
}

impl Decode for VStrF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, imm32, rn, sd } = self;
        let imm32 = imm32.local_into();
        let rn = rn.local_into();
        let sd = sd.local_into();
        pseudo!([
            rn:u32;
            sd:f32;
            let address = rn;
            if (*add) {
                address+=imm32;
            } else {
                address-=imm32;
            }

            LocalAddress(address,32) = Cast(sd,u32);
        ])
    }
}

impl Decode for VStrF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, imm32, rn, dd } = self;
        let imm32 = imm32.local_into();
        let rn = rn.local_into();
        let dd = dd.local_into();
        pseudo!([
            rn:u32;
            dd:f64;
            let address = rn;
            if (*add) {
                address+=imm32;
            } else {
                address-=imm32;
            }

            LocalAddress(address,64) = Cast(dd,u64);
        ])
    }
}

impl Decode for VPushF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { imm32, registers } = self;
        let imm32 = imm32.local_into();
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        pseudo!([
            let address:u32 = Register("SP&") - imm32;
            Register("SP&") = Register("SP&") - imm32;
            for register in registers.into_iter() {
                register:f32;
                LocalAddress(address,32) = Cast(register,u32);
                address += 4.local_into();
            }
        ])
    }
}

impl Decode for VPushF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { imm32, registers } = self;
        let imm32 = imm32.local_into();
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        pseudo!([
            let address:u32 = Register("SP&") - imm32;
            Register("SP&") = Register("SP&") - imm32;
            for register in registers.into_iter() {
                register:f64;
                let intermediate:u64 = Cast(register,u64);
                LocalAddress(address,32) = intermediate<63:32>;
                address += 4.local_into();
                LocalAddress(address,32) = intermediate<31:0>;
                address += 4.local_into();
            }
        ])
    }
}

impl Decode for VLdrF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, imm32, rn, sd } = self;
        let is_pc = *rn == Register::PC;
        let imm32 = imm32.local_into();
        let rn = rn.local_into();
        let sd = sd.local_into();
        pseudo!([
            rn:u32;
            sd:f32;
            let base = rn;
            if (is_pc) {
                base = Register("PC+");
                base = Resize(base<31:2>,u32) << 2u32;
            }
            let address = base;
            if (*add) {
                address += imm32;
            }
            else {
                address -= imm32;
            }
            let val:u32 = LocalAddress(address,32);
            sd = Cast(val,f32);
        ])
    }
}

impl Decode for VLdrF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, imm32, rn, dd } = self;
        let is_pc = *rn == Register::PC;
        let imm32 = imm32.local_into();
        let rn = rn.local_into();
        let dd = dd.local_into();
        pseudo!([
            rn:u32;
            sd:f64;
            let base = rn;
            if (is_pc) {
                base = Register("PC+");
                base = Resize(base<31:2>,u32) << 2u32;
            }
            let address = base;
            if (*add) {
                address += imm32;
            }
            else {
                address -= imm32;
            }
            let val:u64 = LocalAddress(address,64);
            dd = Cast(val,f64);
        ])
    }
}

impl Decode for VPopF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { imm32, registers } = self;
        let imm32 = imm32.local_into();
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        pseudo!([
            let address:u32 = Register("SP&");
            for register in registers.into_iter() {
                let value = LocalAddress(address,32);
                register:f32 = Cast(value,f32);
                address += 4.local_into();
            }
            Register("SP&") = address + imm32;
        ])
    }
}

impl Decode for VPopF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { imm32, registers } = self;
        let imm32 = imm32.local_into();
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        pseudo!([
            let address:u32 = Register("SP&");
            for register in registers.into_iter() {
                let value = LocalAddress(address,64);
                register:f64 = Cast(value,f64);
                address += 8.local_into();
            }
            Register("SP&") = Register("SP&") + imm32;
        ])
    }
}

impl Decode for VLdmF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, wback, imm32, rn, registers } = self;
        let imm32 = imm32.local_into();
        let rn = rn.local_into();
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        pseudo!([
            rn:u32; imm32:u32;

            let address = rn;
            if(*add) {
                address -= imm32;
            }

            if(*wback)  {
                if(*add) {
                    rn+=imm32;
                } else  {
                    rn-=imm32;
                }
            }
            for register in registers.iter() {
                register:f32;
                let value:u32 = LocalAddress(address,32);
                address += 4.local_into();
                register = Cast(value,f32);
            }
        ])
    }
}

impl Decode for VLdmF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { add, wback, imm32, rn, registers } = self;
        let imm32 = imm32.local_into();
        let rn = rn.local_into();
        let registers: Vec<_> = registers.iter().map(|el| el.local_into()).collect();
        pseudo!([
            rn:u32; imm32:u32;

            let address = rn;
            if(*add) {
                address -= imm32;
            }

            if(*wback)  {
                if(*add) {
                    rn+=imm32;
                } else  {
                    rn-=imm32;
                }
            }
            for register in registers.iter() {
                register:f64;
                let value:u64 = LocalAddress(address,64);
                address += 8.local_into();
                register = Cast(value,f64);
            }
        ])
    }
}

impl Decode for VmoveF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { to_core, sn, rt } = self;
        let sn = sn.local_into();
        let rt = rt.local_into();

        pseudo!([
            sn:f32;rt:u32;

            if(*to_core) {
                rt = Cast(sn,u32);
            } else {
                sn = Cast(rt,f32);
            }
        ])
    }
}

impl Decode for VmoveF64 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { to_core, rt, rt2, dm } = self;
        let dm = dm.local_into();
        let rt = rt.local_into();
        let rt2 = rt2.local_into();
        println!("RT : {rt:?}");
        println!("RT2 : {rt2:?}");

        pseudo!([
            dm:f64;rt:u32;rt2:u32;

            if(*to_core) {
                let value:u64 = Cast(dm,u64);
                rt =  value<63:32:u64>;
                rt2 = value<31:0:u64>;
            } else {
                let value:u64 = Resize(rt,u64);
                let intermediate = Resize(rt2,u64) << 32u64;
                value |= intermediate;
                dm = Cast(value,f64);
            }
        ])
    }
}

impl Decode for VmoveDoubleF32 {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { to_core, rt, rt2, sm, sm1 } = self;
        let rt = rt.local_into();
        let rt2 = rt2.local_into();
        let sm = sm.local_into();
        let sm1 = sm1.local_into();
        pseudo!([
            sm:f32;sm1:f32;rt:u32;rt2:u32;
            if (*to_core) {
                rt = Cast(sm,u32);
                rt2 = Cast(sm1,u32);
            } else {
                sm = Cast(rt,f32);
                sm1 = Cast(rt2,f32);
            }
        ])
    }
}

impl Decode for Vmrs {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { rt } = self;
        match rt {
            RegisterOrAPSR::APSR => pseudo!([
                Flag("APSR.N") = Flag("FPSCR.N");
                Flag("APSR.Z") = Flag("FPSCR.Z");
                Flag("APSR.C") = Flag("FPSCR.C");
                Flag("APSR.V") = Flag("FPSCR.V");
            ]),
            RegisterOrAPSR::Register(r) => {
                let r = r.local_into();
                pseudo!([
                    r:u32 = Register("FPSCR");
                ])
            }
        }
    }
}

impl Decode for Vmsr {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Self { rt } = self;
        let rt = rt.local_into();
        pseudo!([
            Register("FPSCR") = rt;
        ])
    }
}

impl super::sealed::Into<Operand> for F32OrF64 {
    fn local_into(self) -> Operand {
        match self {
            F32OrF64::F32(f) => f.local_into(),
            F32OrF64::F64(f) => f.local_into(),
        }
    }
}
impl super::sealed::Into<Operand> for disarmv7::arch::register::F32Register {
    fn local_into(self) -> Operand {
        Operand {
            ty: OperandType::Binary32,
            value: OperandStorage::Register {
                id: self.name(),
                ty: OperandType::Binary32,
            },
        }
    }
}

impl super::sealed::Into<Operand> for disarmv7::arch::register::F64Register {
    fn local_into(self) -> Operand {
        Operand {
            ty: OperandType::Binary64,
            value: OperandStorage::Register {
                id: self.name(),
                ty: OperandType::Binary64,
            },
        }
    }
}

impl super::sealed::Into<ComparisonMode> for Condition {
    fn local_into(self) -> ComparisonMode {
        match self {
            Self::Eq => ComparisonMode::Equal,
            Self::Ne => ComparisonMode::NotEqual,
            Self::Lt => ComparisonMode::Less,
            Self::Le => ComparisonMode::LessOrEqual,
            Self::Gt => ComparisonMode::Greater,
            Self::Ge => ComparisonMode::GreaterOrEqual,
            _ => todo!(),
        }
    }
}
struct Wrappedu64(u64);
struct Wrappedu32(u32);

impl super::sealed::Into<Operand> for Wrappedu64 {
    fn local_into(self) -> Operand {
        let val_ptr: *const u64 = (&self.0) as *const u64;
        Operand {
            ty: OperandType::Binary64,
            value: OperandStorage::Immediate {
                value: unsafe { core::ptr::read(val_ptr as *const f64) },
                ty: OperandType::Binary64,
            },
        }
    }
}

impl super::sealed::Into<Operand> for Wrappedu32 {
    fn local_into(self) -> Operand {
        let val_ptr: *const u32 = (&self.0) as *const u32;
        let value = unsafe { core::ptr::read(val_ptr as *const f32) } as f64;

        Operand {
            ty: OperandType::Binary32,
            value: OperandStorage::Immediate { value, ty: OperandType::Binary32 },
        }
    }
}

impl super::sealed::Into<Operand> for (f64, OperandType) {
    fn local_into(self) -> Operand {
        Operand {
            ty: self.1.clone(),
            value: OperandStorage::Immediate {
                value: self.0,
                ty: self.1.clone(),
            },
        }
    }
}
impl super::sealed::Into<RoundingMode> for IEEE754RoundingMode {
    fn local_into(self) -> RoundingMode {
        match self {
            Self::RN => RoundingMode::TiesToEven,
            Self::RP => RoundingMode::TiesTowardPositive,
            Self::RM => RoundingMode::TiesTowardNegative,
            Self::RZ => RoundingMode::TiesTowardZero,
        }
    }
}

impl super::sealed::Into<Operand> for IntType {
    fn local_into(self) -> Operand {
        match self {
            Self::U32(f) => f.local_into(),
            Self::I32(f) => f.local_into(),
        }
    }
}
