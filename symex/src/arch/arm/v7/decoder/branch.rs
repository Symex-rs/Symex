use disarmv7::operation::Tb;
use transpiler::pseudo;

use super::{sealed::Into, Decode, REMOVE_LAST_BIT_MASK};

impl Decode for Tb {
    fn decode(&self, _in_it_block: bool) -> Vec<general_assembly::prelude::Operation> {
        let Tb { is_tbh, rn, rm } = self;
        let rn = rn.local_into();
        let rm = rm.local_into();
        let is_tbh = is_tbh.unwrap_or(false);

        pseudo!([
            rm:u32;
            rn:u32;

            let halfwords:u32 = 0.local_into();

            if (is_tbh) {
                let address:u32 = rm << 1.local_into();
                address = address + rn;
                halfwords = ZeroExtend(LocalAddress(address,16),32);
            } else {
                let address = rn + rm;
                halfwords = ZeroExtend(LocalAddress(address,8),32);
            }
            let target = halfwords*2.local_into();
            target = target + Register("PC+");
            target = target & REMOVE_LAST_BIT_MASK.local_into();
            Jump(target);
        ])
    }
}
