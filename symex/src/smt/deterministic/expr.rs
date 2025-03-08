#![allow(clippy::len_without_is_empty)]
use std::rc::Rc;

use bitwuzla::{Btor, BV};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitwuzlaExpr(pub(crate) BV<Rc<Btor>>);

//impl BitwuzlaExpr {
//    fn unbounded(bv: BV<Rc<Btor>>) {
//        BV::new(btor, width, symbol)
//    }
//}
//
impl BitwuzlaExpr {
    pub fn get_ctx(&self) -> Rc<Btor> {
        let ctx = self.0.get_btor();
        ctx
    }

    /// Shift left logical
    pub fn sll(&self, other: &Self) -> Self {
        Self(self.0.sll(&other.0))
    }

    /// Shift right logical
    pub fn srl(&self, other: &Self) -> Self {
        Self(self.0.srl(&other.0))
    }

    /// Shift right arithmetic
    pub fn sra(&self, other: &Self) -> Self {
        Self(self.0.sra(&other.0))
    }
}
