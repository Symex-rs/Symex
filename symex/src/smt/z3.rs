use std::{
    ffi::CStr,
    marker::PhantomData,
    pin::Pin,
    sync::{atomic::AtomicU64, Arc, Mutex},
};

use anyhow::Context;
use general_assembly::extension::ieee754::{OperandType, RoundingMode};
use hashbrown::HashMap;
use z3_sys::{Z3_get_numeral_uint64, Z3_mk_fpa_fma, Z3_mk_fpa_mul, Z3_L_TRUE};

use super::{MemoryError, ProgramMemory, SmtExpr, SmtFPExpr, SmtMap, SmtSolver};
use crate::{defaults::z3, executor::ResultOrTerminate, memory::BITS_IN_BYTE, project::Project, Endianness, UserStateContainer};

#[derive(Debug)]
pub struct Z3Context {
    ctx: Pin<Arc<z3_sys::Z3_context>>,
    solver: Pin<Arc<z3_sys::Z3_solver>>,
    counter: Pin<Arc<AtomicU64>>,
}

impl PartialEq for Z3Context {
    fn eq(&self, other: &Self) -> bool {
        self.ctx == other.ctx && self.solver == other.solver && self.counter.load(std::sync::atomic::Ordering::Relaxed) == other.counter.load(std::sync::atomic::Ordering::Relaxed)
    }
}

impl Z3Context {
    pub fn un_named(&mut self) -> String {
        let mut counter = self.counter.load(std::sync::atomic::Ordering::Relaxed);
        counter += 1;
        self.counter.store(counter, std::sync::atomic::Ordering::Relaxed);
        let name = format!("unnamed_{}", counter);
        println!("Unnamed {name}");
        name
    }
}

impl std::clone::Clone for Z3Context {
    fn clone(&self) -> Self {
        Self {
            ctx: Pin::clone(&self.ctx),
            counter: Pin::clone(&self.counter),
            solver: Pin::clone(&self.solver),
        }
    }
}
#[derive(Clone, Debug)]
pub struct Z3Array<UserState: UserStateContainer> {
    pub ram: ArrayMemory,

    register_file: HashMap<String, Z3Bv>,
    flags: HashMap<String, Z3Bv>,
    variables: HashMap<String, Z3Bv>,
    fp_variables: HashMap<String, Z3Fp>,
    program_memory: &'static Project,
    word_size: u32,
    pc: u64,
    initial_sp: Z3Bv,
    static_writes: HashMap<u64, Z3Bv>,
    privelege_map: Vec<(u64, u64)>,
    cycles: u64,
    _0: PhantomData<UserState>,
}

impl<UserState: UserStateContainer> SmtMap for Z3Array<UserState> {
    type Expression = Z3Bv;
    type ProgramMemory = &'static Project;
    type SMT = Z3Solver;
    type StateContainer = UserState;

    fn new(
        smt: Self::SMT,
        program_memory: &'static Project,
        word_size: u32,
        endianness: Endianness,
        initial_sp: Self::Expression,
        _state: &Self::StateContainer,
    ) -> Result<Self, crate::GAError> {
        let ram = { ArrayMemory::new(smt.ctx.clone(), word_size, endianness) };
        Ok(Self {
            ram,
            register_file: HashMap::new(),
            flags: HashMap::new(),
            variables: HashMap::new(),
            fp_variables: HashMap::new(),
            program_memory,
            word_size,
            pc: 0,
            initial_sp,
            static_writes: HashMap::new(),
            privelege_map: Vec::new(),
            cycles: 0,
            _0: PhantomData,
        })
    }

    fn get(&mut self, idx: &Self::Expression, size: u32) -> ResultOrTerminate<Self::Expression> {
        if let Some(address) = idx.get_constant() {
            if !self.program_memory.address_in_range(address) {
                return ResultOrTerminate::Result(
                    self.ram
                        .read(idx, size as u32)
                        .context("While reading from a non constant address pointing in to the symbols memory"),
                );
            }
            return ResultOrTerminate::Result(
                self.program_memory
                    .get(address, size as u32, &self.static_writes, &self.ram)
                    .context("While reading from progam memory"),
            );
            /* DataWord::Word8(value) => self.from_u64(value.into(), 8),
             * DataWord::Word16(value) => self.from_u64(value.into(), 16),
             * DataWord::Word32(value) => self.from_u64(value.into(), 32),
             * DataWord::Word64(value) => self.from_u64(value, 32),
             * DataWord::Bit(value) => self.from_u64(value.into(), 1), */
        }
        ResultOrTerminate::Result(
            self.ram
                .read(idx, size as u32)
                .context("While reading from a non constant address pointing to symbolic memory"),
        )
    }

    fn set(&mut self, idx: &Self::Expression, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        if let Some(address) = idx.get_constant() {
            if self.program_memory.address_in_range(address) {
                assert!(value.size() % 8 == 0, "Value must be a multiple of 8 bits to be written to program memory");
                self.program_memory.set(
                    address,
                    value,
                    // match value.len() / 8 {
                    //     1 => DataWord::Word8((const_value & u8::MAX as u64) as u8),
                    //     2 => DataWord::Word16((const_value & u16::MAX as u64) as u16),
                    //     4 => DataWord::Word32((const_value & u32::MAX as u64) as u32),
                    //     8 => DataWord::Word64(const_value),
                    //     _ => unimplemented!("Unsupported bitwidth"),
                    // },
                    &mut self.static_writes,
                    &mut self.ram,
                );
                return Ok(());
                //Return Ok(self.program_memory.set(address, value)?);
            }
            // todo!("Handle non static program memory writes");
        }
        Ok(self.ram.write(idx, value)?)
    }

    fn get_pc(&self) -> Result<Self::Expression, crate::smt::MemoryError> {
        let ret = self.from_u64(self.pc, self.word_size);
        Ok(ret)
    }

    fn set_pc(&mut self, value: u32) -> Result<(), crate::smt::MemoryError> {
        self.pc = value.into();
        Ok(())
    }

    fn set_flag(&mut self, idx: &str, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        self.flags.insert(idx.to_string(), value);
        Ok(())
    }

    fn get_flag(&mut self, idx: &str) -> Result<Self::Expression, crate::smt::MemoryError> {
        let ret = match self.flags.get(idx) {
            Some(val) => val.clone(),
            _ => {
                let ret = self.unconstrained(idx, 1);
                self.flags.insert(idx.to_owned(), ret.clone());
                ret
            }
        };
        if self.variables.get(idx).is_none() {
            self.variables.insert(idx.to_owned(), ret.clone());
        }
        Ok(ret)
    }

    fn set_register(&mut self, idx: &str, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        if idx == "PC" {
            return self.set_pc(match value.get_constant() {
                Some(val) => val as u32,
                None => return Err(crate::smt::MemoryError::PcNonDetmerinistic),
            });
        }
        let value = value.simplify();
        self.register_file.insert(idx.to_string(), value);
        Ok(())
    }

    fn get_register(&mut self, idx: &str) -> Result<Self::Expression, crate::smt::MemoryError> {
        if idx == "PC" {
            return self.get_pc();
        }
        let ret = match self.register_file.get(idx) {
            Some(val) => val.clone(),
            None => {
                let ret = self.unconstrained(idx, self.word_size);
                self.register_file.insert(idx.to_owned(), ret.clone());
                ret
            }
        };
        if self.variables.get(idx).is_none() {
            self.variables.insert(idx.to_owned(), ret.clone());
        }
        // Ensure that any read from the same register returns the
        //self.register_file.get(idx);
        Ok(ret)
    }

    fn from_u64(&self, value: u64, size: u32) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width value");
        Z3Bv::_from_u64(self.ram.ctx.clone(), value & ((1u128 << size) - 1) as u64, size)
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        Z3Bv::from_bool(self.ram.ctx.clone(), value)
    }

    fn unconstrained(&mut self, name: &str, size: u32) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width unconstrained value");
        let ret = Z3Bv::unconstrained(self.ram.ctx.clone(), size, Some(name.to_string()));
        ret.resize_unsigned(size as u32);
        if !self.variables.contains_key(name) {
            self.variables.insert(name.to_string(), ret.clone());
        }
        ret
    }

    fn unconstrained_unnamed(&mut self, size: u32) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width unconstrained value");
        let ret = Z3Bv::unconstrained(self.ram.ctx.clone(), size, None);
        ret.resize_unsigned(size as u32);
        ret
    }

    fn unconstrained_fp_unnamed(&mut self, ty: general_assembly::extension::ieee754::OperandType) -> <Self::SMT as crate::smt::SmtSolver>::FpExpression {
        let expr = Z3Fp::unconstrained(self.ram.ctx.clone(), ty, None);
        expr
    }

    fn unconstrained_fp(&mut self, ty: general_assembly::extension::ieee754::OperandType, name: &str) -> <Self::SMT as crate::smt::SmtSolver>::FpExpression {
        let expr = Z3Fp::unconstrained(self.ram.ctx.clone(), ty, None);
        if !self.fp_variables.contains_key(name) {
            self.fp_variables.insert(name.to_string(), expr.clone());
        }
        expr
    }

    fn get_ptr_size(&self) -> u32 {
        self.program_memory.get_ptr_size()
    }

    fn get_from_instruction_memory(&self, address: u64) -> crate::Result<Vec<u8>> {
        Ok(self.program_memory.get_raw_word(address)?)
    }

    fn get_stack(&mut self) -> (Self::Expression, Self::Expression) {
        // TODO: Make this more generic.
        (self.initial_sp.clone(), self.register_file.get("SP").expect("Could not get register SP").clone())
    }

    fn clear_named_variables(&mut self) {
        self.variables.clear();
    }

    fn program_memory(&self) -> &Self::ProgramMemory {
        &self.program_memory
    }

    fn is_sat(&self) -> bool {
        unsafe { z3_sys::Z3_solver_check(*self.ram.ctx.ctx, *self.ram.ctx.solver) == Z3_L_TRUE }
    }

    fn with_model_gen<R, F: FnOnce() -> R>(&self, f: F) -> R {
        f()
    }

    fn get_cycle_count(&mut self) -> u64 {
        self.cycles
    }

    fn set_cycle_count(&mut self, value: u64) {
        self.cycles = value
    }

    fn get_registers(&mut self) -> HashMap<String, Self::Expression> {
        self.register_file.clone()
    }
}

impl super::Context for ArrayMemory {
    type Expr = Z3Bv;

    fn new_from_u64(&self, val: u64, bits: u32) -> Self::Expr {
        Z3Bv::_from_u64(self.ctx.clone(), val, bits)
    }
}

#[derive(Debug, Clone)]
pub struct ArrayMemory {
    term: z3_sys::Z3_ast,
    pub ctx: Z3Context,

    /// Size of a pointer.
    ptr_size: u32,
    word_size: u32,

    /// Memory endianness
    endianness: Endianness,
}

impl ArrayMemory {
    pub fn resolve_addresses(&self, addr: &Z3Bv, _upper_bound: u32) -> Result<Vec<Z3Bv>, MemoryError> {
        Ok(vec![addr.clone()])
    }

    pub fn read(&self, addr: &Z3Bv, bits: u32) -> Result<Z3Bv, MemoryError> {
        assert_eq!(addr.size(), self.ptr_size, "passed wrong sized address");

        let value = self.internal_read(addr, bits, self.ptr_size)?;
        Ok(value)
    }

    pub fn write(&mut self, addr: &Z3Bv, value: Z3Bv) -> Result<(), MemoryError> {
        assert_eq!(addr.size(), self.ptr_size, "passed wrong sized address");
        self.internal_write(addr, value, self.ptr_size)
    }

    /// Creates a new memory containing only uninitialized memory.
    pub fn new(ctx: Z3Context, ptr_size: u32, endianness: Endianness) -> Self {
        let mode = unsafe { z3_sys::Z3_mk_bv_sort(*ctx.ctx, ptr_size) };
        let data_width = Z3Bv::_from_u64(ctx.clone(), 0, 8);

        let term = unsafe { z3_sys::Z3_mk_const_array(*ctx.ctx, mode, data_width.term) };
        unsafe { z3_sys::Z3_inc_ref(*ctx.ctx, term) };
        unsafe { z3_sys::Z3_inc_ref(*ctx.ctx, data_width.term) };

        Self {
            ctx,
            ptr_size,
            word_size: ptr_size,
            term,
            endianness,
        }
    }

    /// Reads an u8 from the given address.
    fn read_u8(&self, addr: &Z3Bv) -> Z3Bv {
        let term = unsafe { z3_sys::Z3_mk_select(*self.ctx.ctx, self.term, addr.term) };
        Z3Bv { term, ctx: self.ctx.clone() }
    }

    /// Writes an u8 value to the given address.
    fn write_u8(&mut self, addr: &Z3Bv, val: Z3Bv) {
        self.term = unsafe { z3_sys::Z3_mk_store(*self.ctx.ctx, self.term, addr.term, val.term) };
    }

    /// Reads `bits` from `addr.
    ///
    /// If the number of bits are less than `BITS_IN_BYTE` then individual bits
    /// can be read, but if the number of bits exceed `BITS_IN_BYTE` then
    /// full bytes must be read.
    fn internal_read(&self, addr: &Z3Bv, bits: u32, ptr_size: u32) -> Result<Z3Bv, MemoryError> {
        let value = if bits < BITS_IN_BYTE {
            self.read_u8(addr).slice(0, bits - 1)
        } else {
            // Ensure we only read full bytes now.
            assert_eq!(bits % BITS_IN_BYTE, 0, "Must read bytes, if bits >= 8");
            let num_bytes = bits / BITS_IN_BYTE;

            let mut bytes = Vec::new();

            for byte in 0..num_bytes {
                let offset = Z3Bv::_from_u64(self.ctx.clone(), byte as u64, ptr_size);
                let read_addr = addr.add(&offset);
                let value = self.read_u8(&read_addr);
                bytes.push(value);
            }

            match self.endianness {
                Endianness::Little => bytes.into_iter().reduce(|acc, v| v.concat(&acc)).unwrap(),
                Endianness::Big => bytes.into_iter().rev().reduce(|acc, v| v.concat(&acc)).unwrap(),
            }
        };

        Ok(value)
    }

    fn internal_write(&mut self, addr: &Z3Bv, value: Z3Bv, ptr_size: u32) -> Result<(), MemoryError> {
        // Check if we should zero extend the value (if it less than 8-bits).
        let value = if value.size() < BITS_IN_BYTE { value.zero_ext(BITS_IN_BYTE) } else { value };

        // Ensure the value we write is a multiple of `BITS_IN_BYTE`.
        assert_eq!(value.size() % BITS_IN_BYTE, 0);

        let num_bytes = value.size() / BITS_IN_BYTE;
        for n in 0..num_bytes {
            let low_bit = n * BITS_IN_BYTE;
            let high_bit = (n + 1) * BITS_IN_BYTE - 1;
            assert!(high_bit >= low_bit);
            let byte = value.slice(low_bit, high_bit);

            let offset = match self.endianness {
                Endianness::Little => Z3Bv::_from_u64(self.ctx.clone(), n as u64, ptr_size),
                Endianness::Big => Z3Bv::_from_u64(self.ctx.clone(), (num_bytes - 1 - n) as u64, ptr_size),
            };
            let addr = addr.add(&offset);
            self.write_u8(&addr, byte);
        }

        Ok(())
    }
}

#[derive(Clone)]
pub struct Z3Fp {
    term: z3_sys::Z3_ast,
    ctx: Z3Context,
    ty: super::OperandType,
}

impl Z3Fp {
    fn conv(&self, rm: general_assembly::extension::ieee754::RoundingMode) -> z3_sys::Z3_ast {
        unsafe {
            match rm {
                RoundingMode::Exact => unimplemented!(),
                RoundingMode::TiesToEven => z3_sys::Z3_mk_fpa_round_nearest_ties_to_even(*self.ctx.ctx),
                RoundingMode::TiesToAway => z3_sys::Z3_mk_fpa_round_nearest_ties_to_away(*self.ctx.ctx),
                RoundingMode::TiesTowardZero => z3_sys::Z3_mk_fpa_round_toward_zero(*self.ctx.ctx),
                RoundingMode::TiesTowardPositive => z3_sys::Z3_mk_fpa_round_toward_positive(*self.ctx.ctx),
                RoundingMode::TiesTowardNegative => z3_sys::Z3_mk_fpa_round_toward_negative(*self.ctx.ctx),
            }
        }
    }

    fn from_term(&self, term: z3_sys::Z3_ast) -> Self {
        Self {
            term,
            ctx: self.ctx.clone(),
            ty: self.ty.clone(),
        }
    }

    fn _from_term(ctx: Z3Context, term: z3_sys::Z3_ast, ty: OperandType) -> Self {
        Self {
            term,
            ctx: ctx.clone(),
            ty: ty.clone(),
        }
    }

    fn _from_f64(mut ctx: Z3Context, value: f64, ty: OperandType) -> Self {
        let term = unsafe {
            let mode = z3_sys::Z3_mk_bv_sort(*ctx.ctx, ty.size());
            let name = CStr::from_ptr(ctx.un_named().as_ptr() as *const i8);
            let term = z3_sys::Z3_mk_fpa_numeral_double(*ctx.ctx, value, mode);
            term
        };
        Self::_from_term(ctx, term, ty)
    }

    fn unconstrained(mut ctx: Z3Context, ty: general_assembly::extension::ieee754::OperandType, name: Option<String>) -> Self {
        let name = match name {
            Some(name) => name,
            None => ctx.un_named(),
        };
        let exp = ty.exponent();
        let frac = ty.fraction();
        let term = unsafe {
            let mode = z3_sys::Z3_mk_fpa_sort(*ctx.ctx, exp as u32, frac as u32);
            let name = CStr::from_ptr(name.as_ptr() as *const i8);
            let term = z3_sys::Z3_mk_fresh_const(*ctx.ctx, name.as_ptr(), mode);
            term
        };
        Self { term, ctx, ty }
    }

    fn get_a_solution(&self) -> Option<f64> {
        println!("Checking if is sat");
        let value = unsafe { z3_sys::Z3_solver_check(*self.ctx.ctx, *self.ctx.solver) };

        if value != Z3_L_TRUE {
            println!("Was not sat... :/");
            return None;
        }
        let mut buffer: u64 = 0;
        println!("Getting moddel");

        let model = unsafe { z3_sys::Z3_solver_get_model(*self.ctx.ctx, *self.ctx.solver) };
        unsafe { z3_sys::Z3_model_inc_ref(*self.ctx.ctx, model) };
        println!("Got a model");
        let mut c = Z3Fp::_from_f64(self.ctx.clone(), 0., self.ty());
        println!("Evaluating valiable in the model");
        let success = unsafe { z3_sys::Z3_model_eval(*self.ctx.ctx, model, self.term, true, core::ptr::from_mut(&mut c.term)) };
        if !success {
            println!("Evaluation failed :(");
            return None;
        }

        println!("Getting constant for modelled number");
        let success = unsafe { z3_sys::Z3_get_numeral_double(*self.ctx.ctx, c.term) };
        println!("Got model for constant :)");
        Some(success)
    }
}

impl SmtFPExpr for Z3Fp {
    type Expression = Z3Bv;

    fn mul(&self, other: &Self, rm: general_assembly::extension::ieee754::RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { Z3_mk_fpa_mul(*self.ctx.ctx, rm, self.term, other.term) };
        Ok(self.from_term(term))
    }

    fn sub(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { z3_sys::Z3_mk_fpa_sub(*self.ctx.ctx, rm, self.term, other.term) };
        Ok(self.from_term(term))
    }

    fn add(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { z3_sys::Z3_mk_fpa_add(*self.ctx.ctx, rm, self.term, other.term) };
        Ok(self.from_term(term))
    }

    fn div(&self, other: &Self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { z3_sys::Z3_mk_fpa_div(*self.ctx.ctx, rm, self.term, other.term) };
        Ok(self.from_term(term))
    }

    fn remainder(&self, other: &Self, _rm: RoundingMode) -> crate::Result<Self> {
        let term = unsafe { z3_sys::Z3_mk_fpa_rem(*self.ctx.ctx, self.term, other.term) };
        Ok(self.from_term(term))
    }

    fn sqrt(&self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { z3_sys::Z3_mk_fpa_sqrt(*self.ctx.ctx, rm, self.term) };
        Ok(self.from_term(term))
    }

    fn neg(&self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { z3_sys::Z3_mk_fpa_neg(*self.ctx.ctx, self.term) };
        Ok(self.from_term(term))
    }

    fn round_to_integral(&self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { z3_sys::Z3_mk_fpa_round_to_integral(*self.ctx.ctx, rm, self.term) };
        Ok(self.from_term(term))
    }

    fn convert_from_bv(bv: Self::Expression, rm: RoundingMode, source_ty: OperandType, dest_ty: OperandType, signed: bool) -> crate::Result<Self> {
        // match source_ty {
        //     OperandType::Binary16 => {
        //         return Ok(Self {
        //             ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
        //             ty: dest_ty,
        //         })
        //     }
        //
        //     OperandType::Binary32 => {
        //         return Ok(Self {
        //             ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
        //             ty: dest_ty,
        //         })
        //     }
        //     OperandType::Binary64 => {
        //         return Ok(Self {
        //             ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
        //             ty: dest_ty,
        //         })
        //     }
        //     OperandType::Binary128 => {
        //         return Ok(Self {
        //             ctx: FpOrBv::Fp(FP::from_ieee754_bv(&bv.0, &conv_ty(&dest_ty))),
        //             ty: dest_ty,
        //         })
        //     }
        //     _ => {}
        // }
        //
        // let ctx = match signed {
        //     true => FP::from_sbv(bv.0, conv_rm(&rm), &conv_ty(&dest_ty)),
        //     false => FP::from_ubv(bv.0, conv_rm(&rm), &conv_ty(&dest_ty)),
        // };
        //
        // Ok(Self {
        //     ctx: FpOrBv::Fp(ctx),
        //     ty: dest_ty,
        // })v

        let new = Self::unconstrained(bv.ctx.clone(), dest_ty, None);
        let new_int = new.round_to_integral(rm.clone())?;
        let new_bv = new_int.to_bv(rm, signed)?;
        println!("Rounded: {new_int:?}");
        unsafe {
            z3_sys::Z3_solver_assert(*bv.ctx.ctx, *bv.ctx.solver, z3_sys::Z3_mk_eq(*bv.ctx.ctx, bv.term, new_bv.term));
        }
        println!("Conversion done!");
        Ok(new_int)
    }

    fn ty(&self) -> general_assembly::extension::ieee754::OperandType {
        self.ty.clone()
    }

    fn any(&self, ty: general_assembly::extension::ieee754::OperandType) -> crate::Result<Self> {
        let exp = ty.exponent();
        let frac = ty.fraction();
        let term = unsafe {
            let mode = z3_sys::Z3_mk_fpa_sort(*self.ctx.ctx, exp as u32, frac as u32);
            let name = CStr::from_ptr(self.ctx.clone().un_named().as_ptr() as *const i8);
            let term = z3_sys::Z3_mk_fresh_const(*self.ctx.ctx, name.as_ptr(), mode);
            term
        };
        Ok(Self { term, ctx: self.ctx.clone(), ty })
    }

    fn abs(&self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { z3_sys::Z3_mk_fpa_abs(*self.ctx.ctx, self.term) };
        Ok(self.from_term(term))
    }

    fn to_bv(&self, rm: RoundingMode, signed: bool) -> crate::Result<Self::Expression> {
        let term = unsafe { z3_sys::Z3_mk_fpa_to_ieee_bv(*self.ctx.ctx, self.term) };
        Ok(Z3Bv { term, ctx: self.ctx.clone() })
    }

    fn compare(&self, other: &Self, cmp: general_assembly::extension::ieee754::ComparisonMode, rm: RoundingMode) -> crate::Result<Self::Expression> {
        let term = unsafe {
            match cmp {
                general_assembly::extension::ieee754::ComparisonMode::Less => z3_sys::Z3_mk_fpa_lt(*self.ctx.ctx, self.term, other.term),
                general_assembly::extension::ieee754::ComparisonMode::LessOrEqual => z3_sys::Z3_mk_fpa_leq(*self.ctx.ctx, self.term, other.term),
                general_assembly::extension::ieee754::ComparisonMode::Greater => z3_sys::Z3_mk_fpa_gt(*self.ctx.ctx, self.term, other.term),
                general_assembly::extension::ieee754::ComparisonMode::NotGreater => z3_sys::Z3_mk_not(*self.ctx.ctx, z3_sys::Z3_mk_fpa_gt(*self.ctx.ctx, self.term, other.term)),
                general_assembly::extension::ieee754::ComparisonMode::NotLess => z3_sys::Z3_mk_not(*self.ctx.ctx, z3_sys::Z3_mk_fpa_lt(*self.ctx.ctx, self.term, other.term)),
                general_assembly::extension::ieee754::ComparisonMode::GreaterOrEqual => z3_sys::Z3_mk_fpa_geq(*self.ctx.ctx, self.term, other.term),
                general_assembly::extension::ieee754::ComparisonMode::Equal => z3_sys::Z3_mk_fpa_eq(*self.ctx.ctx, self.term, other.term),
                general_assembly::extension::ieee754::ComparisonMode::NotEqual => z3_sys::Z3_mk_not(*self.ctx.ctx, z3_sys::Z3_mk_fpa_eq(*self.ctx.ctx, self.term, other.term)),
                general_assembly::extension::ieee754::ComparisonMode::LessUnordered | general_assembly::extension::ieee754::ComparisonMode::GreaterUnordered => unimplemented!(),
            }
        };
        let bv = Z3Bv { term, ctx: self.ctx.clone() };
        Ok(bv.ite(&bv.bool(true), &bv.bool(false)))
    }

    fn check_meta(&self, op: general_assembly::extension::ieee754::NonComputational, rm: RoundingMode) -> crate::Result<Self::Expression> {
        let term = unsafe {
            match op {
                general_assembly::extension::ieee754::NonComputational::IsNan => z3_sys::Z3_mk_fpa_is_nan(*self.ctx.ctx, self.term),
                general_assembly::extension::ieee754::NonComputational::IsZero => z3_sys::Z3_mk_fpa_is_zero(*self.ctx.ctx, self.term),
                general_assembly::extension::ieee754::NonComputational::IsNormal => z3_sys::Z3_mk_fpa_is_normal(*self.ctx.ctx, self.term),
                general_assembly::extension::ieee754::NonComputational::IsSubNormal => z3_sys::Z3_mk_fpa_is_subnormal(*self.ctx.ctx, self.term),
                general_assembly::extension::ieee754::NonComputational::IsFinite => z3_sys::Z3_mk_not(*self.ctx.ctx, z3_sys::Z3_mk_fpa_is_infinite(*self.ctx.ctx, self.term)),
                general_assembly::extension::ieee754::NonComputational::IsInfinite => z3_sys::Z3_mk_fpa_is_infinite(*self.ctx.ctx, self.term),
                general_assembly::extension::ieee754::NonComputational::IsSignMinus => z3_sys::Z3_mk_fpa_is_negative(*self.ctx.ctx, self.term),
                general_assembly::extension::ieee754::NonComputational::IsCanonical => unimplemented!(),
            }
        };
        let bv = Z3Bv { term, ctx: self.ctx.clone() };
        Ok(bv.ite(&bv.bool(true), &bv.bool(false)))
    }

    fn get_const(&self) -> Option<f64> {
        // let value = unsafe { z3_sys::Z3_solver_check(*self.ctx.ctx, *self.ctx.solver)
        // };
        //
        // if value != Z3_L_TRUE {
        //     println!("UNSAT!!");
        //     return None;
        // }

        let success = unsafe { z3_sys::Z3_get_numeral_double(*self.ctx.ctx, self.term) };
        Some(success)
    }

    fn fused_multiply(&self, mul: &Self, add: &Self, rm: RoundingMode) -> crate::Result<Self> {
        let rm = self.conv(rm);
        let term = unsafe { Z3_mk_fpa_fma(*self.ctx.ctx, rm, self.term, mul.term, add.term) };
        Ok(self.from_term(term))
    }
}

#[derive(Clone, Debug)]
pub struct Z3Solver {
    pub ctx: Z3Context,
}

impl SmtSolver for Z3Solver {
    type Expression = Z3Bv;
    type FpExpression = Z3Fp;

    fn push(&self) {
        unsafe {
            z3_sys::Z3_solver_push(*self.ctx.ctx, *self.ctx.solver);
        }
    }

    fn pop(&self) {
        unsafe { z3_sys::Z3_solver_pop(*self.ctx.ctx, *self.ctx.solver, 1) }
    }

    fn one(&self, bits: u32) -> Self::Expression {
        Z3Bv::_from_u64(self.ctx.clone(), 1, bits)
    }

    fn zero(&self, size: u32) -> Self::Expression {
        Z3Bv::_from_u64(self.ctx.clone(), 0, size)
    }

    fn is_sat(&self) -> Result<bool, super::SolverError> {
        let value = unsafe { z3_sys::Z3_solver_check(*self.ctx.ctx, *self.ctx.solver) };

        if value != Z3_L_TRUE {
            return Ok(false);
        }
        Ok(true)
    }

    fn assert(&self, constraint: &Self::Expression) {
        let val = Z3Bv::from_bool(self.ctx.clone(), true);
        let rhs = constraint.resize_unsigned(1);
        let eq = unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx, val.term, rhs.term) };

        unsafe {
            z3_sys::Z3_solver_assert(*self.ctx.ctx, *self.ctx.solver, eq);
        }
    }

    fn from_u64(&self, value: u64, size: u32) -> Self::Expression {
        Z3Bv::_from_u64(self.ctx.clone(), value, size)
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        Z3Bv::from_bool(self.ctx.clone(), value)
    }

    fn signed_max(&self, size: u32) -> Self::Expression {
        self.from_u64(!(1u64 << size), size)
    }

    fn signed_min(&self, size: u32) -> Self::Expression {
        self.from_u64(!0, size)
    }

    fn get_values(&self, expr: &Self::Expression, mut upper_bound: u32) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self.push();
        let mut buffer = Vec::new();
        while let Some(ret) = expr.get_a_solution(&[]) {
            let value = Z3Bv::_from_u64(self.ctx.clone(), ret, expr.size());
            let eq = expr.__ne(&value);
            buffer.push(value);
            unsafe {
                z3_sys::Z3_solver_assert(*self.ctx.ctx, *self.ctx.solver, eq);
            }
            if upper_bound == 0 {
                return Ok(super::Solutions::AtLeast(buffer));
            }
            upper_bound -= 1;
        }

        self.pop();
        Ok(super::Solutions::Exactly(buffer))
    }

    fn unsigned_max(&self, size: u32) -> Self::Expression {
        self.from_u64(!0, size)
    }

    fn unconstrained(&self, size: u32, name: &str) -> Self::Expression {
        let val = unsafe {
            let mode = z3_sys::Z3_mk_bv_sort(*self.ctx.ctx, size);
            let name = CStr::from_ptr(name.as_ptr() as *const i8);
            z3_sys::Z3_mk_fresh_const(*self.ctx.ctx, name.as_ptr(), mode)
        };
        Z3Bv { ctx: self.ctx.clone(), term: val }
    }

    fn unconstrained_fp(&self, ty: general_assembly::extension::ieee754::OperandType, name: &str) -> Self::FpExpression {
        Z3Fp::unconstrained(self.ctx.clone(), ty, Some(name.to_string()))
    }

    fn get_solutions(&self, expr: &Self::Expression, mut upper_bound: u32) -> Result<super::Solutions<Self::Expression>, super::SolverError> {
        self.push();
        let mut buffer = Vec::new();
        while let Some(ret) = expr.get_a_solution(&[]) {
            let value = Z3Bv::_from_u64(self.ctx.clone(), ret, expr.size());
            let eq = expr.__ne(&value);
            buffer.push(value);
            unsafe {
                z3_sys::Z3_solver_assert(*self.ctx.ctx, *self.ctx.solver, eq);
            }
            if upper_bound == 0 {
                return Ok(super::Solutions::AtLeast(buffer));
            }
            upper_bound -= 1;
        }

        self.pop();
        Ok(super::Solutions::Exactly(buffer))
    }

    fn is_sat_with_constraint(&self, constraint: &Self::Expression) -> Result<bool, super::SolverError> {
        let val = Z3Bv::from_bool(self.ctx.clone(), true);
        let rhs = constraint.resize_unsigned(1);
        let eq = unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx, val.term, rhs.term) };
        Ok(Z3_L_TRUE == unsafe { z3_sys::Z3_solver_check_assumptions(*self.ctx.ctx, *self.ctx.solver, 1, [eq].as_ptr()) })
    }

    fn is_sat_with_constraints(&self, constraints: &[Self::Expression]) -> Result<bool, super::SolverError> {
        let val = Z3Bv::from_bool(self.ctx.clone(), true);
        let mut valid = |constraint: &Self::Expression| {
            let rhs = constraint.resize_unsigned(1);
            let eq = unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx, val.term, rhs.term) };
            eq
        };
        let n = constraints.len();
        let constraints: Vec<_> = constraints.iter().map(|el| valid(el)).collect();
        Ok(Z3_L_TRUE == unsafe { z3_sys::Z3_solver_check_assumptions(*self.ctx.ctx, *self.ctx.solver, n as u32, constraints.as_ptr()) })
    }

    fn unconstrained_fp_unnamed(&self, ty: general_assembly::extension::ieee754::OperandType) -> Self::FpExpression {
        Z3Fp::unconstrained(self.ctx.clone(), ty, None)
    }

    fn new() -> Self {
        unsafe {
            let cfg = z3_sys::Z3_mk_config();
            // let name = CStr::from_ptr("verbose".as_ptr() as *const i8);
            // let value = CStr::from_ptr("1".as_ptr() as *const i8);
            // z3_sys::Z3_set_param_value(cfg, name.as_ptr(), value.as_ptr());
            let ctx = z3_sys::Z3_mk_context(cfg);
            let solver = z3_sys::Z3_mk_solver(ctx);
            z3_sys::Z3_solver_inc_ref(ctx, solver);
            Self {
                ctx: Z3Context {
                    ctx: Arc::pin(ctx),
                    solver: Arc::pin(solver),
                    counter: Arc::pin(AtomicU64::new(0)),
                },
            }
        }
    }
}

#[derive(Clone)]
pub struct Z3Bv {
    term: z3_sys::Z3_ast,
    ctx: Z3Context,
}

impl Z3Bv {
    fn _size(&self) -> u32 {
        unsafe {
            let sort = z3_sys::Z3_get_sort(*self.ctx.ctx, self.term);
            z3_sys::Z3_get_bv_sort_size(*self.ctx.ctx, sort)
        }
    }

    fn bool(&self, value: bool) -> Z3Bv {
        Self::from_bool(self.ctx.clone(), value)
    }

    fn from_bool(mut ctx: Z3Context, value: bool) -> Z3Bv {
        let term = unsafe {
            let name = CStr::from_ptr(ctx.un_named().as_ptr() as *const i8);
            let mode = z3_sys::Z3_mk_bv_sort(*ctx.ctx, 1);
            let term = z3_sys::Z3_mk_unsigned_int64(*ctx.ctx, value as u64, mode);
            term
        };
        Z3Bv { term, ctx }
    }

    fn _from_u64(mut ctx: Z3Context, value: u64, size: u32) -> Self {
        let term = unsafe {
            let mode = z3_sys::Z3_mk_bv_sort(*ctx.ctx, size);
            let name = CStr::from_ptr(ctx.un_named().as_ptr() as *const i8);
            let term = z3_sys::Z3_mk_unsigned_int64(*ctx.ctx, value, mode);
            term
        };
        Z3Bv { term, ctx }
    }

    fn unconstrained(mut ctx: Z3Context, size: u32, name: Option<String>) -> Self {
        let name = match name {
            Some(name) => name,
            None => ctx.un_named(),
        };
        let term = unsafe {
            let mode = z3_sys::Z3_mk_bv_sort(*ctx.ctx, size);
            let name = CStr::from_ptr(name.as_ptr() as *const i8);
            let term = z3_sys::Z3_mk_fresh_const(*ctx.ctx, name.as_ptr(), mode);
            term
        };
        Z3Bv { term, ctx }
    }

    fn __eq(&self, other: &Self) -> z3_sys::Z3_ast {
        unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx, self.term, other.term) }
    }

    fn __ne(&self, other: &Self) -> z3_sys::Z3_ast {
        let intermediate = unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx, self.term, other.term) };

        unsafe { z3_sys::Z3_mk_not(*self.ctx.ctx, intermediate) }
    }

    pub fn from_term(ctx: Z3Context, term: z3_sys::Z3_ast) -> Self {
        unsafe {
            z3_sys::Z3_inc_ref(*ctx.ctx, term);
        }
        Self { term, ctx }
    }

    pub fn _from_term(&self, term: z3_sys::Z3_ast) -> Self {
        unsafe {
            z3_sys::Z3_inc_ref(*self.ctx.ctx, term);
        }
        Self { term, ctx: self.ctx.clone() }
    }
}
impl SmtExpr for Z3Bv {
    type FPExpression = Z3Fp;

    fn or(&self, other: &Self) -> Self {
        Self {
            ctx: self.ctx.clone(),
            term: unsafe { z3_sys::Z3_mk_bvor(*self.ctx.ctx, self.term, other.term) },
        }
    }

    fn any(&self, width: u32) -> Self {
        let val = unsafe {
            let mode = z3_sys::Z3_mk_bv_sort(*self.ctx.ctx, width);
            let name = CStr::from_ptr(self.ctx.clone().un_named().as_ptr() as *const i8);
            z3_sys::Z3_mk_fresh_const(*self.ctx.ctx, name.as_ptr(), mode)
        };
        Self::from_term(self.ctx.clone(), val)
    }

    fn _eq(&self, other: &Self) -> Self {
        Self::from_term(self.ctx.clone(), unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx, self.term, other.term) }).ite(&self.bool(true), &self.bool(false))
    }

    fn _ne(&self, other: &Self) -> Self {
        let intermediate = unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx, self.term, other.term) };

        Self::from_term(self.ctx.clone(), unsafe { z3_sys::Z3_mk_not(*self.ctx.ctx, intermediate) }).ite(&self.bool(true), &self.bool(false))
    }

    fn ugt(&self, other: &Self) -> Self {
        Self::from_term(self.ctx.clone(), unsafe { z3_sys::Z3_mk_bvugt(*self.ctx.ctx, self.term, other.term) }).ite(&self.bool(true), &self.bool(false))
    }

    fn sgt(&self, other: &Self) -> Self {
        Self::from_term(self.ctx.clone(), unsafe { z3_sys::Z3_mk_bvsgt(*self.ctx.ctx, self.term, other.term) }).ite(&self.bool(true), &self.bool(false))
    }

    fn ugte(&self, other: &Self) -> Self {
        Self::from_term(self.ctx.clone(), unsafe { z3_sys::Z3_mk_bvuge(*self.ctx.ctx, self.term, other.term) }).ite(&self.bool(true), &self.bool(false))
    }

    fn sgte(&self, other: &Self) -> Self {
        self._from_term(unsafe { z3_sys::Z3_mk_bvsge(*self.ctx.ctx, self.term, other.term) })
            .ite(&self.bool(true), &self.bool(false))
    }

    fn sign_ext(&self, width: u32) -> Self {
        self._from_term(unsafe { z3_sys::Z3_mk_sign_ext(*self.ctx.ctx, width - self.size(), self.term) })
    }

    fn ult(&self, other: &Self) -> Self {
        self._from_term(unsafe { z3_sys::Z3_mk_bvult(*self.ctx.ctx, self.term, other.term) })
            .ite(&self.bool(true), &self.bool(false))
    }

    fn slt(&self, other: &Self) -> Self {
        self._from_term(unsafe { z3_sys::Z3_mk_bvslt(*self.ctx.ctx, self.term, other.term) })
            .ite(&self.bool(true), &self.bool(false))
    }

    fn ulte(&self, other: &Self) -> Self {
        self._from_term(unsafe { z3_sys::Z3_mk_bvule(*self.ctx.ctx, self.term, other.term) })
            .ite(&self.bool(true), &self.bool(false))
    }

    fn slte(&self, other: &Self) -> Self {
        self._from_term(unsafe { z3_sys::Z3_mk_bvsle(*self.ctx.ctx, self.term, other.term) })
            .ite(&self.bool(true), &self.bool(false))
    }

    fn slice(&self, low: u32, high: u32) -> Self {
        let term = unsafe { z3_sys::Z3_mk_extract(*self.ctx.ctx, high, low, self.term) };
        self._from_term(term)
    }

    fn umulo(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvmul_no_overflow(*self.ctx.ctx, self.term, other.term, false) };
        self._from_term(term).ite(&self.bool(false), &self.bool(true))
    }

    fn smulo(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvmul_no_overflow(*self.ctx.ctx, self.term, other.term, true) };
        self._from_term(term).ite(&self.bool(false), &self.bool(true))
    }

    fn usubo(&self, other: &Self) -> Self {
        let other = other.clone().simplify();
        println!("usubo Self {self:?}, other {other:?}");
        let term = unsafe { z3_sys::Z3_mk_bvsub_no_overflow(*self.ctx.ctx, self.term, other.term) };
        let overflow = self._from_term(term).ite(&self.bool(false), &self.bool(true));
        let term = unsafe { z3_sys::Z3_mk_bvsub_no_underflow(*self.ctx.ctx, self.term, other.term, false) };
        let underflow = self._from_term(term).ite(&self.bool(false), &self.bool(true));
        underflow.or(&overflow)
    }

    fn ssubo(&self, other: &Self) -> Self {
        let other = other.clone().simplify();
        println!("ssubo Self {self:?}, other {other:?}");
        let term = unsafe { z3_sys::Z3_mk_bvsub_no_overflow(*self.ctx.ctx, self.term, other.term) };
        let overflow = self._from_term(term).ite(&self.bool(false), &self.bool(true));
        let term = unsafe { z3_sys::Z3_mk_bvsub_no_underflow(*self.ctx.ctx, self.term, other.term, true) };
        let underflow = self._from_term(term).ite(&self.bool(false), &self.bool(true));
        underflow.or(&overflow)
    }

    fn uaddo(&self, other: &Self) -> Self {
        let other = other.clone().simplify();
        println!("uaddo Self {self:?}, other {other:?}");
        let term = unsafe { z3_sys::Z3_mk_bvadd_no_overflow(*self.ctx.ctx, self.term, other.term, false) };
        self._from_term(term).ite(&self.bool(false), &self.bool(true))
    }

    fn saddo(&self, other: &Self) -> Self {
        let other = other.clone().simplify();
        println!("saddo Self {self:?}, other {other:?}");
        let term = unsafe { z3_sys::Z3_mk_bvadd_no_overflow(*self.ctx.ctx, self.term, other.term, true) };
        let overflow = self._from_term(term).ite(&self.bool(false), &self.bool(true));
        let term = unsafe { z3_sys::Z3_mk_bvadd_no_underflow(*self.ctx.ctx, self.term, other.term) };
        let underflow = self._from_term(term).ite(&self.bool(false), &self.bool(true));
        overflow.or(&underflow)
    }

    fn sub(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvsub(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn add(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvadd(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn udiv(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvudiv(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn urem(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvurem(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn srem(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvsrem(*self.ctx.ctx, self.term, other.term) };

        self._from_term(term)
    }

    fn sdiv(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvsdiv(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn mul(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvmul(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn and(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvand(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn xor(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvxor(*self.ctx.ctx, self.term, other.term) };

        self._from_term(term)
    }

    fn not(&self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_bvnot(*self.ctx.ctx, self.term) };

        self._from_term(term)
    }

    fn ite(&self, then_bv: &Self, else_bv: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_ite(*self.ctx.ctx, self.term, then_bv.term, else_bv.term) };
        self._from_term(term)
    }

    fn pop(&self) {
        unsafe {
            z3_sys::Z3_solver_pop(*self.ctx.ctx, *self.ctx.solver, 1);
        }
    }

    fn size(&self) -> u32 {
        self._size()
    }

    fn push(&self) {
        unsafe {
            z3_sys::Z3_solver_push(*self.ctx.ctx, *self.ctx.solver);
        }
    }

    fn shift(&self, steps: &Self, direction: general_assembly::prelude::Shift) -> Self {
        let term = unsafe {
            match direction {
                general_assembly::shift::Shift::Lsl => z3_sys::Z3_mk_bvshl(*self.ctx.ctx, self.term, steps.term),
                general_assembly::shift::Shift::Lsr => z3_sys::Z3_mk_bvlshr(*self.ctx.ctx, self.term, steps.term),
                general_assembly::shift::Shift::Asr => z3_sys::Z3_mk_bvashr(*self.ctx.ctx, self.term, steps.term),
                _ => unimplemented!(""),
            }
        };
        self._from_term(term)
    }

    fn uadds(&self, other: &Self) -> Self {
        todo!()
    }

    fn sadds(&self, other: &Self) -> Self {
        todo!()
    }

    fn usubs(&self, other: &Self) -> Self {
        todo!()
    }

    fn ssubs(&self, other: &Self) -> Self {
        todo!()
    }

    fn concat(&self, other: &Self) -> Self {
        let term = unsafe { z3_sys::Z3_mk_concat(*self.ctx.ctx, self.term, other.term) };
        self._from_term(term)
    }

    fn zero_ext(&self, width: u32) -> Self {
        let n = self._size();
        let term = unsafe { z3_sys::Z3_mk_zero_ext(*self.ctx.ctx, width - n, self.term) };
        self._from_term(term)
    }

    fn simplify(self) -> Self {
        let term = unsafe { z3_sys::Z3_simplify(*self.ctx.ctx, self.term) };
        self._from_term(term)
    }

    fn get_constant(&self) -> Option<u64> {
        let value = unsafe { z3_sys::Z3_solver_check(*self.ctx.ctx, *self.ctx.solver) };

        if value != Z3_L_TRUE {
            println!("UNSAT!!!");
            return None;
        }
        let mut buffer: u64 = 0;
        self.push();
        let mut upper_bound = 1;
        let mut buffer = Vec::new();
        println!("Got a solution");
        while let Some(ret) = self.get_a_solution(&[]) {
            println!("Got a resolution");
            let value = Z3Bv::_from_u64(self.ctx.clone(), ret, self.size());
            println!("Created bv");
            let intermediate = unsafe { z3_sys::Z3_mk_eq(*self.ctx.ctx.clone(), self.term, value.term) };
            let eq = unsafe { z3_sys::Z3_mk_not(*self.ctx.ctx, intermediate) };
            println!("Set req");
            buffer.push(ret);
            unsafe {
                println!("Asserting");
                z3_sys::Z3_solver_assert(*self.ctx.ctx, *self.ctx.solver, eq);
                println!("Asserted!");
            }
            if upper_bound == 0 {
                break;
            }
            upper_bound -= 1;
        }

        self.pop();
        println!("Results {buffer:?}");
        // return buffer.get(0).cloned();
        //
        // let success = unsafe { z3_sys::Z3_get_numeral_uint64(*self.ctx.ctx,
        // self.term, core::ptr::from_mut(&mut buffer)) }; if success {
        //     return Some(buffer);
        // }
        // println!("Was not a numeral?? {self:?}");
        if buffer.len() != 1 {
            return None;
        }
        Some(unsafe { buffer.get_unchecked(0).clone() })
    }

    fn replace_part(&self, start_idx: u32, replace_with: Self) -> Self {
        let end = replace_with._size() + start_idx;
        let end = self.slice(start_idx, end);
        let start = self.slice(0, start_idx);

        start.concat(&replace_with).concat(&end)
    }

    fn get_a_solution(&self, e: &[Self]) -> Option<u64> {
        let l = e.len();
        let constraints = e.iter().map(|el| Self::from_term(self.ctx.clone(), el.__eq(&self.bool(true))).term).collect::<Vec<_>>();
        println!("Checking if is sat");
        let value = unsafe { z3_sys::Z3_solver_check_assumptions(*self.ctx.ctx, *self.ctx.solver, l as u32, constraints.as_ptr()) };

        if value != Z3_L_TRUE {
            println!("Was not sat... :/");
            return None;
        }
        let mut buffer: u64 = 0;
        println!("Getting moddel");

        let model = unsafe { z3_sys::Z3_solver_get_model(*self.ctx.ctx, *self.ctx.solver) };
        unsafe { z3_sys::Z3_model_inc_ref(*self.ctx.ctx, model) };
        println!("Got a model");
        let mut c = Z3Bv::_from_u64(self.ctx.clone(), 0, self._size());
        println!("Evaluating valiable in the model");
        let success = unsafe { z3_sys::Z3_model_eval(*self.ctx.ctx, model, self.term, true, core::ptr::from_mut(&mut c.term)) };
        if !success {
            println!("Evaluation failed :(");
            return None;
        }

        println!("Getting constant for modelled number");
        let mut buffer: u64 = 0;
        let success = unsafe { z3_sys::Z3_get_numeral_uint64(*self.ctx.ctx, c.term, core::ptr::from_mut(&mut buffer)) };
        println!("Got model for constant :)");
        if success {
            return Some(buffer);
        }
        println!("Though it was not valid :(");

        None
    }

    fn get_identifier(&self) -> Option<String> {
        None
    }

    fn resize_unsigned(&self, width: u32) -> Self {
        if self._size() == width {
            return self.clone();
        }
        if self._size() > width {
            return self.slice(0, width);
        }
        self.zero_ext(width)
    }

    fn to_binary_string(&self) -> String {
        "NOT USED?".to_string()
    }

    fn get_constant_bool(&self) -> Option<bool> {
        if self._size() != 1 {
            return None;
        }
        self.get_constant().map(|el| el != 0)
    }

    fn from_fp(fp: &Self::FPExpression, rm: general_assembly::extension::ieee754::RoundingMode, signed: bool) -> crate::Result<Self> {
        fp.to_bv(rm, signed)
    }
}
impl<State: UserStateContainer> std::fmt::Display for Z3Array<State> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\tVariables:\r\n")?;
        for (key, value) in self.variables.iter() {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => strip(format!("{:?}", value)),
            })?;
        }
        f.write_str("\tFP Variables:\r\n")?;
        for (key, value) in self.fp_variables.iter() {
            write!(f, "\t\t{key} : {}\r\n", match value.get_const() {
                Some(value) => value.to_string(),
                _ => strip(format!("{:?}", value)),
            })?;
        }
        f.write_str("\tRegister file:\r\n")?;
        for (key, value) in self.register_file.iter() {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => strip(format!("{:?}", value)),
            })?;
        }
        f.write_str("\tFlags:\r\n")?;

        for (key, value) in self.flags.iter() {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => strip(format!("{:?}", value)),
            })?;
        }
        Ok(())
    }
}

fn strip(s: String) -> String {
    if 50 < s.len() {
        return "Large symbolic expression".to_string();
    }
    s
}
impl std::fmt::Debug for Z3Fp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cstr = unsafe { CStr::from_ptr(z3_sys::Z3_ast_to_string(*self.ctx.ctx, self.term)) };
        let dbg = cstr.to_string_lossy().to_string();
        let sort = unsafe { z3_sys::Z3_get_sort(*self.ctx.ctx, self.term) };
        let cstr = unsafe { CStr::from_ptr(z3_sys::Z3_sort_to_string(*self.ctx.ctx, sort)) };
        let ty = cstr.to_string_lossy().to_string();

        write!(f, "({ty}) {dbg}")
    }
}
impl std::fmt::Debug for Z3Bv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cstr = unsafe { CStr::from_ptr(z3_sys::Z3_ast_to_string(*self.ctx.ctx, self.term)) };

        let dbg = cstr.to_string_lossy().to_string();
        let sort = unsafe { z3_sys::Z3_get_sort(*self.ctx.ctx, self.term) };
        let cstr = unsafe { CStr::from_ptr(z3_sys::Z3_sort_to_string(*self.ctx.ctx, sort)) };
        let ty = cstr.to_string_lossy().to_string();

        write!(f, "({ty}) {dbg}")
    }
}
#[cfg(test)]
mod test {

    use std::u32;

    use general_assembly::{
        condition::Condition,
        extension::ieee754::{self, RoundingMode},
        operand::{DataWord, Operand},
        operation::Operation,
    };
    use hashbrown::HashMap;

    use crate::{
        arch::{arm::v6::ArmV6M, Architecture, NoArchitectureOverride},
        defaults::z3::{DefaultComposition, DefaultCompositionNoLogger},
        executor::{
            add_with_carry,
            count_leading_ones,
            count_leading_zeroes,
            count_ones,
            count_zeroes,
            hooks::HookContainer,
            instruction::{CycleCount, Instruction},
            state::GAState,
            vm::VM,
            GAExecutor,
        },
        initiation::NoArchOverride,
        logging::NoLogger,
        path_selection::PathSelector,
        project::Project,
        smt::{
            z3::{Z3Bv, Z3Fp, Z3Solver},
            SmtExpr,
            SmtFPExpr,
            SmtMap,
            SmtSolver,
        },
        Endianness,
        WordSize,
    };

    #[test]
    fn test_count_ones_concrete() {
        let ctx = Z3Solver::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
            project,
            ctx.clone(),
            ctx,
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        let num1 = state.memory.from_u64(1, 32);
        let num32 = state.memory.from_u64(32, 32);
        let numff = state.memory.from_u64(0xff, 32);
        let result: Z3Bv = count_ones(&num1, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result: Z3Bv = count_ones(&num32, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result: Z3Bv = count_ones(&numff, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 8);
    }

    #[test]
    fn test_count_ones_symbolic() {
        let ctx = Z3Solver::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        let any_u32 = ctx.unconstrained(32, "any1");
        let num_0x100 = ctx.from_u64(0x100, 32);
        let num_8 = ctx.from_u64(8, 32);
        ctx.assert(&any_u32.ult(&num_0x100));
        let result = count_ones(&any_u32, &state, 32);
        let result_below_or_equal_8 = result.ulte(&num_8);
        let result_above_8 = result.ugt(&num_8);
        let can_be_below_or_equal_8 = ctx.is_sat_with_constraint(&result_below_or_equal_8).unwrap();
        let can_be_above_8 = ctx.is_sat_with_constraint(&result_above_8).unwrap();
        assert!(can_be_below_or_equal_8);
        assert!(!can_be_above_8);
    }

    #[test]
    fn test_count_zeroes_concrete() {
        let ctx = Z3Solver::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        let num1 = state.memory.from_u64(!1, 32);
        let num32 = state.memory.from_u64(!32, 32);
        let numff = state.memory.from_u64(!0xff, 32);
        let result = count_zeroes(&num1, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result = count_zeroes(&num32, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 1);
        let result = count_zeroes(&numff, &state, 32);
        assert_eq!(result.get_constant().unwrap(), 8);
    }

    #[test]
    fn test_count_leading_ones_concrete() {
        let ctx = Z3Solver::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        let input = state.memory.from_u64(0b1000_0000, 8);
        let result = count_leading_ones(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 1);
        let input = state.memory.from_u64(0b1100_0000, 8);
        let result = count_leading_ones(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 2);
        let input = state.memory.from_u64(0b1110_0011, 8);
        let result = count_leading_ones(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 3);
    }

    #[test]
    fn test_count_leading_zeroes_concrete() {
        let ctx = Z3Solver::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        let input = state.memory.from_u64(!0b1000_0000, 8);
        let result = count_leading_zeroes(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 1);
        let input = state.memory.from_u64(!0b1100_0000, 8);
        let result = count_leading_zeroes(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 2);
        let input = state.memory.from_u64(!0b1110_0011, 8);
        let result = count_leading_zeroes(&input, &state, 8);
        assert_eq!(result.get_constant().unwrap(), 3);
    }

    #[test]
    fn test_add_with_carry() {
        let ctx = Z3Solver::new();
        let project = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project = Box::leak(project);
        let state = GAState::<DefaultComposition>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        let one_bool = state.memory.from_bool(true);
        let zero_bool = state.memory.from_bool(false);
        let zero = state.memory.from_u64(0, 32);
        let num42 = state.memory.from_u64(42, 32);
        let num16 = state.memory.from_u64(16, 32);
        let umax = state.memory.from_u64(u32::MAX as u64, 32);
        let smin = state.memory.from_u64(i32::MIN as u64, 32);
        let smax = state.memory.from_u64(i32::MAX as u64, 32);

        // simple add
        let result = add_with_carry(&num42, &num16, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 58);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // simple sub
        let result = add_with_carry(&num42, &num16.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 26);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // signed sub negative result
        let result = add_with_carry(&num16, &num42.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), (-26i32 as u32) as u64);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // unsigned overflow
        let result = add_with_carry(&umax, &num16, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 15 as u64);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // signed overflow
        let result = add_with_carry(&smax, &num16, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 2147483663);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(result.overflow.get_constant_bool().unwrap());

        // signed underflow
        let result = add_with_carry(&smin, &num16.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 2147483632);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(result.overflow.get_constant_bool().unwrap());

        // zero add
        let result = add_with_carry(&num16, &zero, &zero_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 16);
        assert!(!result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());

        // zero sub
        let result = add_with_carry(&num16, &zero.not(), &one_bool, 32);
        assert_eq!(result.result.get_constant().unwrap(), 16);
        assert!(result.carry_out.get_constant_bool().unwrap());
        assert!(!result.overflow.get_constant_bool().unwrap());
    }

    fn setup_test_vm() -> VM<DefaultCompositionNoLogger> {
        let ctx = Z3Solver::new();
        let project_global = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
        let project: &'static Project = Box::leak(project_global);
        let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
            project,
            ctx.clone(),
            ctx.clone(),
            0,
            0,
            HookContainer::new(),
            (),
            crate::arch::SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new()),
        );
        VM::new_test_vm(project, state, NoLogger).unwrap()
    }

    #[test]
    #[ignore]
    fn test_fp_div_un_even_ties_to_even_explicit() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesToEven),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 2);
    }

    #[test]
    #[ignore]
    fn test_fp_div_un_even_ties_to_even_system_level() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        executor.state.fp_state.rounding_mode = RoundingMode::TiesToEven;
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: None,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 2);
    }

    #[test]
    #[ignore]
    fn test_fp_div_mul() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(4)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR4".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });

        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Multiplication {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR4".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR5".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR5".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 6);
    }

    #[test]
    #[ignore]
    fn test_fp_non_computational() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(0)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsZero,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsInfinite,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsZero,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::NonComputational {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::NonComputational::IsInfinite,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);
    }

    #[test]
    #[ignore]
    fn test_fp_compare() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(3)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(2)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Equal,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Equal,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Greater,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Greater,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::NotGreater,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Less,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::Less,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 0);

        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Compare {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            operation: ieee754::ComparisonMode::LessOrEqual,
            destination: general_assembly::operand::Operand::Register("R0".to_owned()),
            signal: false,
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 : {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!(r0, 1);
    }

    #[test]
    #[ignore]
    fn test_fp_load_store_address() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(144)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("Convert from int done");
        let operation = Operation::Ieee754(ieee754::Operations::Sqrt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Address(general_assembly::operand::Operand::Immediate(DataWord::Word32(0xdead_beef))),
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("sqrt done");

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Address(general_assembly::operand::Operand::Immediate(DataWord::Word32(0xdead_beef))),
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("Round to int done");

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 Result: {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 12)
    }

    #[test]
    #[ignore]

    fn test_fp_load_store_register() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(144)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Sqrt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                    signed: true,
                }, // ieee754::OperandStorage::Address(general_assembly::operand::Operand::Address(DataWord::Word32(120), 32)),,
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                    signed: true,
                }, // ieee754::OperandStorage::Address(general_assembly::operand::Operand::Address(DataWord::Word32(120), 32)),
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap();
        println!("R0 Result: {:?}", r0);
        let r0 = r0.get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 12)
    }

    #[test]
    #[ignore]
    fn test_fp_sqrt() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(144)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Sqrt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 12)
    }

    #[test]
    #[ignore]
    fn test_fp_fma() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());
        let operand_r1 = Operand::Register("R1".to_owned());
        let operand_r2 = Operand::Register("R2".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32((-99i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32((-100i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r2.clone(),
            source: Operand::Immediate(DataWord::Word32((100i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R2".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::FusedMultiplication {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            add: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), (99 * 100) + 100);
    }
    #[test]
    #[ignore]
    fn test_fp_abs() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32((-99i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Abs {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 99);

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32((112i32).cast_unsigned())),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let operation = Operation::Ieee754(ieee754::Operations::Abs {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!((r0 as u32).cast_signed(), 112)
    }

    #[test]
    #[ignore]
    fn test_fp_div_un_even() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(13)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Division {
            nominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            denominator: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, (42. as f32 / 12.).floor() as u64);
    }

    #[test]
    #[ignore]
    fn test_fp_mul() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(12)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Multiplication {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42 * 12);
    }

    #[test]
    fn test_fp_sub() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(12)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Subtraction {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42 - 12);
    }

    #[test]
    fn test_fp_add() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // 1. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("1 done");
        // 2. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        let fpr1 = executor
            .get_fp_operand_value(
                ieee754::Operand {
                    ty: ieee754::OperandType::Binary32,
                    value: ieee754::OperandStorage::Register {
                        id: "FPR1".to_owned(),
                        ty: ieee754::OperandType::Binary32,
                    },
                },
                ieee754::OperandType::Binary32,
                RoundingMode::TiesTowardZero,
                &mut NoLogger,
            )
            .expect("It being possible to retrieve a fp variable");
        let val = fpr1.get_const().expect("This being a constant as it is merely converted from an int!");
        assert!(val == 42.);
        println!("1,2 done");
        let operand_r1 = Operand::Register("R1".to_owned());

        // 3. Load an integer in to a register.
        let operation = Operation::Move {
            destination: operand_r1.clone(),
            source: Operand::Immediate(DataWord::Word32(12)),
        };
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("3 done");
        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::ConvertFromInt {
            operand: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R1".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();

        println!("4 done");
        // 5. Add the two floating point values.
        let operation = Operation::Ieee754(ieee754::Operations::Addition {
            lhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR1".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            rhs: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR2".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("5 done");

        // 4. Load that register in to a fp register and convert to a floating point
        //    value.
        let operation = Operation::Ieee754(ieee754::Operations::RoundToInt {
            source: ieee754::Operand {
                ty: ieee754::OperandType::Binary32,
                value: ieee754::OperandStorage::Register {
                    id: "FPR3".to_owned(),
                    ty: ieee754::OperandType::Binary32,
                },
            },
            destination: ieee754::Operand {
                ty: ieee754::OperandType::Integral { size: 32, signed: true },
                value: ieee754::OperandStorage::CoreRegister {
                    id: "R0".to_owned(),
                    ty: ieee754::OperandType::Integral { size: 32, signed: true },
                    signed: true,
                },
            },
            rounding: Some(ieee754::RoundingMode::TiesTowardZero),
        });
        executor.execute_operation(&operation, &mut NoLogger).unwrap();
        println!("6 done");

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42 + 12);
    }

    #[test]
    fn test_move() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let operand_r0 = Operand::Register("R0".to_owned());

        // move imm into reg
        let operation = Operation::Move {
            destination: operand_r0.clone(),
            source: Operand::Immediate(DataWord::Word32(42)),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0 = executor.get_operand_value(&operand_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42);

        // move reg to local
        let local_r0 = Operand::Local("R0".to_owned());
        let operation = Operation::Move {
            destination: local_r0.clone(),
            source: operand_r0.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0 = executor.get_operand_value(&local_r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0, 42);

        // Move immediate to local memory addr
        let imm = Operand::Immediate(DataWord::Word32(23));
        let memory_op = Operand::AddressInLocal("R0".to_owned(), 32);
        let operation = Operation::Move {
            destination: memory_op.clone(),
            source: imm.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let dexpr_addr = executor.get_dexpr_from_dataword(DataWord::Word32(42));
        let in_memory_value = executor.state.read_word_from_memory(&dexpr_addr).unwrap().get_constant().unwrap();

        assert_eq!(in_memory_value, 23);

        // Move from memory to a local
        let operation = Operation::Move {
            destination: local_r0.clone(),
            source: memory_op.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let local_value = executor.get_operand_value(&local_r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(local_value, 23);
    }

    #[test]
    fn test_add_vm() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

        let r0 = Operand::Register("R0".to_owned());
        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_umax = Operand::Immediate(DataWord::Word32(u32::MAX));
        let imm_16 = Operand::Immediate(DataWord::Word32(16));
        let imm_minus70 = Operand::Immediate(DataWord::Word32(-70i32 as u32));

        // test simple add
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 58);

        // Test add with same operand and destination
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: r0.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 74);

        // Test add with negative number
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus70.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, (-28i32 as u32) as u64);

        // Test add overflow
        let operation = Operation::Add {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_umax.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 41);
    }

    #[test]
    fn test_adc() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_12 = Operand::Immediate(DataWord::Word32(12));
        let imm_umax = Operand::Immediate(DataWord::Word32(u32::MAX));
        let r0 = Operand::Register("R0".to_owned());

        let true_dexpr = executor.state.memory.from_bool(true);
        let false_dexpr = executor.state.memory.from_bool(false);

        // test normal add
        executor.state.set_flag("C".to_owned(), false_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 54);

        // test add with overflow
        executor.state.set_flag("C".to_owned(), false_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_umax.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 11);

        // test add with carry in
        executor.state.set_flag("C".to_owned(), true_dexpr.clone()).unwrap();
        let operation = Operation::Adc {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_12.clone(),
        };

        executor.execute_operation(&operation, &mut NoLogger).ok();
        let result = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();

        assert_eq!(result, 55);
    }

    #[test]
    fn test_sub() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

        let r0 = Operand::Register("R0".to_owned());
        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_imin = Operand::Immediate(DataWord::Word32(i32::MIN as u32));
        let imm_16 = Operand::Immediate(DataWord::Word32(16));
        let imm_minus70 = Operand::Immediate(DataWord::Word32(-70i32 as u32));

        // Test simple sub
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 26);

        // Test sub with same operand and destination
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: r0.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 10);

        // Test sub with negative number
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus70.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 112);

        // Test sub underflow
        let operation = Operation::Sub {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_imin.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, ((i32::MIN) as u32 + 42) as u64);
    }

    #[test]
    fn test_mul() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

        let r0 = Operand::Register("R0".to_owned());
        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_minus_42 = Operand::Immediate(DataWord::Word32(-42i32 as u32));
        let imm_16 = Operand::Immediate(DataWord::Word32(16));
        let imm_minus_16 = Operand::Immediate(DataWord::Word32(-16i32 as u32));

        // simple multiplication
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 672);

        // multiplication right minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_42.clone(),
            operand2: imm_minus_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value as u32, -672i32 as u32);

        // multiplication left minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_minus_42.clone(),
            operand2: imm_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value as u32, -672i32 as u32);

        // multiplication both minus
        let operation = Operation::Mul {
            destination: r0.clone(),
            operand1: imm_minus_42.clone(),
            operand2: imm_minus_16.clone(),
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 672);
    }

    #[test]
    fn test_set_v_flag() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

        let imm_42 = Operand::Immediate(DataWord::Word32(42));
        let imm_12 = Operand::Immediate(DataWord::Word32(12));
        let imm_imin = Operand::Immediate(DataWord::Word32(i32::MIN as u32));
        let imm_imax = Operand::Immediate(DataWord::Word32(i32::MAX as u32));

        // no overflow
        let operation = Operation::SetVFlag {
            operand1: imm_42.clone(),
            operand2: imm_12.clone(),
            sub: true,
            carry: false,
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(!v_flag);

        // overflow
        let operation = Operation::SetVFlag {
            operand1: imm_imax.clone(),
            operand2: imm_12.clone(),
            sub: false,
            carry: false,
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(v_flag);

        // underflow
        let operation = Operation::SetVFlag {
            operand1: imm_imin.clone(),
            operand2: imm_12.clone(),
            sub: true,
            carry: false,
        };
        executor.execute_operation(&operation, &mut NoLogger).ok();

        let v_flag = executor.state.get_flag("V".to_owned()).unwrap().get_constant_bool().unwrap();
        assert!(v_flag);
    }

    #[test]
    fn test_conditional_execution() {
        let mut vm = setup_test_vm();
        let project = vm.project;
        let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);
        let imm_0 = Operand::Immediate(DataWord::Word32(0));
        let imm_1 = Operand::Immediate(DataWord::Word32(1));
        let r0 = Operand::Register("R0".to_owned());

        let program1 = vec![
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::SetZFlag(imm_0.clone())],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::ConditionalExecution {
                    conditions: vec![Condition::EQ, Condition::NE],
                }],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::Move {
                    destination: r0.clone(),
                    source: imm_1,
                }],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
            Instruction {
                instruction_size: 32,
                operations: vec![Operation::Move {
                    destination: r0.clone(),
                    source: imm_0,
                }],
                max_cycle: CycleCount::Value(0),
                memory_access: false,
            },
        ];

        for p in program1 {
            executor.execute_instruction(&p, &mut NoLogger).ok();
        }

        let r0_value = executor.get_operand_value(&r0, &mut NoLogger).ok().unwrap().get_constant().unwrap();
        assert_eq!(r0_value, 1);
    }

    #[test]
    #[should_panic]
    fn test_any() {
        let bw = Z3Solver::new();
        let a_word = bw.unconstrained(32, "a_word");
        a_word.get_constant().unwrap();
    }
}
