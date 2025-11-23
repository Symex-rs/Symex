use std::{fmt::Display, marker::PhantomData, rc::Rc};

use anyhow::Context as _;
use bitwuzla::{Array, Btor, BV};
use general_assembly::extension::ieee754::{OperandType, RoundingMode};
use hashbrown::HashMap;

use super::{expr::BitwuzlaExpr, fpexpr::FpExpr, Bitwuzla};
use crate::{
    executor::ResultOrTerminate,
    memory::{MemoryError, BITS_IN_BYTE},
    project::Project,
    smt::{Context, ProgramMemory, SmtExpr, SmtFPExpr, SmtMap, SmtSolver},
    trace, warn, Endianness, UserStateContainer,
};

#[derive(Debug, Clone)]
#[must_use]
pub struct ArrayMemory {
    /// Reference to the context so new symbols can be created.
    pub ctx: Rc<Btor>,

    /// Size of a pointer.
    ptr_size: u32,

    /// The actual memory. Stores all values written to memory.
    memory: Array<Rc<Btor>>,

    /// Memory endianness
    endianness: Endianness,
}

impl ArrayMemory {
    pub fn resolve_addresses(&self, addr: &BitwuzlaExpr, _upper_bound: u32) -> Result<Vec<BitwuzlaExpr>, MemoryError> {
        Ok(vec![addr.clone()])
    }

    pub fn read(&self, addr: &BitwuzlaExpr, bits: u32) -> Result<BitwuzlaExpr, MemoryError> {
        assert_eq!(addr.size(), self.ptr_size, "passed wrong sized address");

        let value = self.internal_read(addr, bits, self.ptr_size);
        Ok(value)
    }

    pub fn write(&mut self, addr: &BitwuzlaExpr, value: BitwuzlaExpr) {
        assert_eq!(addr.size(), self.ptr_size, "passed wrong sized address");
        self.internal_write(addr, value, self.ptr_size);
    }

    /// Creates a new memory containing only uninitialized memory.
    pub fn new(ctx: Rc<bitwuzla::Bitwuzla>, ptr_size: u32, endianness: Endianness) -> Self {
        let memory = Array::new(ctx.clone(), ptr_size as u64, BITS_IN_BYTE as u64, Some("memory"));

        Self {
            ctx,
            ptr_size,
            memory,
            endianness,
        }
    }

    /// Reads an u8 from the given address.
    fn read_u8(&self, addr: &BitwuzlaExpr) -> BitwuzlaExpr {
        BitwuzlaExpr(self.memory.read(&addr.0))
    }

    /// Writes an u8 value to the given address.
    fn write_u8(&mut self, addr: &BitwuzlaExpr, val: &BitwuzlaExpr) {
        self.memory = self.memory.write(&addr.0, &val.0);
    }

    /// Reads `bits` from `addr`.
    ///
    /// If the number of bits are less than `BITS_IN_BYTE` then individual bits
    /// can be read, but if the number of bits exceed `BITS_IN_BYTE` then
    /// full bytes must be read.
    fn internal_read(&self, addr: &BitwuzlaExpr, bits: u32, ptr_size: u32) -> BitwuzlaExpr {
        let value = if bits < BITS_IN_BYTE {
            self.read_u8(addr).slice(0, bits - 1)
        } else {
            // Ensure we only read full bytes now.
            assert_eq!(bits % BITS_IN_BYTE, 0, "Must read bytes, if bits >= 8");
            let num_bytes = bits / BITS_IN_BYTE;

            let mut bytes = Vec::new();

            for byte in 0..num_bytes {
                let offset = BitwuzlaExpr(BV::from_u64(self.ctx.clone(), byte as u64, ptr_size as u64));
                let read_addr = addr.add(&offset);
                let value = self.read_u8(&read_addr);
                bytes.push(value);
            }

            match self.endianness {
                Endianness::Little => bytes.into_iter().reduce(|acc, v| v.concat(&acc)).unwrap(),
                Endianness::Big => bytes.into_iter().rev().reduce(|acc, v| v.concat(&acc)).unwrap(),
            }
        };

        value
    }

    fn internal_write(&mut self, addr: &BitwuzlaExpr, value: BitwuzlaExpr, ptr_size: u32) {
        // Check if we should zero extend the value (if it less than 8-bits).
        let value = if value.size() < BITS_IN_BYTE { value.zero_ext(BITS_IN_BYTE) } else { value };

        trace!("Value {:?} len : {}", value, value.size());
        // Ensure the value we write is a multiple of `BITS_IN_BYTE`.
        assert_eq!(value.size() % BITS_IN_BYTE, 0);

        let num_bytes = value.size() / BITS_IN_BYTE;
        for n in 0..num_bytes {
            let low_bit = n * BITS_IN_BYTE;
            let high_bit = (n + 1) * BITS_IN_BYTE - 1;
            let byte = value.slice(low_bit, high_bit);

            let offset = match self.endianness {
                Endianness::Little => BitwuzlaExpr(BV::from_u64(self.ctx.clone(), n as u64, ptr_size as u64)),
                Endianness::Big => BitwuzlaExpr(BV::from_u64(self.ctx.clone(), (num_bytes - 1 - n) as u64, ptr_size as u64)),
            };
            let addr = addr.add(&offset);
            self.write_u8(&addr, &byte);
        }
    }
}

impl Context for ArrayMemory {
    type Expr = BitwuzlaExpr;

    fn new_from_u64(&self, val: u64, bits: u32) -> Self::Expr {
        BitwuzlaExpr(BV::from_u64(self.ctx.clone(), val & ((1u128 << bits) - 1) as u64, bits as u64))
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "exact", allow(dead_code))]
pub struct BitwuzlaMemory<State: UserStateContainer> {
    pub(crate) ram: ArrayMemory,
    register_file: HashMap<String, BitwuzlaExpr>,
    flags: HashMap<String, BitwuzlaExpr>,
    variables: HashMap<String, BitwuzlaExpr>,
    fp_variables: HashMap<String, FpExpr>,
    fp_registers: HashMap<String, FpExpr>,
    program_memory: std::sync::Arc<Project<Bitwuzla>>,
    word_size: u32,
    pc: u64,
    initial_sp: BitwuzlaExpr,
    static_writes: HashMap<u64, BitwuzlaExpr>,
    cycles: u64,
    _0: PhantomData<State>,
}

impl<State: UserStateContainer> SmtMap for BitwuzlaMemory<State> {
    type Expression = BitwuzlaExpr;
    type ProgramMemory = std::sync::Arc<Project<Bitwuzla>>;
    type SMT = Bitwuzla;
    type StateContainer = State;

    fn new<O: crate::arch::ArchitectureOverride>(
        smt: Self::SMT,
        program_memory: Self::ProgramMemory,
        endianness: Endianness,
        initial_sp: Self::Expression,
        _state: &Self::StateContainer,
        arch: &crate::arch::SupportedArchitecture<O>,
    ) -> Result<Self, crate::GAError> {
        let ram = {
            let memory = Array::new(smt.ctx.clone(), arch.word_size(), BITS_IN_BYTE as u64, Some("memory"));

            ArrayMemory {
                ctx: smt.ctx,
                ptr_size: arch.word_size() as u32,
                memory,
                endianness,
            }
        };
        Ok(Self {
            ram,
            register_file: HashMap::new(),
            fp_registers: HashMap::new(),
            flags: HashMap::new(),
            variables: HashMap::new(),
            fp_variables: HashMap::new(),
            program_memory,
            word_size: arch.word_size() as u32,
            pc: 0,
            initial_sp,
            static_writes: HashMap::new(),
            cycles: 0,
            _0: PhantomData,
        })
    }

    fn get(&mut self, idx: &Self::Expression, size: u32) -> ResultOrTerminate<Self::Expression> {
        if let Some(address) = idx.get_constant() {
            if !self.program_memory.address_in_range(address) {
                trace!("Got deterministic address ({address:#x}) from ram");
                return ResultOrTerminate::Result(
                    self.ram
                        .read(idx, size)
                        .context("While reading from a non constant address pointing in to the symbols memory"),
                );
            }
            trace!("Got deterministic address ({address:#x}) from project");
            return ResultOrTerminate::Result(
                self.program_memory
                    .get(address, size, &self.static_writes, &self.ram)
                    .context("While reading from program memory"),
            );
        }
        trace!("Got NON deterministic address {idx:?} from ram");
        ResultOrTerminate::Result(self.ram.read(idx, size).context("While reading from a non constant address pointing to symbolic memory"))
    }

    fn set(&mut self, idx: &Self::Expression, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        if let Some(address) = idx.get_constant() {
            if self.program_memory.address_in_range(address) {
                assert!(value.size() % 8 == 0, "Value must be a multiple of 8 bits to be written to program memory");
                let _ = self.program_memory.set(address, value, &mut self.static_writes, &mut self.ram);
                return Ok(());
            }
        }
        self.ram.write(idx, value);
        Ok(())
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
        self.register_file.insert(idx.to_string(), value);
        Ok(())
    }

    #[cfg(not(feature = "bitwuzla-exact-fp"))]
    fn set_fp_register(&mut self, idx: &str, value: <Self::SMT as SmtSolver>::FpExpression, _rm: RoundingMode, _signed: bool) -> Result<(), crate::smt::MemoryError> {
        self.fp_registers.insert(idx.to_string(), value);
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
        Ok(ret)
    }

    #[cfg(not(feature = "bitwuzla-exact-fp"))]
    fn get_fp_register(
        &mut self,
        idx: &str,
        source_ty: OperandType,
        _dest_ty: OperandType,
        _rm: RoundingMode,
        _signed: bool,
    ) -> Result<<Self::SMT as SmtSolver>::FpExpression, crate::smt::MemoryError> {
        let ret = match self.fp_registers.get(idx) {
            Some(val) => val.clone(),
            None => {
                let ret = self.unconstrained_fp(source_ty, idx);
                self.fp_registers.insert(idx.to_owned(), ret.clone());
                ret
            }
        };
        if self.variables.get(idx).is_none() {
            self.fp_variables.insert(idx.to_owned(), ret.clone());
        }
        Ok(ret)
    }

    fn from_u64(&self, value: u64, size: u32) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width value");
        BitwuzlaExpr(BV::from_u64(self.ram.ctx.clone(), value & ((1u128 << size) - 1) as u64, size as u64))
    }

    #[allow(clippy::wrong_self_convention)]
    /// Create a new expression from an `u64` value of size `size`.
    fn from_f64(&mut self, value: f64, rm: RoundingMode, ty: OperandType) -> crate::Result<<Self::SMT as SmtSolver>::FpExpression> {
        let size = match ty {
            OperandType::Binary16 => 16,
            OperandType::Binary32 => 32,
            OperandType::Binary64 => 64,
            OperandType::Binary128 => 128,
            OperandType::Integral { size, signed: _ } => size,
        };
        let value = match ty {
            OperandType::Binary16 => {
                todo!("No support in the rust compiler for binary16");
            }
            OperandType::Binary32 => {
                let value = u64::from((value as f32).to_bits());
                self.from_u64(value, size)
            }
            OperandType::Binary64 => {
                let value = (value).to_bits();
                self.from_u64(value, size)
            }
            OperandType::Binary128 => {
                todo!("TODO! Represent 128 bit numbers");
            }
            OperandType::Integral { size: _, signed: _ } => panic!("Cannot create fp expression from binary"),
        };
        let source_ty = match ty.clone() {
            OperandType::Integral { size: _, signed: _ } => panic!("Cannot create fp expression from binary"),
            t => t,
        };

        value.to_fp(source_ty, ty, rm, true)
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        BitwuzlaExpr(BV::from_bool(self.ram.ctx.clone(), value))
    }

    fn unconstrained(&mut self, name: &str, size: u32) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width unconstrained value");
        let ret = BV::new(self.ram.ctx.clone(), size as u64, Some(name));
        let ret = BitwuzlaExpr(ret);
        let ret = ret.resize_unsigned(size);
        if !self.variables.contains_key(name) {
            trace!("Added a named variabled");
            self.variables.insert(name.to_string(), ret.clone());
        }
        warn!("New unconstrained value {name} = {ret:?}");
        ret
    }

    fn unconstrained_unnamed(&mut self, size: u32) -> Self::Expression {
        assert!(size != 0, "Tried to create a 0 width unconstrained value");
        let ret = BV::new(self.ram.ctx.clone(), size as u64, None);
        let ret = BitwuzlaExpr(ret);
        let _ = ret.resize_unsigned(size);
        ret
    }

    fn unconstrained_fp_unnamed(&mut self, ty: general_assembly::extension::ieee754::OperandType) -> <Self::SMT as crate::smt::SmtSolver>::FpExpression {
        FpExpr::unconstrained(self.ram.ctx.clone(), &ty, None)
    }

    fn unconstrained_fp(&mut self, ty: general_assembly::extension::ieee754::OperandType, name: &str) -> <Self::SMT as crate::smt::SmtSolver>::FpExpression {
        let expr = FpExpr::unconstrained(self.ram.ctx.clone(), &ty, None);
        if !self.fp_variables.contains_key(name) {
            trace!("Added a named variabled");
            self.fp_variables.insert(name.to_string(), expr.clone());
        }
        expr
    }

    fn get_ptr_size(&self) -> u32 {
        self.program_memory.get_ptr_size()
    }

    fn get_from_instruction_memory(&self, address: u64) -> crate::Result<Vec<u8>> {
        warn!("Reading instruction from memory");
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
        self.ram.ctx.is_sat()
    }

    fn with_model_gen<R, F: FnOnce() -> R>(&self, f: F) -> R {
        f()
    }

    fn get_cycle_count(&mut self) -> u64 {
        self.cycles
    }

    fn set_cycle_count(&mut self, value: u64) {
        self.cycles = value;
    }

    fn get_registers(&mut self) -> HashMap<String, Self::Expression> {
        self.register_file.clone()
    }
}

impl<State: UserStateContainer> Display for BitwuzlaMemory<State> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Variables:\r\n")?;
        for (key, value) in &self.variables {
            // In reality, this should probably be a flag to cargo-symex or so...
            #[cfg(feature = "verbose-results")]
            write!(
                f,
                "\t\t{key} :\t {}\r\n",
                match value.get_constant() {
                    Some(_value) => {
                        format!("Constant: 0b{}", value.to_binary_string())
                    }
                    _ => {
                        format!("Solution: {}\n\t\t\t Expression: {}", value.to_binary_string(), strip(format!("{value:?}")))
                    }
                }
            )?;
            #[cfg(not(feature = "verbose-results"))]
            write!(
                f,
                "\t\t{key} : {}\r\n",
                match value.get_constant() {
                    Some(_value) => value.to_binary_string(),
                    _ => strip(format!("{value:?}")),
                }
            )?;
        }
        f.write_str("\tFP Variables:\r\n")?;
        for (key, value) in &self.fp_variables {
            write!(
                f,
                "\t\t{key} : {}\r\n",
                match value.get_const() {
                    Some(value) => value.to_string(),
                    _ => strip(format!("{value:?}")),
                }
            )?;
        }
        f.write_str("\tRegister file:\r\n")?;
        for (key, value) in &self.register_file {
            #[cfg(feature = "verbose-results")]
            write!(
                f,
                "\t\t{key} :\t {}\r\n",
                match value.get_constant() {
                    Some(_value) => format!("Constant: 0b{}", value.to_binary_string()),
                    _ => format!("Solution: {}\n\t\t\t Expression: {}", value.to_binary_string(), strip(format!("{value:?}"))),
                }
            )?;
            #[cfg(not(feature = "verbose-results"))]
            write!(
                f,
                "\t\t{key} : {}\r\n",
                match value.get_constant() {
                    Some(_value) => value.to_binary_string(),
                    _ => strip(format!("{value:?}")),
                }
            )?;
        }
        f.write_str("\tFlags:\r\n")?;

        for (key, value) in &self.flags {
            write!(
                f,
                "\t\t{key} : {}\r\n",
                match value.get_constant() {
                    Some(_value) => value.to_binary_string(),
                    _ => strip(format!("{value:?}")),
                }
            )?;
        }
        Ok(())
    }
}

fn strip(s: String) -> String {
    #[cfg(not(feature = "verbose-results"))]
    if 50 < s.len() {
        return "Large symbolic expression".to_string();
    }
    #[cfg(feature = "verbose-results")]
    if 100 < s.len() {
        return "Large symbolic expression".to_string();
    }
    s
}
