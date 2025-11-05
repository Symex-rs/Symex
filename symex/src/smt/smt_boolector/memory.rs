//! Theories-of-array memory.
//!
//! This memory model uses theories-of-arrays and supports arbitrary read and
//! writes with symbolic values. It uses a linear address space which is byte
//! addressable. A single write will split the symbolic value into byte sized
//! chunks, and write each individually into memory. A read will concatenate
//! multiple bytes into a single large symbol.
//!
//! The concatenation on reads will generate more complex expressions compared
//! to other memory models, and in general this memory model is slower compared
//! to e.g. object memory. However, it may provide better performance in certain
//! situations.
use std::{fmt::Display, marker::PhantomData, sync::Arc};

use anyhow::Context as _;
use hashbrown::HashMap;

use crate::{
    executor::ResultOrTerminate,
    memory::{MemoryError, BITS_IN_BYTE},
    project::Project,
    smt::{
        smt_boolector::{Boolector, DArray, DContext, DExpr},
        Context,
        ProgramMemory,
        SmtExpr,
        SmtMap,
    },
    trace,
    Endianness,
    UserStateContainer,
};

#[derive(Debug, Clone)]
pub struct ArrayMemory {
    /// Reference to the context so new symbols can be created.
    ctx: &'static DContext,

    /// Size of a pointer.
    ptr_size: u32,

    /// The actual memory. Stores all values written to memory.
    memory: DArray,

    /// Memory endianness
    endianness: Endianness,
}

impl Context for &'static DContext {
    type Expr = DExpr;

    fn new_from_u64(&self, val: u64, bits: u32) -> Self::Expr {
        self.from_u64(val, bits)
    }
}

impl ArrayMemory {
    #[tracing::instrument(skip(self))]
    fn read(&self, addr: &DExpr, bits: u32) -> Result<DExpr, MemoryError> {
        assert_eq!(addr.len(), self.ptr_size, "passed wrong sized address");

        let value = self.internal_read(addr, bits, self.ptr_size);
        trace!("Read value: {value:?}");
        Ok(value)
    }

    #[tracing::instrument(skip(self))]
    fn write(&mut self, addr: &DExpr, value: DExpr) -> Result<(), MemoryError> {
        assert_eq!(addr.len(), self.ptr_size, "passed wrong sized address");
        self.internal_write(addr, value, self.ptr_size);
        Ok(())
    }

    #[must_use]
    #[cfg(test)]
    /// Creates a new memory containing only uninitialized memory.
    fn new(ctx: &'static DContext, ptr_size: u32, endianness: Endianness) -> Self {
        let memory = DArray::new(ctx, ptr_size, BITS_IN_BYTE, "memory");

        Self {
            ctx,
            ptr_size,
            memory,
            endianness,
        }
    }

    /// Reads an u8 from the given address.
    fn read_u8(&self, addr: &DExpr) -> DExpr {
        self.memory.read(addr)
    }

    /// Writes an u8 value to the given address.
    fn write_u8(&mut self, addr: &DExpr, val: &DExpr) {
        self.memory.write(addr, val);
    }

    /// Reads `bits` from `addr`.
    ///
    /// If the number of bits are less than `BITS_IN_BYTE` then individual bits
    /// can be read, but if the number of bits exceed `BITS_IN_BYTE` then
    /// full bytes must be read.
    fn internal_read(&self, addr: &DExpr, bits: u32, ptr_size: u32) -> DExpr {
        let value = if bits < BITS_IN_BYTE {
            self.read_u8(addr).slice(bits - 1, 0)
        } else {
            // Ensure we only read full bytes now.
            assert_eq!(bits % BITS_IN_BYTE, 0, "Must read bytes, if bits >= 8");
            let num_bytes = bits / BITS_IN_BYTE;

            let mut bytes = Vec::new();

            for byte in 0..num_bytes {
                let offset = self.ctx.from_u64(byte as u64, ptr_size);
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

    fn internal_write(&mut self, addr: &DExpr, value: DExpr, ptr_size: u32) {
        // Check if we should zero extend the value (if it less than 8-bits).
        let value = if value.len() < BITS_IN_BYTE { value.zero_ext(BITS_IN_BYTE) } else { value };

        // Ensure the value we write is a multiple of `BITS_IN_BYTE`.
        assert_eq!(value.len() % BITS_IN_BYTE, 0);

        let num_bytes = value.len() / BITS_IN_BYTE;
        for n in 0..num_bytes {
            let low_bit = n * BITS_IN_BYTE;
            let high_bit = (n + 1) * BITS_IN_BYTE - 1;
            let byte = value.slice(low_bit, high_bit);

            let offset = match self.endianness {
                Endianness::Little => self.ctx.from_u64(n as u64, ptr_size),
                Endianness::Big => self.ctx.from_u64((num_bytes - 1 - n) as u64, ptr_size),
            };
            let addr = addr.add(&offset);
            self.write_u8(&addr, &byte);
        }
    }
}

#[derive(Debug, Clone)]
pub struct BoolectorMemory<State: UserStateContainer> {
    ram: ArrayMemory,
    register_file: HashMap<String, DExpr>,
    flags: HashMap<String, DExpr>,
    variables: HashMap<String, DExpr>,
    program_memory: Arc<Project<Boolector>>,
    word_size: u32,
    pc: u64,
    initial_sp: DExpr,
    un_named_counter: usize,
    static_writes: HashMap<u64, DExpr>,
    cycles: u64,
    _0: PhantomData<State>,
}

impl<State: UserStateContainer> SmtMap for BoolectorMemory<State> {
    type Expression = DExpr;
    type ProgramMemory = Arc<Project<Boolector>>;
    type SMT = Boolector;
    type StateContainer = State;

    fn new<O: crate::arch::ArchitectureOverride>(
        smt: Self::SMT,
        program_memory: Self::ProgramMemory,
        endianness: Endianness,
        initial_sp: Self::Expression,
        _state: &Self::StateContainer,
        arch: &crate::arch::SupportedArchitecture<O>,
    ) -> Result<Self, crate::GAError> {
        let ctx = Box::new(crate::smt::smt_boolector::BoolectorSolverContext { ctx: smt.ctx.clone() });
        let ctx = Box::leak::<'static>(ctx);
        let ram = {
            let memory = DArray::new(
                &crate::smt::smt_boolector::BoolectorSolverContext { ctx: smt.ctx },
                arch.word_size() as u32,
                BITS_IN_BYTE,
                "memory",
            );

            ArrayMemory {
                ctx,
                ptr_size: arch.ptr_size() as u32,
                memory,
                endianness,
            }
        };
        Ok(Self {
            ram,
            register_file: HashMap::new(),
            flags: HashMap::new(),
            variables: HashMap::new(),
            program_memory,
            word_size: arch.word_size() as u32,
            pc: 0,
            initial_sp,
            un_named_counter: 0,
            static_writes: HashMap::new(),
            cycles: 0,
            _0: PhantomData,
        })
    }

    fn get(&mut self, idx: &Self::Expression, size: u32) -> ResultOrTerminate<Self::Expression> {
        if let Some(address) = idx.get_constant() {
            if !self.program_memory.address_in_range(address) {
                trace!("Got deterministic address ({address:#x}) from ram");
                return ResultOrTerminate::Result(self.ram.read(idx, size).context("While reading from a constant address from symbol memory"));
            }
            trace!("Got deterministic address ({address:#x}) from project");
            return ResultOrTerminate::Result(
                self.program_memory
                    .get(address, size, &self.static_writes, &self.ram.ctx)
                    .context("While reading from program memory"),
            );
        }
        trace!("Got NON deterministic address {idx:?} from ram");
        ResultOrTerminate::Result(self.ram.read(idx, size).context("While reading from memory"))
    }

    fn set(&mut self, idx: &Self::Expression, value: Self::Expression) -> Result<(), crate::smt::MemoryError> {
        if let Some(address) = idx.get_constant() {
            if self.program_memory.address_in_range(address) {
                assert!(value.size() % 8 == 0, "Value must be a multiple of 8 bits to be written to program memory");
                let _ = self.program_memory.set(address, value, &mut self.static_writes, &mut self.ram.ctx);
                return Ok(());
            }
        }
        Ok(self.ram.write(idx, value)?)
    }

    fn get_pc(&self) -> Result<Self::Expression, crate::smt::MemoryError> {
        Ok(self.ram.ctx.from_u64(self.pc, 32))
    }

    fn set_pc(&mut self, value: u32) -> Result<(), crate::smt::MemoryError> {
        self.pc = value as u64;
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
        self.register_file.insert(idx.to_string(), value);
        Ok(())
    }

    fn get_register(&mut self, idx: &str) -> Result<Self::Expression, crate::smt::MemoryError> {
        trace!("Looking for {idx} in  {:?} -> {:?}", self.register_file, self.register_file.get(idx));
        let ret = match self.register_file.get(idx) {
            Some(val) => val.clone(),
            None => {
                trace!("Did not find it.. :(");
                let ret = self.unconstrained(idx, self.word_size);
                self.register_file.insert(idx.to_owned(), ret.clone());
                ret
            }
        };
        if self.variables.get(idx).is_none() {
            self.variables.insert(idx.to_owned(), ret.clone());
        }
        //trace!("{idx} had no hooks");
        // Ensure that any read from the same register returns the
        //self.register_file.get(idx);
        trace!("{idx} Got value from register");
        Ok(ret)
    }

    #[allow(clippy::cast_possible_truncation)]
    fn from_u64(&self, value: u64, size: u32) -> Self::Expression {
        self.ram.ctx.from_u64(value, size)
    }

    fn from_bool(&self, value: bool) -> Self::Expression {
        self.ram.ctx.from_bool(value)
    }

    #[allow(clippy::cast_possible_truncation)]
    fn unconstrained(&mut self, name: &str, size: u32) -> Self::Expression {
        let ret = self.ram.ctx.unconstrained(size, Some(name));
        if !self.variables.contains_key(name) {
            self.variables.insert(name.to_string(), ret.clone());
        }
        ret
    }

    #[allow(clippy::cast_possible_truncation)]
    fn unconstrained_unnamed(&mut self, size: u32) -> Self::Expression {
        let ret = self.ram.ctx.unconstrained(size, Some(&format!("UnNamed{}", self.un_named_counter)));
        self.un_named_counter += 1;
        ret
    }

    fn get_ptr_size(&self) -> u32 {
        self.program_memory.get_ptr_size()
    }

    fn get_from_instruction_memory(&self, address: u64) -> crate::Result<Vec<u8>> {
        Ok(self.program_memory.get_raw_word(address)?)
    }

    fn get_stack(&mut self) -> (Self::Expression, Self::Expression) {
        // TODO: Make this more generic.
        let current = self.register_file.get("SP").expect("Register pointer SP not found.");
        (self.initial_sp.clone(), current.clone())
    }

    fn clear_named_variables(&mut self) {
        self.variables.clear();
    }

    fn program_memory(&self) -> &Self::ProgramMemory {
        &self.program_memory
    }

    fn is_sat(&self) -> bool {
        match self.ram.ctx.ctx.0.sat() {
            boolector::SolverResult::Sat => true,
            _ => false,
        }
    }

    fn with_model_gen<R, F: FnOnce() -> R>(&self, f: F) -> R {
        self.ram.ctx.ctx.0.set_opt(boolector::option::BtorOption::ModelGen(boolector::option::ModelGen::All));
        let ret = f();
        self.ram.ctx.ctx.0.set_opt(boolector::option::BtorOption::ModelGen(boolector::option::ModelGen::Disabled));
        ret
    }

    fn get_cycle_count(&mut self) -> u64 {
        self.cycles
    }

    fn set_cycle_count(&mut self, value: u64) {
        self.cycles = value;
    }

    fn unconstrained_fp_unnamed(&mut self, ty: general_assembly::extension::ieee754::OperandType) -> <Self::SMT as crate::smt::SmtSolver>::FpExpression {
        (self.ram.ctx.unconstrained(ty.size(), None), ty)
    }

    fn unconstrained_fp(&mut self, ty: general_assembly::extension::ieee754::OperandType, name: &str) -> <Self::SMT as crate::smt::SmtSolver>::FpExpression {
        (self.ram.ctx.unconstrained(ty.size(), Some(name)), ty)
    }

    fn get_registers(&mut self) -> HashMap<String, Self::Expression> {
        self.register_file.clone()
    }
}

impl<State: UserStateContainer> Display for BoolectorMemory<State> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\tVariables:\r\n")?;
        for (key, value) in &self.variables {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => format!("{} (Other values possible)", value.get_as_symbolic_trinary_string()),
            })?;
        }
        f.write_str("\tRegister file:\r\n")?;
        for (key, value) in &self.register_file {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => format!("{} (Other values possible)", value.get_as_symbolic_trinary_string()),
            })?;
        }
        f.write_str("\tFlags:\r\n")?;

        for (key, value) in &self.flags {
            write!(f, "\t\t{key} : {}\r\n", match value.get_constant() {
                Some(_value) => value.to_binary_string(),
                _ => format!("{} (Other values possible)", value.get_as_symbolic_trinary_string()),
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::ArrayMemory;
    use crate::{smt::smt_boolector::DContext, Endianness};

    fn setup_test_memory(endianness: Endianness) -> ArrayMemory {
        let ctx = Box::new(DContext::new());
        let ctx = Box::leak(ctx);
        ArrayMemory::new(ctx, 32, endianness)
    }

    #[test]
    fn test_little_endian_write() {
        let mut memory = setup_test_memory(Endianness::Little);
        let indata = memory.ctx.from_u64(0x0102_0304, 32);
        let addr = memory.ctx.from_u64(0, 32);
        let one = memory.ctx.from_u64(1, 32);
        memory.write(&addr, indata).ok();
        let b1 = memory.read_u8(&addr);
        let addr = addr.add(&one);
        let b2 = memory.read_u8(&addr);
        let addr = addr.add(&one);
        let b3 = memory.read_u8(&addr);
        let addr = addr.add(&one);
        let b4 = memory.read_u8(&addr);

        assert_eq!(b1.get_constant().unwrap(), 0x04);
        assert_eq!(b2.get_constant().unwrap(), 0x03);
        assert_eq!(b3.get_constant().unwrap(), 0x02);
        assert_eq!(b4.get_constant().unwrap(), 0x01);
    }

    #[test]
    fn test_big_endian_write() {
        let mut memory = setup_test_memory(Endianness::Big);
        let indata = memory.ctx.from_u64(0x0102_0304, 32);
        let addr = memory.ctx.from_u64(0, 32);
        let one = memory.ctx.from_u64(1, 32);
        memory.write(&addr, indata).ok();
        let b1 = memory.read_u8(&addr);
        let addr = addr.add(&one);
        let b2 = memory.read_u8(&addr);
        let addr = addr.add(&one);
        let b3 = memory.read_u8(&addr);
        let addr = addr.add(&one);
        let b4 = memory.read_u8(&addr);

        assert_eq!(b1.get_constant().unwrap(), 0x01);
        assert_eq!(b2.get_constant().unwrap(), 0x02);
        assert_eq!(b3.get_constant().unwrap(), 0x03);
        assert_eq!(b4.get_constant().unwrap(), 0x04);
    }

    #[test]
    fn test_little_endian_read() {
        let mut memory = setup_test_memory(Endianness::Little);
        let b1 = memory.ctx.from_u64(0x04, 8);
        let b2 = memory.ctx.from_u64(0x03, 8);
        let b3 = memory.ctx.from_u64(0x02, 8);
        let b4 = memory.ctx.from_u64(0x01, 8);

        let one = memory.ctx.from_u64(1, 32);
        let addr = memory.ctx.from_u64(0, 32);
        memory.write_u8(&addr, &b1);
        let addr = addr.add(&one);
        memory.write_u8(&addr, &b2);
        let addr = addr.add(&one);
        memory.write_u8(&addr, &b3);
        let addr = addr.add(&one);
        memory.write_u8(&addr, &b4);

        let addr = memory.ctx.from_u64(0, 32);
        let result = memory.read(&addr, 32).ok().unwrap();
        assert_eq!(result.get_constant().unwrap(), 0x0102_0304);
    }

    #[test]
    fn test_big_endian_read() {
        let mut memory = setup_test_memory(Endianness::Big);
        let b1 = memory.ctx.from_u64(0x01, 8);
        let b2 = memory.ctx.from_u64(0x02, 8);
        let b3 = memory.ctx.from_u64(0x03, 8);
        let b4 = memory.ctx.from_u64(0x04, 8);

        let one = memory.ctx.from_u64(1, 32);
        let addr = memory.ctx.from_u64(0, 32);
        memory.write_u8(&addr, &b1);
        let addr = addr.add(&one);
        memory.write_u8(&addr, &b2);
        let addr = addr.add(&one);
        memory.write_u8(&addr, &b3);
        let addr = addr.add(&one);
        memory.write_u8(&addr, &b4);

        let addr = memory.ctx.from_u64(0, 32);
        let result = memory.read(&addr, 32).ok().unwrap();
        assert_eq!(result.get_constant().unwrap(), 0x0102_0304);
    }
}
