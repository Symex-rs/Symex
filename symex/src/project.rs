use std::fmt::Debug;

use dwarf_helper::SubProgramMap;
use general_assembly::prelude::{DataHalfWord, DataWord};
use hashbrown::HashMap;
use object::Object;
use segments::Segments;

use crate::{
    arch::ArchError,
    memory::MemoryError,
    smt::{sealed::Context, ProgramMemory, SmtExpr, SmtMap, SmtSolver},
    Composition,
    Endianness,
    WordSize,
};

pub mod dwarf_helper;
pub mod segments;

pub type Result<T> = std::result::Result<T, ProjectError>;

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum ProjectError {
    #[error("Unable to parse elf file: {0}")]
    UnableToParseElf(String),

    #[error("Program memory error")]
    ProgrammemoryError(#[from] MemoryError),

    #[error("Unavalable operation")]
    UnabvalableOperation,

    #[error("Architecture specific error {0}")]
    ArchError(#[from] ArchError),

    #[error("Unable to find entry point at address: {0}")]
    InvalidSymbolAddress(u64),

    #[error("Unable to find entry point: {0}")]
    InvalidSymbol(&'static str),
}

/// Holds all data read from the ELF file.
/// Add all read only memory here later to handle global constants.
pub struct Project {
    segments: Segments,
    word_size: WordSize,
    endianness: Endianness,
    symtab: SubProgramMap,
}

impl Project {
    pub fn manual_project(program_memory: Vec<u8>, start_addr: u64, end_addr: u64, word_size: WordSize, endianness: Endianness, _symtab: HashMap<String, u64>) -> Project {
        Project {
            segments: Segments::from_single_segment(program_memory, start_addr, end_addr, false),
            word_size,
            endianness,
            symtab: SubProgramMap::default(),
        }
    }

    pub fn from_binary(obj_file: object::File<'_>, symtab: SubProgramMap) -> Result<Self> {
        let segments = Segments::from_file(&obj_file);
        let endianness = if obj_file.is_little_endian() { Endianness::Little } else { Endianness::Big };

        // Do not catch 16 or 8 bit architectures but will do for now.
        let word_size = if obj_file.is_64() { WordSize::Bit64 } else { WordSize::Bit32 };

        Ok(Project {
            segments,
            word_size,
            endianness,
            symtab,
        })
    }

    fn get_word_internal(&self, address: u64, width: WordSize) -> Result<DataWord> {
        Ok(match width {
            WordSize::Bit64 => match self.segments.read_raw_bytes(address, 8) {
                Some(v) => {
                    let mut data = [0; 8];
                    data.copy_from_slice(&v);
                    DataWord::Word64(match self.endianness {
                        Endianness::Little => u64::from_le_bytes(data),
                        Endianness::Big => u64::from_be_bytes(data),
                    })
                }
                None => {
                    return Err(MemoryError::OutOfBounds.into());
                }
            },
            WordSize::Bit32 => match self.segments.read_raw_bytes(address, 4) {
                Some(v) => {
                    let mut data = [0; 4];
                    data.copy_from_slice(&v);
                    DataWord::Word32(match self.endianness {
                        Endianness::Little => u32::from_le_bytes(data),
                        Endianness::Big => u32::from_be_bytes(data),
                    })
                }
                None => {
                    return Err(MemoryError::OutOfBounds.into());
                }
            },
            WordSize::Bit16 => match self.segments.read_raw_bytes(address, 2) {
                Some(v) => {
                    let mut data = [0; 2];
                    data.copy_from_slice(&v);
                    DataWord::Word16(match self.endianness {
                        Endianness::Little => u16::from_le_bytes(data),
                        Endianness::Big => u16::from_be_bytes(data),
                    })
                }
                None => {
                    return Err(MemoryError::OutOfBounds.into());
                }
            },
            WordSize::Bit8 => DataWord::Word8(self.get_byte(address)?),
        })
    }

    /// Get a byte of data from program memory.
    pub fn get_byte(&self, address: u64) -> Result<u8> {
        match self.segments.read_raw_bytes(address, 1) {
            Some(v) => Ok(v[0]),
            None => Err(MemoryError::OutOfBounds.into()),
        }
    }

    /// Get a word from data memory
    pub fn get_word(&self, address: u64) -> Result<DataWord> {
        self.get_word_internal(address, self.word_size)
    }

    pub fn get_half_word(&self, address: u64) -> Result<DataHalfWord> {
        Ok(match self.word_size {
            WordSize::Bit64 => match self.get_word_internal(address, WordSize::Bit32)? {
                DataWord::Word32(d) => DataHalfWord::HalfWord64(d),
                _ => panic!("Should never reach this part."),
            },
            WordSize::Bit32 => match self.get_word_internal(address, WordSize::Bit16)? {
                DataWord::Word16(d) => DataHalfWord::HalfWord32(d),
                _ => panic!("Should never reach this part."),
            },
            WordSize::Bit16 => match self.get_word_internal(address, WordSize::Bit8)? {
                DataWord::Word8(d) => DataHalfWord::HalfWord16(d),
                _ => panic!("Should never reach this part."),
            },
            WordSize::Bit8 => return Err(ProjectError::UnabvalableOperation),
        })
    }
}

impl ProgramMemory for &'static Project {
    fn get_word_size(&self) -> u32 {
        // This is an oversimplification and not true for some architectures
        // But will do and should map to the addresses in the elf
        match self.word_size {
            WordSize::Bit64 => 64,
            WordSize::Bit32 => 32,
            WordSize::Bit16 => 16,
            WordSize::Bit8 => 8,
        }
    }

    fn out_of_bounds<Map: SmtMap>(&self, addr: &Map::Expression, memory: &Map) -> Map::Expression {
        self.segments.could_possibly_be_out_of_bounds(addr, memory)
    }

    fn get_ptr_size(&self) -> u32 {
        self.get_word_size()
    }

    fn get_endianness(&self) -> Endianness {
        self.endianness.clone()
    }

    /// Get the address of a symbol from the ELF symbol table
    fn borrow_symtab(&self) -> &SubProgramMap {
        &self.symtab
    }

    /// Get the address of a symbol from the ELF symbol table
    fn get_symbol_address(&self, symbol: &str) -> Option<u64> {
        Some(self.symtab.get_by_name(symbol)?.bounds.0)
    }

    fn get<Expr: SmtExpr, Ctx: Context<Expr = Expr>>(&self, address: u64, bits: u32, writes: &HashMap<u64, Expr>, ctx: &Ctx) -> std::result::Result<Expr, crate::smt::MemoryError> {
        let word_size = self.get_word_size() as u32;
        let bytes = bits as u64 / 8;
        assert!(bits % 8 == 0);
        let mut written = false;
        for idx in (address..(address + bytes)) {
            if writes.contains_key(&idx) {
                written = true;
                break;
            }
        }

        if written {
            let mut ret = ctx.new_from_u64(0, bits);
            let shift = ctx.new_from_u64(8, bits);
            for idx in (address..(address + bytes)) {
                let inner = ctx.new_from_u64(self.segments.read_raw_bytes(idx, 1).expect("Regions to contain the data")[0] as u64, 8);
                let read = writes.get(&idx).unwrap_or(&inner);
                ret = ret.shift(&shift, general_assembly::shift::Shift::Lsl);
                ret = ret.or(&read.resize_unsigned(bits));
            }
            return Ok(ret);
        }

        // TODO: Convert to propper errors
        if bits == word_size {
            // full word
            Ok(ctx.new_from_u64(self.get_word(address).unwrap().into(), bits))
        } else if bits % word_size == 0 {
            let mut ret = ctx.new_from_u64(0, bits);
            for _word in 0..(bits / word_size) {
                let new_ret = ctx.new_from_u64(self.get_word(address).unwrap().into(), word_size).resize_unsigned(bits);
                ret = ret.shift(&ctx.new_from_u64(word_size as u64, bits), general_assembly::shift::Shift::Lsl).or(&new_ret);
            }
            Ok(ret)
        } else if bits == word_size / 2 {
            // half word
            let value: u64 = match self.get_half_word(address).unwrap() {
                DataHalfWord::HalfWord64(v) => v as u64,
                DataHalfWord::HalfWord32(v) => v as u64,
                DataHalfWord::HalfWord16(v) => v as u64,
            };
            Ok(ctx.new_from_u64(value, bits))
        } else if bits == 8 {
            // byte
            Ok(ctx.new_from_u64(self.get_byte(address).unwrap() as u64, bits))
        } else {
            todo!()
        }
    }

    fn set<Expr: SmtExpr, Ctx: Context<Expr = Expr>>(
        &self,
        mut address: u64,
        mut dataword: Expr,
        writes: &mut HashMap<u64, Expr>,
        ctx: &mut Ctx,
    ) -> std::result::Result<(), crate::smt::MemoryError> {
        match dataword.size() / 8 {
            0 => todo!(),
            1 => {
                let _ = writes.insert(address, dataword);
            }
            2 => {
                for _ in 0..2 {
                    let old_v = dataword.clone();
                    dataword = dataword.shift(&ctx.new_from_u64(8, dataword.size()), general_assembly::shift::Shift::Lsr);
                    let v2 = old_v
                        .sub(&dataword.shift(&ctx.new_from_u64(8, dataword.size()), general_assembly::shift::Shift::Lsl))
                        .resize_unsigned(8);
                    writes.insert(address, v2);
                    address += 1;
                }
            }
            4 => {
                for _ in 0..4 {
                    let old_v = dataword.clone();
                    dataword = dataword.shift(&ctx.new_from_u64(8, dataword.size()), general_assembly::shift::Shift::Lsr);
                    let v2 = old_v
                        .sub(&dataword.shift(&ctx.new_from_u64(8, dataword.size()), general_assembly::shift::Shift::Lsl))
                        .resize_unsigned(8);
                    writes.insert(address, v2);
                    address += 1;
                }
            }
            8 => {
                for _ in 0..8 {
                    let old_v = dataword.clone();
                    dataword = dataword.shift(&ctx.new_from_u64(8, dataword.size()), general_assembly::shift::Shift::Lsr);
                    let v2 = old_v
                        .sub(&dataword.shift(&ctx.new_from_u64(8, dataword.size()), general_assembly::shift::Shift::Lsl))
                        .resize_unsigned(8);
                    writes.insert(address, v2);
                    address += 1;
                }
            }
            _ => unimplemented!("Unsuported bitwidth"),
        }
        Ok(())
    }

    fn address_in_range(&self, address: u64) -> bool {
        self.segments.read_raw_bytes(address, 1).is_some()
    }

    fn get_raw_word(&self, address: u64) -> std::result::Result<Vec<u8>, crate::smt::MemoryError> {
        Ok(match self.word_size {
            WordSize::Bit64 => match self.segments.read_raw_bytes(address, 8) {
                Some(v) => v,
                None => {
                    return Err(MemoryError::OutOfBounds.into());
                }
            },
            WordSize::Bit32 => match self.segments.read_raw_bytes(address, 4) {
                Some(v) => v,
                None => {
                    return Err(MemoryError::OutOfBounds.into());
                }
            },
            WordSize::Bit16 => match self.segments.read_raw_bytes(address, 2) {
                Some(v) => v,
                None => {
                    return Err(MemoryError::OutOfBounds.into());
                }
            },
            WordSize::Bit8 => match self.segments.read_raw_bytes(address, 1) {
                Some(v) => v,
                None => {
                    return Err(MemoryError::OutOfBounds.into());
                }
            },
        })
    }

    fn get_entry_point_names(&self) -> Vec<String> {
        self.symtab.get_all_names()
    }
}

impl Debug for Project {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Project").field("word_size", &self.word_size).field("endianness", &self.endianness).finish()
    }
}
