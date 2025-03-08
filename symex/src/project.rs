use std::fmt::Debug;

use dwarf_helper::SubProgramMap;
use general_assembly::prelude::{DataHalfWord, DataWord};
use hashbrown::HashMap;
use object::Object;
use segments::Segments;

use crate::{arch::ArchError, memory::MemoryError, smt::ProgramMemory, Endianness, WordSize};

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

    #[error("Architecture specific error")]
    ArchError(#[from] ArchError),
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
            segments: Segments::from_single_segment(program_memory, start_addr, end_addr),
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
                    data.copy_from_slice(v);
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
                    data.copy_from_slice(v);
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
                    data.copy_from_slice(v);
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
    fn get_word_size(&self) -> usize {
        // This is an oversimplification and not true for some architectures
        // But will do and should map to the addresses in the elf
        match self.word_size {
            WordSize::Bit64 => 64,
            WordSize::Bit32 => 32,
            WordSize::Bit16 => 16,
            WordSize::Bit8 => 8,
        }
    }

    fn get_ptr_size(&self) -> usize {
        self.get_word_size()
    }

    fn get_endianness(&self) -> Endianness {
        self.endianness.clone()
    }

    /// Get the address of a symbol from the ELF symbol table
    fn get_symbol_address(&self, symbol: &str) -> Option<u64> {
        Some(self.symtab.get_by_name(symbol)?.bounds.0)
    }

    fn get(&self, address: u64, bits: u32) -> std::result::Result<DataWord, crate::smt::MemoryError> {
        let word_size = self.get_word_size() as u32;
        if bits == word_size as u32 {
            // full word
            Ok(self.get_word(address).unwrap())
        } else if bits == word_size / 2 {
            // half word
            Ok(self.get_half_word(address).unwrap().into())
        } else if bits == 8 {
            // byte
            Ok(DataWord::Word8(self.get_byte(address).unwrap()))
        } else {
            todo!()
        }
    }

    fn set(&self, _address: u64, _dataword: DataWord) -> std::result::Result<(), crate::smt::MemoryError> {
        todo!("Project does not yet support caching writes to globals.")
    }

    fn address_in_range(&self, address: u64) -> bool {
        self.segments.read_raw_bytes(address, 1).is_some()
    }

    fn get_raw_word(&self, address: u64) -> std::result::Result<&[u8], crate::smt::MemoryError> {
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
