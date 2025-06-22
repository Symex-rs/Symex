//! A loader that can load all segments from a elf file properly.

use object::{read::elf::ProgramHeader, File, Object};

use crate::smt::{SmtExpr, SmtMap};
pub struct Segment {
    data: Vec<u8>,
    start_address: u64,
    end_address: u64,
    constants: bool,
}

pub struct Segments(Vec<Segment>);

impl Segments {
    pub fn from_single_segment(data: Vec<u8>, start_addr: u64, end_addr: u64, constants: bool) -> Self {
        Segments(vec![Segment {
            data,
            start_address: start_addr,
            end_address: end_addr,
            constants,
        }])
    }

    pub(crate) fn could_possibly_be_out_of_bounds<Map: SmtMap>(&self, addr: &Map::Expression, memory: &Map) -> Map::Expression {
        let mut ret = memory.from_bool(true);
        for segment in self.0.iter().filter(|el| el.constants) {
            // println!("Segment that spans from {:#x} until {:#x}", segment.start_address,
            // segment.end_address);
            let start = memory.from_u64(segment.start_address, memory.get_ptr_size());
            let end = memory.from_u64(segment.end_address, memory.get_ptr_size());
            ret = ret.and(&addr.ult(&start).or(&addr.ugt(&end)));
        }
        ret
    }

    #[allow(deprecated)]
    pub fn from_file(file: &File<'_>) -> Self {
        let elf_file = match file {
            File::Elf32(elf_file) => elf_file,
            File::Elf64(_elf_file) => todo!(),
            _ => todo!(),
        };

        let mut ret = vec![];
        for segment in elf_file.raw_segments() {
            let segment_type = segment.p_type.get(file.endianness());

            if segment_type == 1 {
                // if it is a LOAD segment
                let addr_start = segment.p_vaddr.get(file.endianness()) as u64;
                //let size = segment.p_memsz.get(file.endianness());
                let data = segment.data(file.endianness(), elf_file.data()).unwrap();

                let new = Segment {
                    data: data.to_owned(),
                    start_address: addr_start,
                    end_address: addr_start + data.len() as u64,
                    constants: segment.p_flags.get(file.endianness()) & 0b010 == 0b000,
                };
                ret.push(new)
            }
        }
        Segments(ret)
    }

    pub fn read_raw_bytes(&self, mut address: u64, bytes: usize) -> Option<Vec<u8>> {
        let initial_bytes = bytes;
        let mut segments = self.0.iter();
        while let Some(segment) = segments.next() {
            if address >= segment.start_address && address < segment.end_address {
                let offset = (address - segment.start_address) as usize;
                if (address + bytes as u64) > segment.end_address {
                    println!("Reading across segments!");
                    let mut buffer: Vec<u8> = Vec::new();
                    let remaining_bytes = address + bytes as u64 - segment.end_address;
                    let bytes = bytes - remaining_bytes as usize;
                    let in_this_segment = &segment.data[offset..(offset + bytes)];
                    buffer.extend(in_this_segment);
                    address += bytes as u64;
                    Self::continue_reading_bytes(&mut buffer, segments, address, bytes);
                    if buffer.len() != initial_bytes {
                        return None;
                    }
                    // Sub-optimal
                    return Some(buffer);
                }
                let data_slice = &segment.data[offset..(offset + bytes)];
                return Some(data_slice.to_vec());
            }
        }

        None
    }

    pub fn continue_reading_bytes<'borrow, I: Iterator<Item = &'borrow Segment>>(read: &mut Vec<u8>, mut segments: I, mut address: u64, mut bytes: usize) {
        if bytes == 0 {
            return;
        }
        while let Some(segment) = segments.next() {
            if address >= segment.start_address && address < segment.end_address {
                let offset = (address - segment.start_address) as usize;
                let remaining_bytes = address + bytes as u64 - (address + bytes as u64).min(segment.end_address);
                let contained_bytes = bytes - remaining_bytes as usize;
                let data_slice = &segment.data[offset..(offset + contained_bytes)];
                address += contained_bytes as u64;
                bytes = remaining_bytes as usize;
                read.extend(data_slice);
                Self::continue_reading_bytes(read, segments, address, bytes);
                return;
            }
        }
    }
}
