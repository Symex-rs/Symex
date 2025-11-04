//! A loader that can load all segments from a elf file properly.

use object::{read::elf::ProgramHeader, File, Object};

use crate::smt::{Lambda, SmtExpr, SmtSolver};
pub struct Segment {
    data: Vec<u8>,
    start_address: u64,
    end_address: u64,
    constants: bool,
}

pub struct Segments<S: SmtSolver>(Vec<Segment>, S::UnaryLambda);

fn construct_lookup<C: SmtSolver>(ctx: &mut C, word_size: u32, segments: &Vec<Segment>) -> C::UnaryLambda {
    let ctx_clone = ctx.clone();
    C::UnaryLambda::new(ctx, word_size, move |addr: C::Expression| {
        let mut ret = ctx_clone.from_bool(true);
        let symbolic = segments
            .into_iter()
            .filter(|el| el.constants)
            .map(|el| (ctx_clone.from_u64(el.start_address, word_size), ctx_clone.from_u64(el.end_address, word_size)));
        for (start, end) in symbolic {
            ret = ret.and(&addr.ult(&start).or(&addr.ugt(&end)));
        }
        ret
    })
}

impl<S: SmtSolver> Segments<S> {
    pub fn sections(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        self.0.iter().map(|seg| (seg.start_address, seg.end_address))
    }

    pub fn read_only_sections(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        self.0.iter().filter(|el| el.constants).map(|seg| (seg.start_address, seg.end_address))
    }

    pub(crate) fn could_possibly_be_out_of_bounds(&self, addr: S::Expression) -> S::Expression {
        self.1.apply(addr)
    }

    pub(crate) fn could_possibly_be_out_of_bounds_const(&self, addr: u64) -> bool {
        let mut ret = true;
        for segment in self.0.iter().filter(|el| el.constants) {
            let start = segment.start_address;
            let end = segment.end_address;
            ret = ret && ((addr < start) || (addr > end));
        }
        ret
    }

    #[allow(deprecated)]
    pub fn from_file(ctx: &mut S, file: &File<'_>) -> Self {
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
        // TODO: Correct this.
        let lookup = construct_lookup(ctx, 32, &ret);
        Segments(ret, lookup)
    }

    pub fn read_raw_bytes(&self, mut address: u64, bytes: usize) -> Option<Vec<u8>> {
        let initial_bytes = bytes;
        let mut segments = self.0.iter();
        while let Some(segment) = segments.next() {
            if address >= segment.start_address && address < segment.end_address {
                let offset = (address - segment.start_address) as usize;
                if (address + bytes as u64) > segment.end_address {
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
