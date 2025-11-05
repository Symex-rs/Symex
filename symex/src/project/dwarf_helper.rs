//! Helper functions to read dwarf debug data.

pub mod variables;

use std::hash::Hash;

use gimli::{
    read::DebugFrame,
    AttributeValue,
    DW_AT_decl_file,
    DW_AT_decl_line,
    DW_AT_high_pc,
    DW_AT_low_pc,
    DW_AT_name,
    DebugAbbrev,
    DebugInfo,
    DebugLine,
    DebugStr,
    Dwarf,
    EndianSlice,
    Reader,
    RunTimeEndian,
};
use hashbrown::{HashMap, HashSet};
use object::{Object, ObjectSection};
use regex::Regex;
use rust_debug::call_stack::{CallFrame, MemoryAccess, StackFrame};

use crate::{
    arch::{ArchitectureOverride, SupportedArchitecture},
    debug,
    smt::{SmtExpr, SmtMap},
    trace,
};

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", derive(serde::Deserialize))]
#[must_use]
pub struct SubProgram {
    pub name: String,
    pub bounds: (u64, u64),
    pub file: Option<(String, usize)>,
    /// Call site for an inlined sub routine.
    pub call_file: Option<(String, usize)>,
}

impl Hash for SubProgram {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

#[derive(Clone, Debug)]
#[must_use]
pub struct SubProgramMap {
    pub index_1: HashMap<String, u64>,
    index_2: HashMap<u64, u64>,
    pub map: HashMap<u64, SubProgram>,
    counter: u64,
    pub symtab: HashMap<String, SubProgram>,
}

impl Default for SubProgramMap {
    fn default() -> Self {
        Self::_new()
    }
}

impl SubProgramMap {
    fn _new() -> Self {
        Self {
            index_1: HashMap::new(),
            index_2: HashMap::new(),
            map: HashMap::new(),
            counter: 0,
            symtab: HashMap::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn empty() -> Self {
        Self {
            index_1: HashMap::new(),
            index_2: HashMap::new(),
            map: HashMap::new(),
            counter: 0,
            symtab: HashMap::new(),
        }
    }

    pub fn insert_symtab(&mut self, symtab: HashMap<String, u64>) {
        for (key, value) in symtab {
            let _ = self.symtab.insert(key.clone(), SubProgram {
                name: key,
                bounds: (value & ((u64::MAX >> 1) << 1), value & ((u64::MAX >> 1) << 1)),
                file: None,
                call_file: None,
            });
        }
    }

    #[must_use]
    pub fn in_bounds(&self, pc: u64) -> Vec<SubProgram> {
        self.map
            .values()
            .chain(self.symtab.values())
            .filter(|s| ((s.bounds.0)..=(s.bounds.1)).contains(&pc))
            .cloned()
            .collect()
    }

    #[must_use]
    pub fn get_all_names(&self) -> Vec<String> {
        let mut ret: Vec<String> = self.symtab.keys().cloned().collect::<Vec<_>>();
        ret.extend(self.index_1.keys().cloned());
        ret
    }

    fn insert(&mut self, name: String, address: u64, value: SubProgram) {
        let _ = self.index_1.insert(name, self.counter);
        let _ = self.index_2.insert(address & ((u64::MAX >> 1) << 1), self.counter);
        let _ = self.map.insert(self.counter, value);
        self.counter += 1;
    }

    #[must_use]
    pub fn get_by_name(&self, name: &str) -> Option<&SubProgram> {
        let Some(idx) = self.index_1.get(name) else {
            return self.symtab.get(name);
        };
        self.map.get(idx)
    }

    #[must_use]
    pub fn get_by_address(&self, address: &u64) -> Option<&SubProgram> {
        let idx = self.index_2.get(&(*address & ((u64::MAX >> 1) << 1)))?;
        self.map.get(idx)
    }

    #[must_use]
    pub fn get_by_regex(&self, pattern: &'static str) -> Option<&SubProgram> {
        let regex = Regex::new(pattern).ok()?;
        for (idx, prog) in &self.index_1 {
            if regex.is_match(idx) {
                return self.map.get(prog);
            }
        }
        for (idx, prog) in &self.symtab {
            if regex.is_match(idx) {
                return Some(prog);
            }
        }
        None
    }

    #[must_use]
    pub fn get_all_by_regex(&self, pattern: &'static str) -> Vec<&SubProgram> {
        let Ok(regex) = Regex::new(pattern) else {
            return vec![];
        };
        let mut ret = HashSet::new();
        for (idx, prog) in &self.index_1 {
            if regex.is_match(idx) {
                if let Some(val) = self.map.get(prog) {
                    trace!("[{pattern}] :Matched  {val:?}");
                    ret.insert(val);
                }
            }
        }
        if !ret.is_empty() {
            return ret.into_iter().collect::<Vec<_>>();
        }
        for (idx, prog) in &self.symtab {
            if regex.is_match(idx) {
                trace!("[{pattern}]2 : Matched  {prog:?}");
                ret.insert(prog);
            }
        }
        ret.into_iter().collect::<Vec<_>>()
    }

    pub fn new<R: Reader>(debug_info: &DebugInfo<R>, debug_abbrev: &DebugAbbrev<R>, debug_str: &DebugStr<R>, _lines: &DebugLine<R>) -> Self {
        let mut ret = Self::_new();
        let mut units = debug_info.units();
        while let Some(unit) = units.next().unwrap() {
            let abbrev = unit.abbreviations(debug_abbrev).unwrap();
            let mut cursor = unit.entries(&abbrev);

            while let Some((_dept, entry)) = cursor.next_dfs().unwrap() {
                let tag = entry.tag();
                if tag != gimli::DW_TAG_subprogram {
                    // is not a function continue the search
                    continue;
                }
                let Some(attr) = entry.attr_value(DW_AT_name).unwrap() else {
                    continue;
                };

                let AttributeValue::DebugStrRef(entry_name) = attr else {
                    continue;
                };
                let entry_name = debug_str.get_str(entry_name).unwrap();
                let name = entry_name.to_string().unwrap().to_string();

                let addr = match entry.attr_value(DW_AT_low_pc).unwrap() {
                    Some(AttributeValue::Addr(v)) => v,
                    Some(AttributeValue::Data1(v)) => v as u64,
                    Some(AttributeValue::Data2(v)) => v as u64,
                    Some(AttributeValue::Data4(v)) => v as u64,
                    Some(AttributeValue::Data8(v)) => v,
                    Some(AttributeValue::Udata(val)) => val,
                    _ => continue,
                } & ((u64::MAX >> 1) << 1);
                let addr_end = match entry.attr_value(DW_AT_high_pc).unwrap() {
                    Some(AttributeValue::Data1(v)) => v as u64,
                    Some(AttributeValue::Data2(v)) => v as u64,
                    Some(AttributeValue::Data4(v)) => v as u64,
                    Some(AttributeValue::Data8(v)) => v,
                    Some(AttributeValue::Udata(val)) => val,
                    _val => 0,
                } & ((u64::MAX >> 1) << 1);
                let file = match entry.attr_value(DW_AT_decl_file).unwrap() {
                    Some(AttributeValue::String(s)) => s.to_string().unwrap().to_string(),
                    _ => String::new(),
                };
                let line = match entry.attr_value(DW_AT_decl_line).unwrap() {
                    Some(AttributeValue::Data1(v)) => v as usize,
                    Some(AttributeValue::Data2(v)) => v as usize,
                    Some(AttributeValue::Data4(v)) => v as usize,
                    Some(AttributeValue::Data8(v)) => v as usize,
                    Some(AttributeValue::Udata(val)) => val as usize,
                    _ => 0,
                };
                if addr == 0 {
                    continue;
                }
                debug!("entry point {name} at addr {}", addr);

                ret.insert(name.clone(), addr, SubProgram {
                    name,
                    bounds: (addr, addr + addr_end),
                    file: Some((file, line)),
                    call_file: None,
                });
            }
        }
        ret
    }
}

#[derive(Clone, Debug)]
pub struct LineInfo {
    file: String,
    line: u64,
    text: Option<String>,
}

#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct LineMap {
    map: Option<&'static HashMap<u64, LineInfo>>,
}
impl LineMap {
    pub(crate) const fn empty() -> Self {
        Self { map: None }
    }

    #[must_use]
    pub fn lookup(&self, address: u64) -> Option<&LineInfo> {
        let map = self.map?;
        map.get(&address)
    }
}
impl std::fmt::Display for LineInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.text {
            Some(text) => write!(f, "{text} (in file {} on line {})", self.file, self.line),
            None => write!(f, "in file {} on line {}", self.file, self.line),
        }
    }
}

/// All credit goes to [The gimli developers](https://github.com/gimli-rs/gimli/blob/master/crates/examples/src/bin/simple_line.rs#L20)
pub(crate) fn line_program(object: &object::File<'_>, endian: gimli::RunTimeEndian) -> Result<LineMap, Box<dyn std::error::Error>> {
    // Load a section and return as `Cow<[u8]>`.
    let load_section = |id: gimli::SectionId| -> Result<std::borrow::Cow<'_, [u8]>, Box<dyn std::error::Error>> {
        Ok(match object.section_by_name(id.name()) {
            Some(section) => section.uncompressed_data()?,
            None => std::borrow::Cow::Borrowed(&[]),
        })
    };

    // Borrow a `Cow<[u8]>` to create an `EndianSlice`.
    let borrow_section = |section| gimli::EndianSlice::new(std::borrow::Cow::as_ref(section), endian);

    // Load all of the sections.
    let dwarf_sections = gimli::DwarfSections::load(&load_section)?;

    // Create `EndianSlice`s for all of the sections.
    let dwarf = dwarf_sections.borrow(borrow_section);
    let mut map = HashMap::new();

    // Iterate over the compilation units.
    let mut iter = dwarf.units();
    while let Some(header) = iter.next()? {
        let unit = dwarf.unit(header)?;
        let unit = unit.unit_ref(&dwarf);

        // Get the line program for the compilation unit.
        if let Some(program) = unit.line_program.clone() {
            // NOTE: Omitted due to size for now.
            let comp_dir = std::path::PathBuf::new();

            // Iterate over the line program rows.
            let mut rows = program.rows();
            while let Some((header, row)) = rows.next_row()? {
                if row.end_sequence() {
                    // End of sequence indicates a possible gap in addresses.
                } else {
                    // Determine the path. Real applications should cache this for performance.
                    let mut path = std::path::PathBuf::new();
                    if let Some(file) = row.file(header) {
                        path.clone_from(&comp_dir);

                        // The directory index 0 is defined to correspond to the compilation unit
                        // directory.
                        if file.directory_index() != 0 {
                            if let Some(dir) = file.directory(header) {
                                path.push(unit.attr_string(dir)?.to_string_lossy().as_ref());
                            }
                        }

                        path.push(unit.attr_string(file.path_name())?.to_string_lossy().as_ref());
                    }

                    // Determine line/column. DWARF line/column is never 0, so we use that
                    // but other applications may want to display this differently.
                    let line = match row.line() {
                        Some(line) => line.get(),
                        None => 0,
                    };
                    let meta = LineInfo {
                        text: None,
                        file: path.display().to_string(),
                        line,
                    };
                    let _ = map.try_insert(row.address(), meta);
                }
            }
        }
    }

    Ok(LineMap {
        map: Some(Box::leak(Box::new(map))),
    })
}

pub struct DAP<'a, M: SmtMap, E: SmtExpr> {
    pub mem: &'a mut M,
    pub constraints: &'a [E],
}

#[derive(Clone, Debug)]
pub struct DebugData {
    dwarf: &'static Dwarf<EndianSlice<'static, RunTimeEndian>>,
    debug_frame: &'static DebugFrame<EndianSlice<'static, RunTimeEndian>>,
}

pub struct CallStack {
    pub final_frame: StackFrame<EndianSlice<'static, RunTimeEndian>>,
    pub stack_trace: Vec<(CallFrame, Vec<(String, String)>)>,
}

impl DebugData {
    pub const fn unwind_symbolic(&self) {}

    pub(crate) fn new(object: &'static object::File<'static>, endian: gimli::RunTimeEndian) -> Result<Self, Box<dyn std::error::Error>> {
        let load_section = |id: gimli::SectionId| -> Result<std::borrow::Cow<'_, [u8]>, Box<dyn std::error::Error>> {
            Ok(match object.section_by_name(id.name()) {
                Some(section) => section.uncompressed_data()?,
                None => std::borrow::Cow::Borrowed(&[]),
            })
        };

        // Borrow a `Cow<[u8]>` to create an `EndianSlice`.
        let borrow_section = |section| gimli::EndianSlice::new(std::borrow::Cow::as_ref(section), endian);

        // Load all of the sections.
        let dwarf_sections = Box::leak(Box::new(gimli::DwarfSections::load(&load_section)?));

        // Create `EndianSlice`s for all of the sections.
        let dwarf = dwarf_sections.borrow(borrow_section);

        let sec = object
            .section_by_name(".debug_frame")
            .expect("debug frame to exist")
            .uncompressed_data()
            .expect("Data to be readable");
        let frame = DebugFrame::new(Box::leak(Box::new(sec)), endian);

        Ok(Self {
            dwarf: Box::leak(Box::new(dwarf)),
            debug_frame: Box::leak(Box::new(frame)),
        })
    }

    pub fn produce_backtrace<M: SmtMap<Expression = E>, O: ArchitectureOverride, E: SmtExpr>(
        &self,
        dap: &mut DAP<'_, M, E>,
        last_pc: u64,
        arch: &SupportedArchitecture<O>,
    ) -> Option<CallStack> {
        let mut register_map = std::collections::HashMap::new();
        let registers = dap.mem.get_registers();
        registers.iter().for_each(|(reg, value)| {
            let _ = register_map.insert(
                arch.register_name_to_number(reg).expect("Register to be named") as u16,
                value.get_a_solution(dap.constraints).expect("State to be sat") as u32,
            );
        });
        register_map.insert(arch.register_name_to_number("PC").expect("PC to be named") as u16, last_pc as u32);

        for idx in 0..16 {
            let _ = register_map.entry(idx).or_insert(0);
        }
        let mut registers = rust_debug::registers::Registers::default();
        registers.registers = register_map;

        // TODO: Make generic!
        registers.link_register = arch.register_name_to_number("LR").map(|el| el as usize);
        registers.program_counter_register = arch.register_name_to_number("PC").map(|el| el as usize);
        registers.stack_pointer_register = arch.register_name_to_number("SP").map(|el| el as usize);

        let call_trace = rust_debug::call_stack::unwind_call_stack(registers.clone(), dap, self.debug_frame).expect("Call stack to be traceable");

        if call_trace.is_empty() {
            return None;
        }
        let val = &call_trace[0];
        let current_frame = rust_debug::call_stack::create_stack_frame(self.dwarf, val.clone(), &registers, dap, "").expect("Stack trace being creatable");
        let stack_trace = call_trace
            .iter()
            .map(|el| {
                let mut regs = rust_debug::registers::Registers::default();
                regs.registers = std::collections::HashMap::with_capacity(16);
                for (idx, el) in el.registers.iter().enumerate() {
                    if let Some(reg) = el {
                        let _ = regs.registers.insert(idx as u16, *reg);
                    } else {
                        let _ = regs.registers.insert(idx as u16, 0);
                    }
                }
                registers.link_register = arch.register_name_to_number("LR").map(|el| el as usize);
                registers.program_counter_register = arch.register_name_to_number("PC").map(|el| el as usize);
                registers.stack_pointer_register = arch.register_name_to_number("SP").map(|el| el as usize);

                let frame = rust_debug::call_stack::create_stack_frame(self.dwarf, val.clone(), &registers, dap, "").expect("Stack trace being creatable");

                let args = frame
                    .arguments
                    .iter()
                    .map(|el| {
                        (
                            el.name.clone().unwrap_or_else(|| "Unnamed argument".to_string()),
                            el.value.clone().to_value().map_or_else(|| "Unable to get value".to_string(), |el| el.to_string()),
                        )
                    })
                    .collect::<_>();
                (el.clone(), args)
            })
            .collect::<Vec<_>>();
        Some(CallStack {
            final_frame: current_frame,
            stack_trace,
        })
    }
}

impl<M, E: SmtExpr> MemoryAccess for DAP<'_, M, E>
where
    M: SmtMap<Expression = E>,
{
    fn get_address(&mut self, address: &u32, num_bytes: usize) -> Option<Vec<u8>> {
        let mut address = *address as u64;

        let mut buffer = Vec::with_capacity(num_bytes);
        for _el in 0..num_bytes {
            buffer.push(
                self.mem
                    .get(&self.mem.from_u64(address, self.mem.get_ptr_size()), 1)
                    .ok()
                    // NOTE: Approximate!
                    .and_then(|el| el.get_a_solution(self.constraints))? as u8,
            );
            address += 1;
        }
        Some(buffer)
    }
}
