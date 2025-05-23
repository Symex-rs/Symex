//! Helper functions to read dwarf debug data.

use std::{borrow::Cow, hash::Hash};

use gimli::{
    AttributeValue,
    CompleteLineProgram,
    DW_AT_decl_file,
    DW_AT_decl_line,
    DW_AT_high_pc,
    DW_AT_low_pc,
    DW_AT_name,
    DebugAbbrev,
    DebugInfo,
    DebugLine,
    DebugStr,
    LineSequence,
    Reader,
};
use hashbrown::{HashMap, HashSet};
use regex::Regex;

use crate::{debug, smt::SmtMap, trace};

#[derive(Clone, Debug, PartialEq, Eq)]
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
        //println!("Loading symtab {:?}", symtab);
        for (key, value) in symtab {
            let _ = self.symtab.insert(key.clone(), SubProgram {
                name: key,
                bounds: (value & ((u64::MAX >> 1) << 1), value & ((u64::MAX >> 1) << 1)),
                file: None,
                call_file: None,
            });
        }
    }

    pub fn in_bounds(&self, pc: u64) -> Vec<SubProgram> {
        self.map
            .values()
            .chain(self.symtab.values())
            .filter(|s| ((s.bounds.0)..=(s.bounds.1)).contains(&pc))
            .cloned()
            .collect()
    }

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

    pub fn get_by_name(&self, name: &str) -> Option<&SubProgram> {
        let idx = match self.index_1.get(name) {
            Some(val) => val,
            None => return self.symtab.get(name),
        };
        self.map.get(idx)
    }

    pub fn get_by_address(&self, address: &u64) -> Option<&SubProgram> {
        let idx = self.index_2.get(&(*address & ((u64::MAX >> 1) << 1)))?;
        self.map.get(idx)
    }

    pub fn get_by_regex(&self, pattern: &'static str) -> Option<&SubProgram> {
        let regex = Regex::new(pattern).ok()?;
        for (idx, prog) in self.index_1.iter() {
            if regex.is_match(idx) {
                return self.map.get(prog);
            }
        }
        for (idx, prog) in self.symtab.iter() {
            if regex.is_match(idx) {
                return Some(prog);
            }
        }
        None
    }

    pub fn get_all_by_regex(&self, pattern: &'static str) -> Vec<&SubProgram> {
        let regex = match Regex::new(pattern) {
            Ok(val) => val,
            Err(_) => return vec![],
        };
        let mut ret = HashSet::new();
        for (idx, prog) in self.index_1.iter() {
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
        for (idx, prog) in self.symtab.iter() {
            if regex.is_match(idx) {
                trace!("[{pattern}]2 : Matched  {prog:?}");
                ret.insert(prog);
            }
        }
        ret.into_iter().collect::<Vec<_>>()
    }

    // fn process_unit<R: Reader>(line_info: &DebugLine<R>, target_pc: u64) ->
    // Option<(String, u32)> {     let mut entry_pc = 0;
    //     let mut entry_line = 1;
    //     let mut current_file = Cow::Borrowed("");
    //     let (line_program, line_sequence): (CompleteLineProgram<R, _>,
    // Vec<LineSequence<R>>) = line_info.program(0, 32, None,
    // None).ok()?.sequences().ok()?;
    //
    //     for instruction in line_sequence {
    //         // QUESTION: Is this correct?
    //         //
    //         // PROCEDURE: If this is not correct, please correct it.
    //         if !(instruction.start..instruction.end).contains(&target_pc) {
    //             continue;
    //         }
    //
    //         let prog: CompleteLineProgram<R, <R as Reader>::Offset> =
    // line_program.resume_from(&instruction);
    //
    //         todo!(" Get the line number, file name `with absolute path`");
    //     }
    //
    //     None
    // }

    pub fn new<R: Reader>(debug_info: &DebugInfo<R>, debug_abbrev: &DebugAbbrev<R>, debug_str: &DebugStr<R>, lines: &DebugLine<R>) -> SubProgramMap {
        let mut ret: SubProgramMap = SubProgramMap::_new();
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
                let attr = match entry.attr_value(DW_AT_name).unwrap() {
                    Some(a) => a,
                    None => continue,
                };

                let entry_name = match attr {
                    AttributeValue::DebugStrRef(s) => s,
                    _ => continue,
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
                    _ => "".to_string(),
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

//fn line_map<R:gimli::Reader>(pc:
