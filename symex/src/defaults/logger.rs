use std::fmt::Display;

use colored::Colorize;

use crate::{
    debug,
    executor::PathResult,
    logging::{Logger, Region, RegionMetaData},
    manager::SymexArbiter,
    project::dwarf_helper::{SubProgram, SubProgramMap},
};

#[derive(Clone, Debug)]
pub struct PathLog {
    statements: Vec<(Option<SubProgram>, String)>,
    final_state: String,
    result: String,
    constraints: Vec<String>,
    execution_time: String,
    visited: Vec<String>,
    log_idx: usize,
}

#[derive(Clone, Debug)]
pub struct SimplePathLogger {
    statements: Vec<(Option<SubProgram>, String)>,
    final_state: String,
    result: String,
    constraints: Vec<String>,
    execution_time: String,
    visited: Vec<String>,

    log_idx: usize,

    regions: SubProgramMap,
    current_region: Option<SubProgram>,
    pc: u64,
}

impl PathLog {
    fn new(log_idx: usize) -> Self {
        Self {
            statements: Vec::new(),
            final_state: String::new(),
            result: String::new(),
            constraints: Vec::new(),
            execution_time: String::new(),
            visited: Vec::new(),
            log_idx,
        }
    }
}

struct PathLogger<'logger> {
    sub_program: &'logger Option<SubProgram>,
    path: &'logger mut PathLog,
}

#[derive(Clone, Debug)]
pub struct SimpleLogger {
    regions: SubProgramMap,
    current_region: Option<SubProgram>,
    paths: Vec<PathLog>,
    pc: u64,
    path_idx: usize,
}

impl SimpleLogger {
    fn path_logger(&mut self) -> PathLogger<'_> {
        PathLogger {
            path: &mut self.paths[self.path_idx],
            sub_program: &self.current_region,
        }
    }
}

impl<'a> PathLogger<'a> {
    fn write(&mut self, statement: String) {
        self.path.statements.push((self.sub_program.clone(), statement));
    }

    fn finalize(&mut self, state: String) {
        self.path.result = state;
    }

    fn final_state(&mut self, state: String) {
        self.path.final_state = state;
    }

    fn constrain(&mut self, assumption: String) {
        self.path.constraints.push(assumption);
    }

    fn execution_time(&mut self, time: String) {
        self.path.execution_time = time;
    }

    fn visit(&mut self, func: String) {
        if Some(&func) != self.path.visited.last() {
            self.path.visited.push(func);
        }
    }
}

impl SimplePathLogger {
    pub fn from_sub_programs(state: &SubProgramMap) -> Self {
        Self {
            statements: Vec::new(),
            final_state: String::new(),
            result: String::new(),
            constraints: Vec::new(),
            execution_time: String::new(),
            visited: Vec::new(),
            log_idx: 0,
            regions: state.clone(),
            current_region: None,
            pc: 0,
        }
    }
}

impl Logger for SimplePathLogger {
    type RegionDelimiter = u64;
    type RegionIdentifier = SubProgram;

    fn set_path_idx(&mut self, new_path_idx: usize) {
        self.log_idx = new_path_idx;
    }

    fn fork(&self) -> Self {
        self.clone()
    }

    fn warn<T: ToString>(&mut self, warning: T) {
        let subprogram = self.regions.in_bounds(self.pc);
        debug!("Matching subprograms {subprogram:?}");
        let subprogram = subprogram.get(0).cloned();
        // println!("Logging in {subprogram:?}");
        self.statements.push((subprogram, format!("[{}]: {}", "WARN".yellow(), warning.to_string())));
    }

    fn error<T: ToString>(&mut self, warning: T) {
        let subprogram = self.regions.in_bounds(self.pc).get(0).cloned();
        self.statements.push((subprogram, format!("[{}]: {}", "ERROR".red(), warning.to_string())));
    }

    fn update_delimiter<T: Into<Self::RegionDelimiter>>(&mut self, region: T) {
        self.pc = region.into();
        let region = self.regions.get_by_address(&self.pc).cloned();

        if region
            .as_ref()
            .is_some_and(|el| self.current_region.as_ref().is_some_and(|other| other != el) || self.current_region.is_none())
        {
            let region = unsafe { region.as_ref().unwrap_unchecked() };
            self.visited.push(region.name.clone());
        }
        self.current_region = region;
    }

    fn record_path_result<C: crate::Composition>(&mut self, path_result: PathResult<C>) {
        let res = format!("Result: {}", match path_result {
            PathResult::Suppress => "Path suppressed".yellow(),
            PathResult::Success(Some(expression)) => format!("Success ({:?})", expression).green(),
            PathResult::Success(None) => "Success".green(),
            PathResult::Failure(cause) => format!("Failure {cause}",).red(),
            PathResult::AssumptionUnsat => "Unsatisfiable".red(),
        });
        self.result = res;
    }

    fn register_region(&mut self, _region: Self::RegionIdentifier) {
        todo!("This should likely be removed");
    }

    fn assume<T: ToString>(&mut self, assumption: T) {
        let subprogram = self.regions.in_bounds(self.pc);
        debug!("Matching subprograms {subprogram:?}");
        let subprogram = subprogram.get(0).cloned();
        self.statements.push((subprogram, format!("[{}]: {}", "ASSUME".blue(), assumption.to_string())));
    }

    fn current_region(&self) -> Option<Self::RegionIdentifier> {
        self.regions.get_by_address(&self.pc).cloned()
    }

    fn add_constraints(&mut self, constraints: Vec<String>) {
        for constraint in constraints {
            self.constraints.push(format!("[{}]: {}", "CONSTRAINT".yellow(), constraint));
        }
    }

    fn record_final_state<C: crate::Composition>(&mut self, state: crate::executor::state::GAState<C>) {
        let memory = state.memory;
        let fp_state = state.fp_state;
        self.final_state = format!("{memory}\r\n{fp_state}");
    }

    fn record_execution_time<T: ToString>(&mut self, time: T) {
        self.execution_time = time.to_string();
    }

    fn new<C: crate::Composition>(state: &SymexArbiter<C>) -> Self {
        Self {
            statements: Vec::new(),
            final_state: String::new(),
            result: String::new(),
            constraints: Vec::new(),
            execution_time: String::new(),
            visited: Vec::new(),
            log_idx: 0,
            regions: state.get_symbol_map().clone(),
            current_region: None,
            pc: 0,
        }
    }
}

impl Logger for SimpleLogger {
    type RegionDelimiter = u64;
    type RegionIdentifier = SubProgram;

    fn fork(&self) -> Self {
        self.clone()
    }

    fn update_delimiter<T: Into<Self::RegionDelimiter>>(&mut self, region: T) {
        self.pc = region.into();
        self.current_region = self.regions.get_by_address(&self.pc).cloned();
        if let Some(region) = &self.current_region {
            let name = region.name.clone();
            self.path_logger().visit(name);
        }
    }

    fn warn<T: ToString>(&mut self, warning: T) {
        self.path_logger().write(format!("[{}]: {}", "WARN".yellow(), warning.to_string()));
    }

    fn record_path_result<C: crate::Composition>(&mut self, path_result: crate::executor::PathResult<C>) {
        let res = format!("Result: {}", match path_result {
            PathResult::Suppress => "Path suppressed".yellow(),
            PathResult::Success(Some(expression)) => format!("Success ({:?})", expression).green(),
            PathResult::Success(None) => "Success".green(),
            PathResult::Failure(cause) => format!("Failure {cause}",).red(),
            PathResult::AssumptionUnsat => "Unsatisfiable".red(),
        });
        self.path_logger().finalize(res);
    }

    fn set_path_idx(&mut self, new_path_idx: usize) {
        while new_path_idx >= self.paths.len() {
            let ret = PathLog::new(new_path_idx);
            self.paths.push(ret);
        }
        self.path_idx = new_path_idx;
    }

    fn error<T: ToString>(&mut self, error: T) {
        self.path_logger().write(format!("[{}]: {}", "ERROR".red(), error.to_string()));
    }

    fn assume<T: ToString>(&mut self, assumption: T) {
        self.path_logger().write(format!("[{}]: {}", "ASSUME".blue(), assumption.to_string()));
    }

    fn current_region(&self) -> Option<Self::RegionIdentifier> {
        self.current_region.clone()
    }

    fn add_constraints(&mut self, constraints: Vec<String>) {
        for constraint in constraints {
            let pc = self.pc;
            self.path_logger().constrain(format!("{:#x} -> {constraint}", pc));
        }
    }

    fn register_region(&mut self, _region: Self::RegionIdentifier) {
        todo!();
    }

    fn record_final_state<C: crate::Composition>(&mut self, state: crate::executor::state::GAState<C>) {
        let memory = state.memory;

        let fp_state = state.fp_state;
        self.path_logger().final_state(format!("{memory}\r\n{fp_state}"));
    }

    fn record_execution_time<T: ToString>(&mut self, time: T) {
        self.path_logger().execution_time(time.to_string());
    }

    fn new<C: crate::Composition>(state: &SymexArbiter<C>) -> Self {
        Self {
            regions: state.get_symbol_map().clone(),
            current_region: None,
            paths: vec![],
            pc: 0,
            path_idx: 0,
        }
    }
}

impl SimpleLogger {
    pub fn from_sub_programs(state: &SubProgramMap) -> Self {
        Self {
            regions: state.clone(),
            current_region: None,
            paths: vec![],
            pc: 0,
            path_idx: 0,
        }
    }

    pub fn get_paths(&self) -> &Vec<PathLog> {
        &self.paths
    }

    pub fn get_latest_path(&self) -> Option<&PathLog> {
        self.paths.last()
    }
}
// NOTE: This describes the implementation better.
#[allow(clippy::to_string_trait_impl)]
impl ToString for SubProgram {
    fn to_string(&self) -> String {
        let file = match &self.file {
            Some((name, line)) => format!("<({name}@{line})>"),
            None => String::new(),
        };
        format!("Subprogram({}) {file}", self.name)
    }
}
impl Region for SubProgram {
    fn global() -> Self {
        Self {
            name: "GLOBAL:".to_string(),
            bounds: (0, u64::MAX),
            file: None,
            call_file: None,
        }
    }
}

impl From<RegionMetaData> for SubProgram {
    fn from(value: RegionMetaData) -> Self {
        let RegionMetaData {
            name,
            start,
            end,
            area_delimiter: _,
            instructions: _,
            execution_time: _,
        } = value;

        Self {
            name: name.unwrap_or("".to_string()),
            bounds: (start, end),
            file: None,
            call_file: None,
        }
    }
}

impl Display for SimplePathLogger {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let SimplePathLogger {
            statements,
            final_state,
            result,
            constraints,
            execution_time,
            visited,
            log_idx,
            regions: _regions,
            current_region: _,
            pc: _,
        } = self;

        write!(f, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ PATH {} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\r\n", log_idx)?;
        if !statements.is_empty() {
            write!(f, "Logs:\r\n")?;
            for (program, statement) in statements {
                write!(f, "\t")?;
                if let Some(SubProgram {
                    name,
                    bounds: _,
                    file: Some((file, _line)),
                    call_file: _,
                }) = program
                {
                    write!(f, "<{name} ({file})> -> ")?;
                }
                if let Some(SubProgram {
                    name,
                    bounds: _,
                    file: None,
                    call_file: _,
                }) = program
                {
                    write!(f, "<{name}> -> ")?;
                }

                write!(f, "{}\r\n", statement)?;
            }
        }

        if !visited.is_empty() {
            writeln!(f, "Visited:")?;
            for constraint in visited {
                writeln!(f, "\t{}", constraint)?;
            }
        }
        if !constraints.is_empty() {
            writeln!(f, "Constraints:\r\n")?;
            for constraint in constraints {
                writeln!(f, "\t{}", constraint)?;
            }
        }

        write!(f, "Final state : \r\n\t{}\r\n", final_state)?;
        write!(f, "Execution took : {}\r\n", execution_time)?;

        write!(f, "{}\r\n", result)?;
        Ok(())
    }
}

impl Display for PathLog {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let PathLog {
            statements,
            final_state,
            result,
            constraints,
            execution_time,
            visited,
            log_idx,
        } = self;

        write!(f, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ PATH {} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\r\n", log_idx)?;
        if !statements.is_empty() {
            write!(f, "Logs:\r\n")?;
            for (program, statement) in statements {
                write!(f, "\t")?;
                if let Some(SubProgram {
                    name,
                    bounds: _,
                    file: Some((file, _line)),
                    call_file: _,
                }) = program
                {
                    write!(f, "<{name} ({file})> -> ")?;
                }
                if let Some(SubProgram {
                    name,
                    bounds: _,
                    file: None,
                    call_file: _,
                }) = program
                {
                    write!(f, "<{name}> -> ")?;
                }

                write!(f, "{}\r\n", statement)?;
            }
        }

        if !visited.is_empty() {
            writeln!(f, "Visited:")?;
            for constraint in visited {
                writeln!(f, "\t{}", constraint)?;
            }
        }
        if !constraints.is_empty() {
            writeln!(f, "Constraints:\r\n")?;
            for constraint in constraints {
                writeln!(f, "\t{}", constraint)?;
            }
        }

        write!(f, "Final state : \r\n\t{}\r\n", final_state)?;
        write!(f, "Execution took : {}\r\n", execution_time)?;

        write!(f, "{}\r\n", result)?;
        Ok(())
    }
}
impl Display for SimpleLogger {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let len = self.paths.len();
        for (idx, path) in self.paths.iter().enumerate() {
            if idx == len - 1 {
                continue;
            }
            write!(f, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ PATH {} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\r\n{path}", idx)?;
        }

        Ok(())
    }
}
