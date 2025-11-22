use std::fmt::Display;

use colored::Colorize;

use crate::{
    debug,
    executor::{state::GAState, PathResult},
    logging::{Logger, Region, RegionMetaData},
    manager::SymexArbiter,
    project::dwarf_helper::{CallStack, SubProgram, SubProgramMap},
    Composition,
};

#[derive(Clone, Debug)]
#[must_use]
pub struct PathLog {
    statements: Vec<(Option<SubProgram>, String)>,
    final_state: String,
    result: String,
    constraints: Vec<String>,
    execution_time: String,
    visited: Vec<String>,
    backtrace: Vec<(String, String)>,
    function_arguments: Vec<(String, String)>,
    log_idx: usize,
}

#[derive(Clone, Debug)]
#[must_use]
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
    backtrace: Vec<(String, String)>,
    function_arguments: Vec<(String, String)>,
    pc: u64,
}

impl PathLog {
    const fn new(log_idx: usize) -> Self {
        Self {
            statements: Vec::new(),
            final_state: String::new(),
            result: String::new(),
            constraints: Vec::new(),
            execution_time: String::new(),
            visited: Vec::new(),
            backtrace: Vec::new(),
            function_arguments: Vec::new(),
            log_idx,
        }
    }
}

struct PathLogger<'logger> {
    sub_program: &'logger Option<SubProgram>,
    path: &'logger mut PathLog,
}

#[must_use]
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

impl PathLogger<'_> {
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

    fn visit<C: Composition>(&mut self, func: String, _state: &mut GAState<C>) {
        if Some(&func) != self.path.visited.last() {
            // let bt = state.get_back_trace(&[]);
            self.path.visited.push(func);
        }
    }

    fn record_backtrace(&mut self, bt: Option<CallStack>) {
        if bt.is_none() {
            self.path.backtrace = vec![];
            return;
        }
        let bt = bt.unwrap();

        self.path.backtrace = bt
            .final_frame
            .variables
            .iter()
            .map(|var| (var.name.clone().unwrap_or_else(|| "NO NAME".to_string()), var.value.to_string()))
            .collect();
        self.path.function_arguments = bt
            .final_frame
            .arguments
            .iter()
            .map(|var| (var.name.clone().unwrap_or_else(|| "NO NAME".to_string()), var.value.to_string()))
            .collect();
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
            backtrace: Vec::new(),
            function_arguments: Vec::new(),
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
        let subprogram = subprogram.first().cloned();
        // println!("Logging in {subprogram:?}");
        self.statements.push((subprogram, format!("[{}]: {}", "WARN".yellow(), warning.to_string())));
    }

    fn error<T: ToString>(&mut self, warning: T) {
        let subprogram = self.regions.in_bounds(self.pc).first().cloned();
        self.statements.push((subprogram, format!("[{}]: {}", "ERROR".red(), warning.to_string())));
    }

    fn update_delimiter<T: Into<Self::RegionDelimiter>, C: Composition>(&mut self, region: T, _state: &mut GAState<C>) {
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
            PathResult::Success(Some(expression)) => format!("Success ({expression:?})").green(),
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
        let subprogram = subprogram.first().cloned();
        self.statements.push((subprogram, format!("[{}]: {}", "ASSUME".blue(), assumption.to_string())));
    }

    fn current_region(&self) -> Option<Self::RegionIdentifier> {
        self.regions.get_by_address(&self.pc).cloned()
    }

    fn add_constraints(&mut self, constraints: Vec<String>) {
        for constraint in constraints {
            self.constraints.push(format!("[{}]: {constraint}", "CONSTRAINT".yellow()));
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
            backtrace: Vec::new(),
            function_arguments: Vec::new(),
        }
    }

    fn record_backtrace(&mut self, bt: Option<CallStack>) {
        if bt.is_none() {
            self.backtrace = vec![];
            return;
        }
        let bt = bt.unwrap();

        self.backtrace = bt
            .final_frame
            .variables
            .iter()
            .map(|var| (var.name.clone().unwrap_or_else(|| "NO NAME".to_string()), var.value.to_string()))
            .collect();
        self.function_arguments = bt
            .final_frame
            .arguments
            .iter()
            .map(|var| (var.name.clone().unwrap_or_else(|| "NO NAME".to_string()), var.value.to_string()))
            .collect();
    }
}

impl Logger for SimpleLogger {
    type RegionDelimiter = u64;
    type RegionIdentifier = SubProgram;

    fn fork(&self) -> Self {
        self.clone()
    }

    fn update_delimiter<T: Into<Self::RegionDelimiter>, C: crate::Composition>(&mut self, region: T, state: &mut crate::executor::state::GAState<C>) {
        self.pc = region.into();
        self.current_region = self.regions.get_by_address(&self.pc).cloned();
        if let Some(region) = &self.current_region {
            let name = region.name.clone();
            self.path_logger().visit(name, state);
        }
    }

    fn warn<T: ToString>(&mut self, warning: T) {
        self.path_logger().write(format!("[{}]: {}", "WARN".yellow(), warning.to_string()));
    }

    fn record_path_result<C: crate::Composition>(&mut self, path_result: crate::executor::PathResult<C>) {
        let res = format!("Result: {}", match path_result {
            PathResult::Suppress => "Path suppressed".yellow(),
            PathResult::Success(Some(expression)) => format!("Success ({expression:?})").green(),
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
            self.path_logger().constrain(format!("{pc:#x} -> {constraint}"));
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

    fn record_backtrace(&mut self, bt: Option<CallStack>) {
        self.path_logger().record_backtrace(bt);
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

    #[must_use]
    pub const fn get_paths(&self) -> &Vec<PathLog> {
        &self.paths
    }

    #[must_use]
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
            name: name.unwrap_or_default(),
            bounds: (start, end),
            file: None,
            call_file: None,
        }
    }
}

impl Display for SimplePathLogger {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
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
            backtrace: _,
            function_arguments,
        } = self;

        write!(f, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ PATH {log_idx} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\r\n")?;
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

                write!(f, "{statement}\r\n")?;
            }
        }

        if !visited.is_empty() {
            writeln!(f, "Visited:")?;
            for constraint in visited {
                writeln!(f, "\t{constraint}")?;
            }
        }
        if !constraints.is_empty() {
            writeln!(f, "Constraints:\r\n")?;
            for constraint in constraints {
                writeln!(f, "\t{constraint}")?;
            }
        }

        write!(
            f,
            "Named variables : \r\n\t{}\r\n",
            self.backtrace.iter().map(|(name, val)| format!("{name} = {val}")).collect::<Vec<String>>().join("\r\n\t")
        )?;

        write!(
            f,
            "Function arguments: \r\n\t{}\r\n",
            function_arguments
                .iter()
                .map(|(name, val)| format!("{name} = {val}"))
                .collect::<Vec<String>>()
                .join("\r\n\t")
        )?;
        write!(f, "Final state : \r\n\t{final_state}\r\n")?;
        write!(f, "Execution took : {execution_time}\r\n")?;

        write!(f, "{result}\r\n")?;
        Ok(())
    }
}

impl Display for PathLog {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            statements,
            final_state,
            result,
            constraints,
            execution_time,
            visited,
            log_idx,
            backtrace,
            function_arguments,
        } = self;

        write!(f, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ PATH {log_idx} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\r\n")?;
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

                write!(f, "{statement}\r\n")?;
            }
        }

        if !visited.is_empty() {
            writeln!(f, "Visited:")?;
            for constraint in visited {
                writeln!(f, "\t{constraint}")?;
            }
        }
        if !constraints.is_empty() {
            writeln!(f, "Constraints:\r\n")?;
            for constraint in constraints {
                writeln!(f, "\t{constraint}")?;
            }
        }

        write!(
            f,
            "Named variables : \r\n\t{}\r\n",
            backtrace.iter().map(|(name, val)| format!("{name} = {val}")).collect::<Vec<String>>().join("\r\n\t")
        )?;
        write!(
            f,
            "Function arguments: \r\n\t{}\r\n",
            function_arguments
                .iter()
                .map(|(name, val)| format!("{name} = {val}"))
                .collect::<Vec<String>>()
                .join("\r\n\t")
        )?;
        write!(f, "Final state : \r\n\t{final_state}\r\n")?;
        write!(f, "Execution took : {execution_time}\r\n")?;

        write!(f, "{result}\r\n",)?;
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
            write!(f, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ PATH {idx} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\r\n{path}")?;
        }

        Ok(())
    }
}
