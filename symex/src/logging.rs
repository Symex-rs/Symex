use std::hash::Hash;

use crate::{
    executor::{state::GAState, PathResult},
    manager::SymexArbiter,
    Composition,
};

/// Denotes meta data regarding a region of code.
#[derive(Hash, Clone)]
pub struct RegionMetaData {
    /// Region label if any.
    pub name: Option<String>,
    /// Start value for delimiter.
    pub start: u64,
    /// End value for delimiter.
    pub end: u64,
    /// Typically delimited by PC.
    pub area_delimiter: String,

    /// The instructions contained in the region.
    pub instructions: Vec<String>,

    /// The instructions contained in the region.
    pub execution_time: Vec<String>,
}

/// The execution does not use a logger.
#[derive(Hash, Clone, Debug)]
pub struct NoLogger;

pub trait Region {
    /// Returns the global scope.
    fn global() -> Self;
}

/// A generic logger used to generate reports.
///
///
/// Will not work in a multi threaded context as of now.
pub trait Logger: Clone + core::fmt::Debug {
    type RegionIdentifier: Sized + ToString + From<RegionMetaData> + Hash + Region;
    type RegionDelimiter: Hash + ToString + From<u64>;

    /// Assumes that the constraint holds.
    fn assume<T: ToString>(&mut self, assumption: T);

    /// An issue occurred, non terminal but might be problematic.
    fn warn<T: ToString>(&mut self, warning: T);

    /// An issue occurred, probably terminal for the current path.
    fn error<T: ToString>(&mut self, error: T);

    /// Records the result of the current path.
    fn record_path_result<C: Composition>(&mut self, path_result: PathResult<C>);

    /// Records the final state of the current path.
    fn record_final_state<C: Composition>(&mut self, state: GAState<C>);

    /// Changes to a new path in the executor.
    ///
    /// If this is path has been partially explored before it will simply append
    /// to the previous logs.
    fn set_path_idx(&mut self, new_path_idx: usize);

    fn fork(&self) -> Self {
        self.clone()
    }

    /// Adds constraint info to the currently executing path.
    fn add_constraints(&mut self, constraints: Vec<String>);

    /// Report of execution time, typically this will include a set of meta data
    /// instructions such as start PC end PC etc.
    fn record_execution_time<T: ToString>(&mut self, time: T);

    /// Returns the current region if any is detected.
    fn current_region(&self) -> Option<Self::RegionIdentifier>;

    /// Adds a new region to the logger.
    fn register_region(&mut self, region: Self::RegionIdentifier);

    /// Adds a new region to the logger.
    fn update_delimiter<T: Into<Self::RegionDelimiter>>(&mut self, region: T);

    fn new<C: Composition>(state: &SymexArbiter<C>) -> Self;
}

impl Logger for NoLogger {
    type RegionDelimiter = u64;
    type RegionIdentifier = RegionMetaData;

    fn warn<T: ToString>(&mut self, _warning: T) {}

    fn error<T: ToString>(&mut self, _error: T) {}

    fn assume<T: ToString>(&mut self, _assumption: T) {}

    fn record_execution_time<T: ToString>(&mut self, _time: T) {}

    fn set_path_idx(&mut self, _: usize) {}

    fn add_constraints(&mut self, _constraints: Vec<String>) {}

    fn current_region(&self) -> Option<Self::RegionIdentifier> {
        None
    }

    fn record_final_state<C: Composition>(&mut self, _state: GAState<C>) {}

    fn register_region(&mut self, _region: Self::RegionIdentifier) {}

    fn record_path_result<C: Composition>(&mut self, _path_result: PathResult<C>) {}

    fn update_delimiter<T: Into<Self::RegionDelimiter>>(&mut self, _region: T) {}

    fn new<C: Composition>(_state: &SymexArbiter<C>) -> Self {
        Self
    }
}

impl From<RegionMetaData> for NoLogger {
    fn from(_value: RegionMetaData) -> Self {
        NoLogger
    }
}

impl ToString for RegionMetaData {
    fn to_string(&self) -> String {
        let area_delimiter = self.area_delimiter.clone();
        format!(
            "region (name: \\bold{{{}}} from $`{area_delimiter} = {}`$ to $`{area_delimiter} = {}`$",
            self.name.as_ref().map_or("No name", |v| v),
            self.start,
            self.end
        )
    }
}

impl Region for RegionMetaData {
    fn global() -> Self {
        Self {
            name: Some("Global scope".to_string()),
            start: 0,
            end: u64::MAX,
            area_delimiter: "PC".to_string(),
            instructions: vec![],
            execution_time: vec![],
        }
    }
}
