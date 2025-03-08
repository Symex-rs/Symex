use clap::Parser;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
pub struct Args {
    /// Reads from elf file
    #[clap(
        long,
        conflicts_with = "bin",
        conflicts_with = "example",
        conflicts_with = "lib",
        conflicts_with = "release",
        conflicts_with = "features",
        conflicts_with = "all_features",
        conflicts_with = "embed_bitcode"
    )]
    pub path: Option<String>,

    /// Build package library.
    #[clap(long, conflicts_with = "bin", conflicts_with = "example")]
    pub lib: Option<bool>,

    /// Builds given example.
    #[clap(long, conflicts_with = "bin", conflicts_with = "lib")]
    pub example: Option<String>,

    /// Builds given binary.
    #[clap(long, conflicts_with = "example", conflicts_with = "lib")]
    pub bin: Option<String>,

    /// Build in release mode.
    #[clap(long)]
    pub release: bool,

    /// List of features to activate.
    #[clap(long)]
    pub features: Vec<String>,

    /// Activate all features.
    #[clap(long)]
    pub all_features: bool,

    /// Name of function to run. Should be a full module path, excluding the
    /// root module.
    #[clap(short, long)]
    pub function: Option<String>,

    #[clap(short, long, default_value = "bitwuzla")]
    /// Denotes the solver to use during analysis.
    pub solver: Solver,

    /// Denotes the mode to run the analysis in.
    #[clap(subcommand)]
    pub mode: Mode,
}

#[derive(Parser, clap::ValueEnum, Debug, Clone)]
/// Enumerates all of the supported solvers.
pub enum Solver {
    /// The bitwuzla solver.
    Bitwuzla,
    // The boolector solver.
    Boolector,
}

#[derive(Parser, Debug)]
/// THe operating mode for the binary.
pub enum Mode {
    /// Analyses a single (or multiple functions).
    Function(FunctionArguments),
}

#[derive(Parser, Debug)]
pub struct FunctionArguments {
    /// The name of the function to analyze.
    pub name: String,
}
