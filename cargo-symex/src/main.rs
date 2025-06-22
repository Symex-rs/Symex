#![deny(warnings, clippy::all)]

use anyhow::{anyhow, Result};
use clap::Parser;
use log::debug;

const BINARY_NAME: &str = "symex";

mod args;
mod build;

use args::{Args, FunctionArguments, Mode, Solver};
use build::{Features, Settings, Target};
use symex::{arch::NoArchitectureOverride, defaults::logger::SimplePathLogger, executor::hooks::LangagueHooks, manager::SymexArbiter};

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    match run() {
        Ok(_) => {}
        Err(err) => {
            eprintln!("{err}");
        }
    }
    Ok(())
}
fn run() -> Result<()> {
    let mut args = std::env::args().collect::<Vec<_>>();
    debug!("received arguments: {args:?}");

    // If this is run as a cargo subcommand, the second argument will be the name of
    // this binary. So remove this if this is the case.
    if args.get(1).map(|s| s.as_str() == BINARY_NAME).unwrap_or(false) {
        debug!("used as cargo subcommand: removing {BINARY_NAME} as second argument");
        args.remove(1);
    }

    let args = Args::parse_from(args);
    std::env::set_var("SYMEX", "true");

    use crate::build::generate_binary_build_command;

    debug!("Run elf file.");
    let path = match args.path.clone() {
        Some(path) => path,
        None => {
            let opts = settings_from_args(&args);

            // Build LLVM BC file.
            let cargo_out = generate_binary_build_command(&opts).status()?;
            debug!("cargo output: {cargo_out:?}");
            if !cargo_out.success() {
                return Err(anyhow!("Failed to build using cargo sub command"));
            }

            // Create path to .bc file.
            let target_dir = opts.get_target_dir()?;
            let target_name = opts.get_target_name()?;

            debug!("target dir: {:?}, target name: {}", target_dir, target_name);
            format!("{}/{}", target_dir.to_str().unwrap(), target_name)
        }
    };

    #[cfg(any(feature = "bitwuzla", feature = "boolector"))]
    match (args.mode, args.solver) {
        #[cfg(feature = "bitwuzla")]
        (Mode::Function(FunctionArguments { name }), Solver::Bitwuzla) => run_elf::<symex::defaults::bitwuzla::DefaultComposition>(path, name, LangagueHooks::Rust),
        #[cfg(feature = "boolector")]
        (Mode::Function(FunctionArguments { name }), Solver::Boolector) => run_elf::<symex::defaults::boolector::DefaultComposition>(path, name, LangagueHooks::Rust),
    }?;

    Ok(())
}
fn run_elf<C>(path: String, function_name: String, language: LangagueHooks) -> Result<()>
where
    C: symex::Composition<Logger = SimplePathLogger, StateContainer = (), ArchitectureOverride = NoArchitectureOverride>,
    C::Memory: symex::smt::SmtMap<ProgramMemory = &'static symex::project::Project>,
{
    let mut executor: SymexArbiter<C> = symex::initiation::SymexConstructor::new(&path)
        .load_binary()
        .unwrap()
        .discover()
        .unwrap()
        .configure_smt::<C::SMT>()
        .compose(|| (), SimplePathLogger::from_sub_programs)
        .unwrap();

    let sub_program = executor.get_symbol_map().get_by_name(&function_name).unwrap().clone();
    let result = executor.run(&sub_program.name, language)?;
    for path in result {
        let (_state, path, _result) = path?;
        println!("{path}");
    }

    Ok(())
}

fn settings_from_args(opts: &Args) -> Settings {
    let target = if let Some(name) = &opts.bin {
        Target::Bin(name.clone())
    } else if let Some(name) = &opts.example {
        Target::Example(name.clone())
    } else {
        Target::Lib
    };

    let features = if opts.all_features {
        Features::All
    } else if opts.features.is_empty() {
        Features::None
    } else {
        Features::Some(opts.features.clone())
    };

    Settings {
        target,
        features,
        release: opts.release,
    }
}
