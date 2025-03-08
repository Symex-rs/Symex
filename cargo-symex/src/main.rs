use std::{
    collections::{HashMap, VecDeque},
    fmt::Display,
    marker::PhantomData,
};

use anyhow::{anyhow, Result};
use clap::Parser;
use log::debug;

const BINARY_NAME: &str = "symex";

mod args;
mod build;

use args::{Args, FunctionArguments, Mode, Solver};
use build::{Features, Settings, Target};
use symex::{
    defaults::logger::SimplePathLogger,
    executor::{hooks::HookContainer, instruction::CycleCount, state::GAState},
    logging::Logger,
    manager::SymexArbiter,
    project::dwarf_helper::SubProgram,
    smt::{SmtExpr, SmtMap},
};

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

    match (args.mode, args.solver) {
        (Mode::Function(FunctionArguments { name }), Solver::Bitwuzla) => run_elf::<symex::defaults::bitwuzla::DefaultComposition>(path, name),
        (Mode::Function(FunctionArguments { name }), Solver::Boolector) => run_elf::<symex::defaults::boolector::DefaultComposition>(path, name),
    }?;

    Ok(())
}
fn run_elf<C: symex::Composition>(path: String, function_name: String) -> Result<()>
where
    C::Logger: Display,
    C::Memory: symex::smt::SmtMap<ProgramMemory = &'static symex::project::Project>,
    C: symex::Composition<Logger = SimplePathLogger, StateContainer = ()>,
{
    let mut executor: SymexArbiter<C> = symex::initiation::SymexConstructor::new(&path)
        .load_binary()
        .unwrap()
        .discover()
        .unwrap()
        .configure_smt::<C::SMT>()
        .compose(|| (), |map| SimplePathLogger::from_sub_programs(map))
        .unwrap();

    let sub_program = executor.get_symbol_map().get_by_name(&function_name).unwrap().clone();
    let result = executor.run(&sub_program.name)?;
    for path in result {
        let (_state, path) = path?;
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
