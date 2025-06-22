#![allow(dead_code, missing_docs)]
use std::{fmt::Display, path::PathBuf};

use gimli::{DebugAbbrev, DebugInfo, DebugLine, DebugStr};
use hashbrown::HashMap;
use object::{Object, ObjectSection, ObjectSymbol};

use crate::{
    arch::{ArchitectureOverride, NoArchitectureOverride, SupportedArchitecture},
    debug,
    error,
    executor::hooks::HookContainer,
    manager::SymexArbiter,
    project::{
        dwarf_helper::{line_program, DebugData, LineMap, SubProgramMap},
        Project,
        ProjectError,
    },
    smt::{SmtMap, SmtSolver},
    Composition,
    Endianness,
};

mod sealed {
    pub trait ArchOverride: Clone {}
    pub trait SmtSolverConfigured: Clone {}
    pub trait BinaryLoadingDone: Clone {}
}
use sealed::*;

#[doc(hidden)]
#[derive(Debug)]
/// SMT solver has been configured.
pub struct SmtConfigured<Smt: SmtSolver> {
    smt: Smt,
}

impl<Smt: SmtSolver> Clone for SmtConfigured<Smt> {
    fn clone(&self) -> Self {
        Self { smt: Smt::new() }
    }
}

#[doc(hidden)]
#[derive(Debug, Clone)]
/// SMT solver has not been configured.
pub struct SmtNotConfigured;

#[doc(hidden)]
#[derive(Debug)]
/// Binary file loaded.
pub struct BinaryLoaded<'file> {
    object: object::File<'file>,
    path: String,
}

impl Clone for BinaryLoaded<'static> {
    fn clone(&self) -> Self {
        let file = std::fs::read(self.path.clone())
            .map_err(|e| crate::GAError::CouldNotOpenFile(e.to_string()))
            .expect("Faulty path");
        let data = &(*file.leak());
        let obj_file = match object::File::parse(data) {
            Ok(x) => x,
            Err(_e) => {
                error!("Could not parse file that had already been parsed");
                unreachable!("Could not parse file that had already been parsed");
            }
        };
        Self {
            object: obj_file,
            path: self.path.clone(),
        }
    }
}

#[doc(hidden)]
#[derive(Debug, Clone)]
/// Binary not loaded.
pub struct BinaryNotLoaded;

#[doc(hidden)]
#[derive(Debug, Clone)]
/// No architecture specified.
pub struct NoArchOverride;

#[derive(Clone)]
/// Constructs the symex virtual machine to run with the desired settings.
///
/// See [`defaults`](crate::defaults) for default configurations.
pub struct SymexConstructor<'str, Override: ArchOverride, Smt: SmtSolverConfigured, Binary: BinaryLoadingDone> {
    file: &'str str,
    override_arch: Override,
    smt: Smt,
    binary_file: Binary,
}

impl<'str> SymexConstructor<'str, NoArchOverride, SmtNotConfigured, BinaryNotLoaded> {
    /// Begins the [`SymexArbiter`] initiation.
    pub const fn new(path: &'str str) -> Self {
        Self {
            file: path,
            override_arch: NoArchOverride,
            smt: SmtNotConfigured,
            binary_file: BinaryNotLoaded,
        }
    }
}

impl<'str, S: SmtSolverConfigured, B: BinaryLoadingDone> SymexConstructor<'str, NoArchOverride, S, B> {
    pub fn override_architecture<Override: ArchitectureOverride>(self, a: Override) -> SymexConstructor<'str, SupportedArchitecture<Override>, S, B> {
        SymexConstructor::<'str, SupportedArchitecture<Override>, S, B> {
            file: self.file,
            override_arch: a.into(),
            smt: self.smt,
            binary_file: self.binary_file,
        }
    }
}

impl<'str, A: ArchOverride, B: BinaryLoadingDone> SymexConstructor<'str, A, SmtNotConfigured, B> {
    pub fn configure_smt<S: SmtSolver>(self) -> SymexConstructor<'str, A, SmtConfigured<S>, B> {
        SymexConstructor {
            file: self.file,
            override_arch: self.override_arch,
            smt: SmtConfigured::<S> { smt: S::new() },
            binary_file: self.binary_file,
        }
    }
}

impl<'str, A: ArchOverride, S: SmtSolverConfigured> SymexConstructor<'str, A, S, BinaryNotLoaded> {
    pub fn load_binary(self) -> crate::Result<SymexConstructor<'str, A, S, BinaryLoaded<'static>>> {
        let file = std::fs::read(self.file).map_err(|e| crate::GAError::CouldNotOpenFile(e.to_string()))?;
        let data = &(*file.leak());
        let obj_file = match object::File::parse(data) {
            Ok(x) => x,
            Err(e) => {
                debug!("Error: {}", e);
                let _ = e;
                let mut ret = PathBuf::new();
                ret.push(self.file);

                return Err(crate::GAError::ProjectError(ProjectError::UnableToParseElf(ret.display().to_string())))?;
            }
        };
        Ok(SymexConstructor {
            file: self.file,
            override_arch: self.override_arch,
            smt: self.smt,
            binary_file: BinaryLoaded {
                object: obj_file,
                path: self.file.to_string(),
            },
        })
    }
}

impl<'str, S: SmtSolverConfigured> SymexConstructor<'str, NoArchOverride, S, BinaryLoaded<'static>> {
    pub fn discover(self) -> crate::Result<SymexConstructor<'str, SupportedArchitecture<NoArchitectureOverride>, S, BinaryLoaded<'static>>> {
        let arch = SupportedArchitecture::discover(&self.binary_file.object)?;

        Ok(SymexConstructor {
            file: self.file,
            override_arch: arch,
            smt: self.smt,
            binary_file: self.binary_file,
        })
    }
}

impl<'str, S: SmtSolver, Override: ArchitectureOverride> SymexConstructor<'str, SupportedArchitecture<Override>, SmtConfigured<S>, BinaryLoaded<'static>> {
    pub fn compose<C, StateCreator: FnOnce() -> C::StateContainer, LoggingCreator: FnOnce(&SubProgramMap) -> C::Logger>(
        self,
        user_state_composer: StateCreator,
        logger: LoggingCreator,
    ) -> crate::Result<SymexArbiter<C>>
    where
        C::Memory: SmtMap<ProgramMemory = &'static Project>,
        C: Composition<SMT = S, ArchitectureOverride = Override>,
        //C: Composition<StateContainer = Box<A>>,
    {
        let binary = self.binary_file.object;
        let smt = self.smt.smt;

        let endianness = if binary.is_little_endian() { Endianness::Little } else { Endianness::Big };

        let mut symtab = HashMap::new();
        for symbol in binary.symbols() {
            symtab.insert(
                match symbol.name() {
                    Ok(name) => name.to_owned(),
                    Err(_) => continue, // Ignore entry if name can not be read
                },
                symbol.address(),
            );
        }

        let gimli_endian = match endianness {
            Endianness::Little => gimli::RunTimeEndian::Little,
            Endianness::Big => gimli::RunTimeEndian::Big,
        };

        let debug_info = binary.section_by_name(".debug_info").unwrap();
        let debug_info = DebugInfo::new(debug_info.data().unwrap(), gimli_endian);

        let debug_abbrev = binary.section_by_name(".debug_abbrev").unwrap();
        let debug_abbrev = DebugAbbrev::new(debug_abbrev.data().unwrap(), gimli_endian);

        let debug_str = binary.section_by_name(".debug_str").unwrap();
        let debug_str = DebugStr::new(debug_str.data().unwrap(), gimli_endian);
        let debug_line = DebugLine::new(binary.section_by_name(".debug_line").unwrap().data().unwrap(), gimli_endian);

        let mut map = SubProgramMap::new(&debug_info, &debug_abbrev, &debug_str, &debug_line);
        map.insert_symtab(symtab);
        let mut hooks = HookContainer::default(&map)?;
        self.override_arch.add_hooks(&mut hooks, &mut map);

        let project = Box::new(Project::from_binary(&binary, map.clone())?);
        let project = Box::leak(project);
        let line_map = line_program(&binary, gimli_endian).unwrap_or(LineMap::empty());
        let debug_data = DebugData::new(Box::leak(Box::new(binary)), gimli_endian).expect("Debug data to be created");

        Ok(SymexArbiter::<C>::new(
            logger(&map),
            project,
            smt,
            user_state_composer(),
            hooks,
            map,
            self.override_arch,
            line_map,
            debug_data,
        ))
    }
}

impl Display for NoArchOverride {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Not overriding architecture")
    }
}

impl<Override: ArchitectureOverride> ArchOverride for SupportedArchitecture<Override> {}
impl ArchOverride for NoArchOverride {}

impl SmtSolverConfigured for SmtNotConfigured {}

impl<S: SmtSolver> SmtSolverConfigured for SmtConfigured<S> {}

impl BinaryLoadingDone for BinaryNotLoaded {}
impl BinaryLoadingDone for BinaryLoaded<'static> {}

//let context = Box::new(DContext::new());
//    let context = Box::leak(context);
//
//    let end_pc = 0xFFFFFFFE;
//
//    debug!("Parsing elf file: {}", path);
//    let file = fs::read(path).expect("Unable to open file.");
//    let data = file.as_ref();
//    let obj_file = match object::File::parse(data) {
//        Ok(x) => x,
//        Err(e) => {
//            debug!("Error: {}", e);
//            return Err(ProjectError::UnableToParseElf(path.to_owned()))?;
//        }
//    };
//
//    add_architecture_independent_hooks(&mut cfg);
//    let project = Box::new(Project::from_path(&mut cfg, obj_file,
// &architecture)?);    let project = Box::leak(project);
//    project.add_pc_hook(end_pc, PCHook::EndSuccess);
//    debug!("Created project: {:?}", project);
//
//    let mut vm = VM::new(project, context, function, end_pc, architecture)?;
//    run_elf_paths(&mut vm, &cfg)
