use std::{env, path::PathBuf, process::Command};

use anyhow::{anyhow, Result};
use cargo_project::{Artifact, Profile, Project};

/// Build settings.
pub struct Settings {
    /// Target to use, e.g. binary, example or lib.
    pub target: Target,

    /// The features to activate, if any.
    pub features: Features,

    /// Build in release.
    pub release: bool,
}

impl Settings {
    /// Return the path to the target directory for the project.
    pub fn get_target_dir(&self) -> Result<PathBuf> {
        let artifact = match &self.target {
            Target::Bin(name) => Artifact::Bin(name),
            Target::Example(name) => Artifact::Example(name),
            Target::Lib => Artifact::Lib,
        };

        let profile = match self.release {
            true => Profile::Release,
            false => Profile::Dev,
        };

        let cwd = env::current_dir()?;
        let meta = rustc_version::version_meta()?;
        let project = Project::query(cwd).map_err(|err| anyhow!(err.to_string()))?;
        let host = meta.host;
        let mut path = project.path(artifact, profile, None, &host).map_err(|err| anyhow::anyhow!("{err}"))?;
        path = path.parent().expect("unreachable").to_path_buf();

        // Binary files --bin are in the `/deps` folder.
        if matches!(artifact, Artifact::Bin(_)) {
            //path = path.join("deps");
        }

        Ok(path)
    }

    /// Returns the name of the built target.
    pub fn get_target_name(&self) -> Result<String> {
        let cwd = env::current_dir()?;
        let project = Project::query(cwd).map_err(|err| anyhow!(err.to_string()))?;

        let name = match &self.target {
            Target::Bin(name) => name.clone(),
            Target::Example(name) => name.clone(),
            Target::Lib => project.name().to_string(),
        };

        // Target names have `-` replaced with `_`.
        let name = name.replace('-', "_");
        Ok(name)
    }
}

pub enum Target {
    Bin(String),
    Example(String),
    Lib,
}

pub enum Features {
    None,
    Some(Vec<String>),
    All,
}

pub fn generate_binary_build_command(opts: &Settings) -> Command {
    let mut cargo = Command::new("cargo");
    cargo.args(["build"]);
    match &opts.features {
        Features::None => {}
        Features::Some(features) => {
            cargo.args(["--features", &features.join(",")]);
        }
        Features::All => {
            cargo.arg("--all-features");
        }
    };

    match &opts.target {
        Target::Bin(name) => cargo.args(["--bin", name]),
        Target::Example(name) => cargo.args(["--example", name]),
        Target::Lib => cargo.arg("--lib"),
    };

    if opts.release {
        cargo.arg("--release");
    }

    cargo
}
