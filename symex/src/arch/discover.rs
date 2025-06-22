use object::{File, Object};

use super::{
    arm::{arm_isa, v6::ArmV6M, v7::ArmV7EM, ArmIsa},
    ArchError,
    Architecture,
    NoArchitectureOverride,
    SupportedArchitecture,
    RISCV,
};

impl SupportedArchitecture<NoArchitectureOverride> {
    /// Discovers all supported binary formats from the binary file.
    pub fn discover(obj_file: &File<'_>) -> Result<Self, ArchError> {
        let architecture = obj_file.architecture();

        // Exception here as we will extend this in the future.
        //
        // TODO: Remove this allow when risc-v is done.
        #[allow(clippy::single_match)]
        match architecture {
            object::Architecture::Arm => return discover_arm(obj_file),
            object::Architecture::Riscv32 => return Ok(SupportedArchitecture::RISCV(<RISCV as Architecture<NoArchitectureOverride>>::new())),
            _ => {}
        }
        Err(ArchError::UnsupportedArchitechture)
    }
}

fn discover_arm(file: &File<'_>) -> Result<SupportedArchitecture<NoArchitectureOverride>, ArchError> {
    let f = match file {
        File::Elf32(f) => Ok(f),
        _ => Err(ArchError::IncorrectFileType),
    }?;
    let section = match f.section_by_name(".ARM.attributes") {
        Some(section) => Ok(section),
        None => Err(ArchError::MissingSection(".ARM.attributes")),
    }?;
    let isa = arm_isa(&section)?;
    match isa {
        ArmIsa::ArmV6M => Ok(SupportedArchitecture::Armv6M(<ArmV6M as Architecture<NoArchitectureOverride>>::new())),
        ArmIsa::ArmV7EM => Ok(SupportedArchitecture::Armv7EM(<ArmV7EM as Architecture<NoArchitectureOverride>>::new())),
    }
}
