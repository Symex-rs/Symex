//! Defines the supported ARM architectures
pub mod v6;
pub mod v7;

use object::ObjectSection;

use super::ArchError;

#[non_exhaustive]
#[allow(dead_code)]
pub(super) enum ArmIsa {
    ArmV6M,
    ArmV7EM,
}

pub(super) fn arm_isa<'a, T: ObjectSection<'a>>(section: &T) -> Result<ArmIsa, ArchError> {
    let data = section.data().map_err(|_| ArchError::MalformedSection)?;
    // Magic extraction
    //
    // the index here is from
    // https://github.com/ARM-software/abi-aa/blob/main/addenda32/addenda32.rst
    //
    // so are the f_cpu_arch values
    //
    // This offset might be a bit hacky
    let f_cpu_arch = match data.get(6 * 4 - 1) {
        Some(el) => Ok(el),
        None => Err(ArchError::MalformedSection),
    }?;

    match f_cpu_arch {
        // Cortex-m3, this should really be Arvm7M.
        10 => Ok(ArmIsa::ArmV7EM),

        12 => Ok(ArmIsa::ArmV6M),

        // Cortex-m4
        13 => Ok(ArmIsa::ArmV7EM),

        _ => Err(ArchError::UnsupportedArchitechture),
    }
}
