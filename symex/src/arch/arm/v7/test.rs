use disarmv7::prelude::{operation::*, *};
use general_assembly::{
    operand::{DataWord, Operand},
    operation::Operation as GAOperation,
};
use hashbrown::HashMap;

use super::ArmV7EM;
use crate::{
    arch::{arm::v7::decoder::*, Architecture},
    defaults::bitwuzla::DefaultCompositionNoLogger,
    executor::{
        hooks::HookContainer,
        instruction::{CycleCount, Instruction},
        state::GAState,
        vm::VM,
        GAExecutor,
    },
    logging::NoLogger,
    project::{dwarf_helper::SubProgramMap, Project},
    smt::{bitwuzla::Bitwuzla, SmtExpr, SmtSolver},
    Endianness,
    WordSize,
};

macro_rules! get_operand {
    ($exec:ident register $id:ident) => {{
        let operand = Operand::Register(stringify!($id).to_owned());
        let local = HashMap::new();
        $exec
            .get_operand_value(&operand, &local, &mut crate::logging::NoLogger)
            .expect("Could not find a test specified register")
            .get_constant()
            .expect("Could not get test specified register as constant")
    }};
    ($exec:ident flag $id:ident) => {{
        let operand = Operand::Flag(stringify!($id).to_owned());
        let local = HashMap::new();
        $exec
            .get_operand_value(&operand, &local, &mut crate::logging::NoLogger)
            .expect("Could not find a test specified flag")
            .get_constant()
            .expect("Could not get test specified flag as constant")
    }};
    ($exec:ident address $id:literal $width:literal) => {{
        let operand = Operand::Address(general_assembly::operand::DataWord::Word32($id), $width as u32);
        let local = HashMap::new();
        $exec
            .get_operand_value(&operand, &local, &mut crate::logging::NoLogger)
            .expect("Could not find a test specified flag")
            .get_constant()
            .expect("Could not get test specified flag as constant")
    }};
}

/// This can be miss used but will fail at compile time if not correctly
/// structured.
macro_rules! test {
    ($exec:ident {
        $(
            $(
                register $reg:ident
            )?
            $(
                flag $flag:ident
            )?
            $(
                address ($address:literal,$width:literal)
            )?

            $(== $eq_rhs:literal)?
            $(!= $neq_rhs:literal)?
            $(== ($eq_rhs_expr:expr_2021))?
            $(!= ($neq_rhs_expr:expr_2021))?
        ),*
    }) => {
        $(
            let result = get_operand!(
                $exec $(register $reg)? $(address $address $width)? $(flag $flag)?
            );

            println!("{} = {}",
                stringify!(
                    $($reg)?
                    $($address)?
                    $($flag)?
                    $(!= $eq_rhs)?
                    $(== $neq_rhs)?
                    $(!= $eq_rhs_expr)?
                    $(== $neq_rhs_expr)?
                ),result);
            assert!(
                result
                $(== $eq_rhs)?
                $(!= $neq_rhs)?
                $(!= $eq_rhs_expr)?
                $(== $neq_rhs_expr)?,

                stringify!(
                    $($reg)?
                    $($address)?
                    $($flag)?
                    $(!= $eq_rhs)?
                    $(== $neq_rhs)?
                    $(!= $eq_rhs_expr)?
                    $(== $neq_rhs_expr)?
                )
            );
        )*

    };
}

/// This can be misused but will fail at compile time if not correctly
/// structured.
macro_rules! initiate {
    ($exec:ident {
        $(
            $(
                register $reg:ident
            )?
            $(
                flag $flag:ident
            )?
            $(
                address ($address:literal,$width:literal)
            )?

            = $eq_value:expr_2021
        );*
    }) => {
        $(
            let operand = initiate!($exec $(register $reg)? $(address $address $width)? $(flag $flag)?);
            let intermediate = Operand::Immediate(general_assembly::operand::DataWord::Word32($eq_value as u32));
            let operation = general_assembly::operation::Operation::Move { destination: operand, source: intermediate};
            $exec.execute_operation(&operation,&mut HashMap::new(),&mut crate::logging::NoLogger).expect("Malformed test");
        )*

    };

    ($exec:ident register $id:ident) => {
        Operand::Register(stringify!($id).to_owned())
    };

    ($exec:ident flag $id:ident) => {
        Operand::Flag(stringify!($id).to_owned())
    };

    ($exec:ident address $id:literal $width:literal) => {
        Operand::Address(general_assembly::operand::DataWord::Word32($id), $width as u32)
    };
}

fn setup_test_vm() -> VM<DefaultCompositionNoLogger> {
    let ctx = Bitwuzla::new();
    let project_global = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
    let project: &'static Project = Box::leak(project_global);
    let mut hooks = HookContainer::new();
    ArmV7EM {}.add_hooks(&mut hooks, &mut SubProgramMap::empty());
    let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
        project,
        ctx.clone(),
        ctx.clone(),
        0,
        0,
        hooks,
        (),
        crate::arch::SupportedArchitecture::Armv7EM(ArmV7EM::new()),
    );
    VM::new_test_vm(project, state, NoLogger).unwrap()
}

#[test]
fn test_adc_no_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 2;
        register R2 = 3;
        flag C = true
    });

    let instruction: Operation = AdcRegister::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 6,
        flag C == 1
    });
}

#[test]
fn test_adc_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 2;
        register R2 = 3;
        flag C = true
    });

    let instruction: Operation = AdcRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(None)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 6,
        flag C == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        register R2 = 0x80000000;
        flag C = false
    });

    let instruction: Operation = AdcRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag V == 1
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        register R2 = 0x80000000;
        flag C = false;
        flag V = false;
        flag Z = false
    });

    let instruction: Operation = AdcRegister::builder()
        .set_s(Some(SetFlags::InITBlock(true)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(true),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag V == 1
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        register R2 = 0x80000000;
        flag C = false;
        flag V = false;
        flag Z = false
    });

    let instruction: Operation = AdcRegister::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(true),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 0,
        flag Z == 0,
        flag V == 0
    });
}

#[test]
fn test_adc_imm_no_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 2;
        flag C = true
    });

    let instruction: Operation = AdcImmediate::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(3)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 6,
        flag C == 1
    });
}
#[test]
fn test_adc_immediate_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 2;
        register R2 = 3;
        flag C = true
    });

    let instruction: Operation = AdcImmediate::builder().set_s(Some(true)).set_rd(None).set_rn(Register::R1).set_imm(3).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 6,
        flag C == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        flag C = false
    });

    let instruction: Operation = AdcImmediate::builder()
        .set_s(Some(true))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(0x80000000)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag V == 1
    });
}

#[test]
fn test_add_no_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 2;
        register R2 = 3;
        flag C = true
    });

    let instruction: Operation = AddRegister::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 5,
        flag C == 1
    });
}

#[test]
fn test_add_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 2;
        register R2 = 3;
        flag C = true
    });

    let instruction: Operation = AddRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(None)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 5,
        flag C == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        register R2 = 0x80000000;
        flag C = false
    });

    let instruction: Operation = AddRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag V == 1
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        register R2 = 0x80000000;
        flag C = true;
        flag V = false;
        flag Z = false
    });

    let instruction: Operation = AddRegister::builder()
        .set_s(Some(SetFlags::InITBlock(true)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(true),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag V == 1
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        register R2 = 0x80000000;
        flag C = false;
        flag V = false;
        flag Z = false
    });

    let instruction: Operation = AddRegister::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(true),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 0,
        flag Z == 0,
        flag V == 0
    });
}

#[test]
fn test_add_imm_no_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 2;
        flag C = true
    });

    let instruction: Operation = AdcImmediate::builder().set_s(Some(false)).set_rd(None).set_rn(Register::R1).set_imm(3).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 6,
        flag C == 1
    });
}

#[test]
fn test_add_immediate_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 2;
        register R2 = 3;
        flag C = true
    });

    let instruction: Operation = AdcImmediate::builder()
        .set_s(Some(true))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(3)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 6,
        flag C == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x80000000;
        flag C = false
    });

    let instruction: Operation = AdcImmediate::builder()
        .set_s(Some(true))
        .set_rd(None)
        .set_rn(Register::R1)
        .set_imm(0x80000000)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag V == 1
    });
}

#[test]
fn test_add_sp_immediate() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 8;
        register SP = 8;
        register PC = 0;
        flag C = true
    });

    let instruction: Operation = AddSPImmediate::builder().set_s(Some(true)).set_rd(None).set_imm(16).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 24,
        flag C == 0
    });

    initiate!(executor {
        register R1 = 8;
        register SP = 9;
        flag C = true
    });

    let instruction: Operation = AddSPImmediate::builder().set_s(Some(false)).set_rd(Some(Register::SP)).set_imm(16).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 24,
        flag C == 1
    });

    initiate!(executor {
        register R1 = 8;
        register SP = 9;
        flag C = true
    });

    let instruction: Operation = AddSPImmediate::builder().set_s(Some(false)).set_rd(Some(Register::R1)).set_imm(16).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 24,
        flag C == 1
    });
}

#[test]
fn test_add_sp_reg() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 16;
        register SP = 8;
        flag C = true
    });

    let instruction: Operation = AddSPRegister::builder()
        .set_s(Some(true))
        .set_rd(Some(Register::SP))
        .set_rm(Register::R1)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 24,
        flag C == 0
    });

    initiate!(executor {
        register R1 = 16;
        register SP = 9;
        flag C = true
    });

    let instruction: Operation = AddSPRegister::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::SP))
        .set_rm(Register::R1)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 24,
        flag C == 1
    });

    initiate!(executor {
        register R1 = 8;
        register SP = 9;
        flag C = true
    });

    let instruction: Operation = AddSPRegister::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::SP))
        .set_rm(Register::R1)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 24,
        flag C == 1
    });
}

#[test]
fn test_adr() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 16;
        flag C = true
    });

    let instruction: Operation = Adr::builder().set_rd(Register::PC).set_imm(4).set_add(true).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 24
    });

    initiate!(executor {
        register PC = 16;
        flag C = true
    });

    let instruction: Operation = Adr::builder().set_rd(Register::PC).set_imm(4).set_add(false).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 16
    });

    initiate!(executor {
        register R0 = 16;
        flag C = true
    });

    let instruction: Operation = Adr::builder().set_rd(Register::R0).set_imm(4).set_add(false).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R0 == 16
    });
}

#[test]
fn test_and_no_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x00000002;
        register R2 = 0x80000001;
        flag C = true
    });

    let instruction: Operation = AndRegister::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b10,
        flag C == 1
    });
}

#[test]
fn test_and_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x00000002;
        register R2 = 0x80000001;
        flag C = false
    });

    let instruction: Operation = AndRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(None)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b10,
        flag C == 1
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x00000002;
        register R2 = 0x80000002;
        flag C = false
    });

    let instruction: Operation = AndRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b00,
        flag C == 1,
        flag Z == 1,
        flag N == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x00000002;
        register R2 = 0x80000002;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = AndRegister::builder()
        .set_s(Some(SetFlags::InITBlock(true)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(true),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b00,
        flag C == 1,
        flag Z == 1,
        flag N == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x00000002;
        register R2 = 0x80000002;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = AndRegister::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b00,
        flag C == 1,
        flag Z == 1,
        flag N == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x00000002;
        register R2 = 0x80000002;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = AndRegister::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(None)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b00,
        flag C == 1,
        flag Z == 1,
        flag N == 0
    });
}

#[test]
fn test_and_imm_no_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 2;
        flag C = true
    });

    let instruction: Operation = AdcImmediate::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(3)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 6,
        flag C == 1
    });
}

#[test]
fn test_and_immediate_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x00000002;
        flag C = false
    });

    let instruction: Operation = AndImmediate::builder()
        .set_s(Some(true))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(0x00000002)
        .set_carry(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };

    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b10,
        flag C == 1
    });

    initiate!(executor {
        register R1 = 0x00000002;
        flag C = false
    });

    let instruction: Operation = AndImmediate::builder()
        .set_s(Some(true))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(0x00000002)
        .set_carry(Some(false))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };

    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b10,
        flag C == 0
    });

    initiate!(executor {
        register R0 = 1;
        register R1 = 0x00000002;
        register R2 = 0x80000002;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    initiate!(executor {
        register R1 = 0x00000002;
        flag C = false
    });

    let instruction: Operation = AndImmediate::builder()
        .set_s(Some(true))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(0x00000000)
        .set_carry(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };

    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0b00,
        flag C == 0
    });

    initiate!(executor {
        register R1 = 0x80000002;
        flag C = false
    });

    let instruction: Operation = AndImmediate::builder()
        .set_s(Some(true))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R1)
        .set_imm(0x80000000)
        .set_carry(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };

    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80000000,
        flag C == 0,
        flag N == 1
    });
}

#[test]
fn test_asr_immediate() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x80000000;
        flag C = true
    });

    let instruction: Operation = AsrImmediate::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rd(Register::R1)
        .set_rm(Register::R1)
        .set_imm(1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0xc0000000,
        flag C == 1
    });
}

#[test]
fn test_asr_immediate_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x80000001;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrImmediate::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Register::R1)
        .set_rm(Register::R1)
        .set_imm(1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0xc0000000,
        flag C == 1,
        flag N == 1
    });

    initiate!(executor {
        register R1 = 0x00000001;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrImmediate::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Register::R1)
        .set_rm(Register::R1)
        .set_imm(1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x00000000,
        flag C == 1,
        flag Z == 1
    });

    initiate!(executor {
        register R1 = 0x80000001;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrImmediate::builder()
        .set_s(Some(SetFlags::InITBlock(true)))
        .set_rd(Register::R1)
        .set_rm(Register::R1)
        .set_imm(1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(true),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0xc0000000,
        flag C == 1,
        flag N == 1
    });

    initiate!(executor {
        register R1 = 0x00000001;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrImmediate::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(Register::R1)
        .set_rm(Register::R1)
        .set_imm(1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x00000000,
        flag C == 1,
        flag Z == 1
    });
}

#[test]
fn test_asr() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x80000000;
        register R2 = 1;
        flag C = true
    });

    let instruction: Operation = AsrRegister::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rd(Register::R1)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0xc0000000,
        flag C == 1
    });
}

#[test]
fn test_asr_set_flag() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x80000001;
        register R2 = 1;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Register::R1)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0xc0000000,
        flag C == 1,
        flag N == 1
    });

    initiate!(executor {
        register R1 = 0x00000001;
        register R2 = 1;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Register::R1)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x00000000,
        flag C == 1,
        flag Z == 1
    });

    initiate!(executor {
        register R1 = 0x80000001;
        register R2 = 1;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrRegister::builder()
        .set_s(Some(SetFlags::InITBlock(true)))
        .set_rd(Register::R1)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(true),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0xc0000000,
        flag C == 1,
        flag N == 1
    });

    initiate!(executor {
        register R1 = 0x00000001;
        register R2 = 1;
        flag C = false;
        flag Z = false;
        flag N = false
    });

    let instruction: Operation = AsrRegister::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(Register::R1)
        .set_rn(Register::R1)
        .set_rm(Register::R2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x00000000,
        flag C == 1,
        flag Z == 1
    });
}

#[test]
fn test_b() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80000000;
        register R2 = 1;
        flag C = true
    });

    let instruction: Operation = B::builder().set_condition(Condition::None).set_imm(1230).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 1234
    });
}

#[test]
fn test_b_conditional() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80000000;
        register R2 = 1;
        flag C = true
    });
    println!("Init done! {}", executor.state.memory);

    let instruction: Operation = B::builder().set_condition(Condition::Cs).set_imm(1230).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 1234
    });

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80000000;
        register R2 = 1;
        flag C = true
    });

    let instruction: Operation = B::builder().set_condition(Condition::Cc).set_imm(1230).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 2
    });

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80000000;
        register R2 = 1;
        flag V = true
    });

    let instruction: Operation = B::builder().set_condition(Condition::Vs).set_imm(1230).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 1234
    });

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80000000;
        register R2 = 1;
        flag V = true
    });

    let instruction: Operation = B::builder().set_condition(Condition::Vc).set_imm(1230).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 2
    });
}

#[test]
fn test_bx() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register LR = 0x1234;
        register R1 = 0x80000000;
        register R2 = 1;
        flag C = true
    });

    let instruction: Operation = Bx::builder().set_rm(Register::LR).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 0x1234
    });
}

#[test]
fn test_bfc() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 1;
        flag C = true
    });

    let instruction: Operation = Bfc::builder().set_rd(Register::R1).set_lsb(0).set_msb(2).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80010000
    });
}

#[test]
fn test_bfi() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 12;
        flag C = true
    });

    let instruction: Operation = Bfi::builder().set_rd(Register::R1).set_lsb(0).set_msb(4).set_rn(Register::R2).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x8001000c
    });
}

#[test]
#[should_panic]
fn test_bfi_panic() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 12;
        flag C = true
    });

    let instruction: Operation = Bfi::builder().set_rd(Register::R1).set_lsb(4).set_msb(0).set_rn(Register::R2).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x8001000c
    });
}

#[test]
fn test_bic_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 12;
        flag C = false
    });

    let instruction: Operation = BicImmediate::builder()
        .set_rd(None)
        .set_rn(Register::R1)
        .set_imm(0b00110)
        .set_s(Some(false))
        .set_carry(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80010001,
        flag C == 0
    });
}

#[test]
fn test_bic_imm_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 12;
        flag C = true
    });

    let instruction: Operation = BicImmediate::builder()
        .set_rd(None)
        .set_rn(Register::R1)
        .set_imm(0b00110)
        .set_s(Some(true))
        .set_carry(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80010001,
        flag C == 1
    });
    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 12;
        flag C = true;
        flag Z = false
    });

    let instruction: Operation = BicImmediate::builder()
        .set_rd(None)
        .set_rn(Register::R1)
        .set_imm(0xffffffff)
        .set_s(Some(true))
        .set_carry(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1
    });
}

#[test]
fn test_bic_reg() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 0b0110;
        flag C = false
    });

    let instruction: Operation = BicRegister::builder()
        .set_rd(None)
        .set_rn(Register::R1)
        .set_s(Some(SetFlags::Literal(false)))
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80010001,
        flag C == 0
    });
}

#[test]
fn test_bic_reg_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010003;
        register R2 = 0b11;
        flag C = true
    });

    let instruction: Operation = BicRegister::builder()
        .set_rd(None)
        .set_rn(Register::R1)
        .set_s(Some(SetFlags::Literal(true)))
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80010001,
        flag C == 0
    });
    initiate!(executor {
        register PC = 0;
        register R1 = 0x80010000;
        register R2 = 0xFFFFFFFF;
        flag C = false;
        flag Z = false
    });

    let instruction: Operation = BicRegister::builder()
        .set_rd(None)
        .set_rn(Register::R1)
        .set_s(Some(SetFlags::Literal(true)))
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1
    });
}

#[test]
fn test_bl() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    let v6 = vec![
        GAOperation::Move {
            destination: Operand::Local("PC".to_owned()),
            source: Operand::Register("PC".to_owned()),
        },
        GAOperation::Move {
            destination: Operand::Register("LR".to_owned()),
            source: Operand::Local("PC".to_owned()),
        },
        GAOperation::Add {
            destination: Operand::Local("newPC".to_owned()),
            operand1: Operand::Local("PC".to_owned()),
            operand2: Operand::Immediate(DataWord::Word32(0x4)),
        },
        GAOperation::Move {
            destination: Operand::Register("PC".to_owned()),
            source: Operand::Local("newPC".to_owned()),
        },
    ];
    initiate!(executor {
        register PC = 0x100;
        register LR = 0xFFFFFFFF;
        flag C = false;
        flag V = false;
        flag N = false;
        flag Z = false
    });

    let instruction: Operation = Bl::builder().set_imm(0x4).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 0x108,
        register LR == 0x105,
        flag C == 0,
        flag V == 0,
        flag N == 0,
        flag Z == 0
    });

    initiate!(executor {
        register PC = 0x100;
        register LR = 0xFFFFFFFF;
        flag C = false;
        flag V = false;
        flag N = false;
        flag Z = false
    });

    let instruction = Instruction {
        operations: v6,
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    // TODO! Discuss this, the spec is the same for the v6 and the v7 but the v6
    // only supports 16 bit instructions so this might be a fulhack?
    test!(executor {
        register PC == 0x106,
        register LR == 0x102, // It should be one less since V6 does not account for the error bit.
        flag C == 0,
        flag V == 0,
        flag N == 0,
        flag Z == 0
    });
}

#[test]
fn test_cmp_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        flag C = false;
        flag V = false;
        flag N = false;
        flag Z = false
    });

    let instruction: Operation = CmpImmediate::builder().set_rn(Register::R1).set_imm(0x4).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        flag C == 0,
        flag V == 0,
        flag N == 1,
        flag Z == 0
    });

    initiate!(executor {
        register R1 = 0x4;
        flag C = false;
        flag V = false;
        flag N = false;
        flag Z = false
    });

    let instruction: Operation = CmpImmediate::builder().set_rn(Register::R1).set_imm(0x4).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        flag C == 1,
        flag V == 0,
        flag N == 0,
        flag Z == 1
    });
}

#[test]
fn test_ldr_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x100;
        register SP = 0x104

    });

    let instruction: Operation = LdrImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x0)
        .set_w(Some(false))
        .set_add(true)
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x100,
        register SP == 0x104,
        address (0x104,32) == 0x100
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x100;
        register SP = 0x100
    });

    let instruction: Operation = LdrImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(false))
        .set_add(true)
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x100,
        register SP == 0x100,
        address (0x104,32) == 0x100
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x100;
        register SP = 0x108
    });

    let instruction: Operation = LdrImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(false))
        .set_add(false)
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x100,
        register SP == 0x108,
        address (0x104,32) == 0x100
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x100;
        register SP = 0x104
    });

    let instruction: Operation = LdrImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(false))
        .set_add(true)
        .set_index(false)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x100,
        register SP == 0x104,
        address (0x104,32) == 0x100
    });
    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x100;
        register SP = 0x100
    });

    let instruction: Operation = LdrImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(true))
        .set_add(true)
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x100,
        register SP == 0x104,
        address (0x104,32) == 0x100
    });
}

#[test]
fn test_ldr_literal() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x100;
        register PC = 0
    });

    let instruction: Operation = LdrLiteral::builder().set_add(true).set_rt(Register::R1).set_imm(0x100).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x100,
        address (0x104,32) == 0x100
    });
}

#[test]
fn test_ldr_register() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x4;
        address (0x104,32) = 0x100;
        register SP = 0x100

    });

    let instruction: Operation = LdrRegister::builder()
        .set_rn(Register::R1)
        .set_rt(Register::SP)
        .set_w(Some(false))
        .set_rm(Register::SP)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 0x100,
        address (0x104,32) == 0x100,
        register R1 == 0x4
    });

    initiate!(executor {
        register R1 = 0x4;
        address (0x104,32) = 0x100;
        register SP = 0x100

    });

    let instruction: Operation = LdrRegister::builder()
        .set_rn(Register::R1)
        .set_rt(Register::SP)
        .set_w(Some(true))
        .set_rm(Register::SP)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 0x100,
        address (0x104,32) == 0x100,
        register R1 == 0x104
    });

    initiate!(executor {
        register R1 = 0x4;
        address (0x20c,32) = 0x100;
        register SP = 0x104

    });

    let instruction: Operation = LdrRegister::builder()
        .set_rn(Register::R1)
        .set_rt(Register::SP)
        .set_w(Some(true))
        .set_rm(Register::SP)
        .set_shift(Some(ImmShift { shift_t: Shift::Lsl, shift_n: 1 }))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register SP == 0x100,
        address (0x20c,32) == 0x100,
        register R1 == 0x20c
    });
}
#[test]
fn test_ldrh_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x8001000;
        register SP = 0x104

    });

    let instruction: Operation = LdrhImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x0)
        .set_w(Some(false))
        .set_add(Some(true))
        .set_index(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x1000,
        register SP == 0x104
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001000;
        register SP = 0x100
    });

    let instruction: Operation = LdrhImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(false))
        .set_add(Some(true))
        .set_index(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x1000,
        register SP == 0x100
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001000;
        register SP = 0x108
    });

    let instruction: Operation = LdrhImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(false))
        .set_add(Some(false))
        .set_index(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x1000,
        register SP == 0x108
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001000;
        register SP = 0x104
    });

    let instruction: Operation = LdrhImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(false))
        .set_add(Some(true))
        .set_index(Some(false))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x1000,
        register SP == 0x104
    });
    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001000;
        register SP = 0x100
    });

    let instruction: Operation = LdrhImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(0x4)
        .set_w(Some(true))
        .set_add(Some(true))
        .set_index(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x1000,
        register SP == 0x104
    });
}

#[test]
fn test_ldrb_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x8001000;
        register SP = 0x104

    });

    let instruction: Operation = LdrbImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(Some(0x0))
        .set_w(Some(false))
        .set_add(Some(true))
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0000,
        register SP == 0x104
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x8001001;
        register SP = 0x104

    });

    let instruction: Operation = LdrbImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(Some(0x0))
        .set_w(Some(false))
        .set_add(Some(true))
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0001,
        register SP == 0x104
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001001;
        register SP = 0x100
    });

    let instruction: Operation = LdrbImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(Some(0x4))
        .set_w(Some(false))
        .set_add(Some(true))
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x001,
        register SP == 0x100
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001002;
        register SP = 0x108
    });

    let instruction: Operation = LdrbImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(Some(0x4))
        .set_w(Some(false))
        .set_add(Some(false))
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0002,
        register SP == 0x108
    });

    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001004;
        register SP = 0x104
    });

    let instruction: Operation = LdrbImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(Some(0x4))
        .set_w(Some(false))
        .set_add(Some(true))
        .set_index(false)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x004,
        register SP == 0x104
    });
    initiate!(executor {
        register R1 = 0x3;
        address (0x104,32) = 0x80001006;
        register SP = 0x100
    });

    let instruction: Operation = LdrbImmediate::builder()
        .set_rn(Register::SP)
        .set_rt(Register::R1)
        .set_imm(Some(0x4))
        .set_w(Some(true))
        .set_add(Some(true))
        .set_index(true)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0006,
        register SP == 0x104
    });
}

#[test]
fn test_lsl_immediate() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = LslImmediate::builder()
        .set_rd(Register::R1)
        .set_imm(0x0)
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rm(Register::R1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x3,
        flag C == 0,
        flag Z == 0,
        flag N == 0
    });

    initiate!(executor {
        register R1 = 0x8000_0000;
        register R2 = 0x1;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = LslImmediate::builder()
        .set_rd(Register::R1)
        .set_imm(0x1)
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rm(Register::R1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag N == 0
    });
}

#[test]
fn test_lsr_immediate() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 24;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = LsrImmediate::builder()
        .set_rd(Register::R1)
        .set_imm(0x3)
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rm(Register::R1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 3,
        flag C == 0,
        flag Z == 0,
        flag N == 0
    });

    initiate!(executor {
        register R1 = 0x0000_0001;
        register R2 = 0x1;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = LsrImmediate::builder()
        .set_rd(Register::R1)
        .set_imm(0x1)
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rm(Register::R1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag C == 1,
        flag Z == 1,
        flag N == 0
    });
}

#[test]
fn test_mov_imm_no_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = MovImmediate::builder()
        .set_rd(Register::R1)
        .set_imm(0x0)
        .set_s(None)
        .set_carry(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0,
        flag C == 0,
        flag Z == 0,
        flag N == 0
    });
}

#[test]
fn test_mov_imm_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = MovImmediate::builder()
        .set_rd(Register::R1)
        .set_imm(0x0)
        .set_s(Some(SetFlags::Literal(true)))
        .set_carry(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0,
        flag C == 1,
        flag Z == 1,
        flag N == 0
    });

    initiate!(executor {
        register R1 = 0x3;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = MovImmediate::builder()
        .set_rd(Register::R1)
        .set_imm(0x80010001)
        .set_s(Some(SetFlags::Literal(true)))
        .set_carry(Some(true))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80010001,
        flag C == 1,
        flag Z == 0,
        flag N == 1
    });
}

#[test]
fn test_mov_reg_no_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        register R2 =  0x0;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = MovRegister::builder().set_rd(Register::R1).set_rm(Register::R2).set_s(None).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0,
        flag C == 0,
        flag Z == 0,
        flag N == 0
    });
}

#[test]
fn test_mov_reg_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        register R2 =  0x0;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = MovRegister::builder().set_rd(Register::R1).set_rm(Register::R2).set_s(Some(true)).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0,
        flag C == 0,
        flag Z == 1,
        flag N == 0
    });

    initiate!(executor {
        register R1 = 0x3;
        register R2 = 0x80010001;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = MovRegister::builder().set_rd(Register::R1).set_rm(Register::R2).set_s(Some(true)).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x80010001,
        flag Z == 0,
        flag N == 1
    });
}

#[test]
fn test_mul() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        register R2 =  0x2;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = Mul::builder()
        .set_rd(Some(Register::R1))
        .set_rm(Register::R2)
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rn(Register::R1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x6,
        flag C == 0,
        flag Z == 0,
        flag N == 0
    });

    initiate!(executor {
        register R1 = 0x3;
        register R2 =  0x0;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = Mul::builder()
        .set_rd(Some(Register::R1))
        .set_rm(Register::R2)
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rn(Register::R1)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x0,
        flag C == 0,
        flag Z == 1,
        flag N == 0
    });
}

#[test]
fn test_pop() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        register R2 =  0x0;
        flag C = 0;
        flag Z = 0;
        flag N = 0;
        register SP = 0x100;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003


    });

    let instruction: Operation = Pop::builder()
        .set_registers(RegisterList {
            registers: vec![Register::R4, Register::R5, Register::R7, Register::PC],
        })
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R4 == 0x1001,
        register R5 == 0x1002,
        register R7 == 0x1003,
        register PC == 0x1002,
        register SP == 0x110
    });
}

#[test]
fn test_push() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        register R2 =  0x0;
        flag C = 0;
        flag Z = 0;
        flag N = 0;
        register SP = 0x110;
        register R4 = 0x1001;
        register R5 = 0x1002;
        register R7 = 0x1003;
        register LR = 0x1003
    });

    let instruction: Operation = Push::builder()
        .set_registers(RegisterList {
            registers: vec![Register::R4, Register::R5, Register::R7, Register::LR],
        })
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x100,32) == 0x1001,
        address (0x104,32) == 0x1002,
        address (0x108,32) == 0x1003,
        address (0x10C,32) == 0x1003,
        register SP == 0x100
    });
}

#[test]
fn test_rsb() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x3;
        register R0 = 24;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = RsbImmediate::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R0)
        .set_imm(1024)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 1000,
        register R0 == 24
    });

    initiate!(executor {
        register R1 = 0x3;
        register R0 = 24;
        flag C = 0;
        flag Z = 0;
        flag N = 0
    });

    let instruction: Operation = RsbImmediate::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rd(Some(Register::R1))
        .set_rn(Register::R0)
        .set_imm(0)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        flag N == 1
    });
}

#[test]
fn test_strb_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x101;
        address (0x100,32) = 0x1234_0003
    });

    let instruction: Operation = StrbImmediate::builder()
        .set_index(Some(true))
        .set_add(true)
        .set_w(Some(true))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x103,8) == 0x034,
        register R2 == 0x103,
        register R1 == 0x8000_1234
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x101;
        address (0x100,32) = 0x1234_0003
    });

    let instruction: Operation = StrbImmediate::builder()
        .set_index(Some(true))
        .set_add(true)
        .set_w(Some(false))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x103,8) == 0x034,
        register R2 == 0x101,
        register R1 == 0x8000_1234
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x105;
        address (0x100,32) = 0x1234_0003
    });

    let instruction: Operation = StrbImmediate::builder()
        .set_index(Some(true))
        .set_add(false)
        .set_w(Some(false))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x103,8) == 0x034,
        register R2 == 0x105,
        register R1 == 0x8000_1234
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x103;
        address (0x100,32) = 0x1234_0003
    });

    let instruction: Operation = StrbImmediate::builder()
        .set_index(Some(false))
        .set_add(false)
        .set_w(Some(false))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(2)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x103,8) == 0x034,
        register R2 == 0x103,
        register R1 == 0x8000_1234
    });
}

#[test]
fn test_strh_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x100;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrhImmediate::builder()
        .set_index(true)
        .set_add(true)
        .set_w(true)
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(Some(4))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x104,32) == 0x1234,
        address (0x104,16) == 0x1234,
        register R2 == 0x104
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x100;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrhImmediate::builder()
        .set_index(true)
        .set_add(true)
        .set_w(false)
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(Some(4))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x104,32) == 0x1234,
        address (0x104,16) == 0x1234,
        register R2 == 0x100
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x104;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrhImmediate::builder()
        .set_index(true)
        .set_add(false)
        .set_w(false)
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(Some(4))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x100,32) == 0x1234,
        address (0x100,16) == 0x1234,
        register R2 == 0x104
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x104;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrhImmediate::builder()
        .set_index(false)
        .set_add(false) // Should not matter here
        .set_w(false)
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(Some(4))
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x104,32) == 0x1234,
        address (0x104,16) == 0x1234,
        register R2 == 0x104
    });
}

#[test]
fn test_str_imm() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x100;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrImmediate::builder()
        .set_index(Some(true))
        .set_add(true)
        .set_w(Some(true))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(4)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x104,32) == 0x80001234,
        register R2 == 0x104
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x100;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrImmediate::builder()
        .set_index(Some(true))
        .set_add(true)
        .set_w(Some(false))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(4)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x104,32) == 0x80001234,
        register R2 == 0x100
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x104;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrImmediate::builder()
        .set_index(Some(true))
        .set_add(false)
        .set_w(Some(false))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(4)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x100,32) == 0x80001234,
        register R2 == 0x104
    });

    initiate!(executor {
        register R1 = 0x80001234;
        register R2 = 0x104;
        address (0x100,32) = 0x1001;
        address (0x104,32) = 0x1002;
        address (0x108,32) = 0x1003;
        address (0x10C,32) = 0x1003
    });

    let instruction: Operation = StrImmediate::builder()
        .set_index(Some(false))
        .set_add(false) // Should not matter here
        .set_w(Some(false))
        .set_rt(Register::R1)
        .set_rn(Register::R2)
        .set_imm(4)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        address (0x104,32) == 0x80001234,
        register R2 == 0x104
    });
}

#[test]
fn test_sub_imm_no_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubImmediate::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rn(Register::SP)
        .set_rd(Some(Register::R1))
        .set_imm(0x100)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x4,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubSpMinusImmediate::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::R1))
        .set_imm(0x104)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 1;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubImmediate::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rn(Register::SP)
        .set_rd(Some(Register::R1))
        .set_imm(0x104)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 1,
        flag V == 0,
        flag C == 0
    });
}

#[test]
fn test_sub_imm_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubImmediate::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rn(Register::SP)
        .set_rd(Some(Register::R1))
        .set_imm(0x100)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x4,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 1
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubImmediate::builder()
        .set_s(Some(SetFlags::InITBlock(false)))
        .set_rn(Register::SP)
        .set_rd(Some(Register::R1))
        .set_imm(0x104)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 1,
        flag V == 0,
        flag C == 1
    });
}

#[test]
fn test_sub_reg_no_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        register R2 = 0x100;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubRegister::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rn(Register::SP)
        .set_rd(Some(Register::R1))
        .set_rm(Register::R2)
        .set_shift(None)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x4,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        register R2 = 0x104;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubRegister::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rd(Some(Register::R1))
        .set_rm(Register::R2)
        .set_shift(None)
        .set_rn(Register::SP)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        register R2 = (0x104 >> 1);
        flag N = 0;
        flag Z = 1;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubRegister::builder()
        .set_s(Some(SetFlags::Literal(false)))
        .set_rd(Some(Register::R1))
        .set_rm(Register::R2)
        .set_shift(Some(ImmShift { shift_n: 1, shift_t: Shift::Lsl }))
        .set_rn(Register::SP)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 1,
        flag V == 0,
        flag C == 0
    });
}

#[test]
fn test_sub_reg_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        register R2 = 0x100;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Some(Register::R1))
        .set_rm(Register::R2)
        .set_shift(None)
        .set_rn(Register::SP)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x4,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 1
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        register R2 = 0x104;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubRegister::builder()
        .set_s(Some(SetFlags::Literal(true)))
        .set_rd(Some(Register::R1))
        .set_rm(Register::R2)
        .set_shift(None)
        .set_rn(Register::SP)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 1,
        flag V == 0,
        flag C == 1
    });
}

#[test]
fn test_sub_sp_imm_no_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubSpMinusImmediate::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::R1))
        .set_imm(0x100)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x4,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubSpMinusImmediate::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::R1))
        .set_imm(0x104)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 1;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubSpMinusImmediate::builder()
        .set_s(Some(false))
        .set_rd(Some(Register::R1))
        .set_imm(0x104)
        .complete()
        .into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 1,
        flag V == 0,
        flag C == 0
    });
}

#[test]
fn test_sub_sp_imm_set_flags() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubSpMinusImmediate::builder().set_s(Some(true)).set_rd(Some(Register::R1)).set_imm(0x100).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x4,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 1
    });

    initiate!(executor {
        register SP = 0x104;
        register R1 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = SubSpMinusImmediate::builder().set_s(Some(true)).set_rd(Some(Register::R1)).set_imm(0x104).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0,
        flag N == 0,
        flag Z == 1,
        flag V == 0,
        flag C == 1
    });
}

#[test]
fn test_sub_uxth() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x123;
        register R2 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = Uxth::builder().set_rd(Register::R1).set_rm(Register::R2).set_rotation(Some(1)).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x91,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });

    initiate!(executor {
        register R1 = 0x123;
        register R2 = 0x123;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = Uxth::builder().set_rd(Register::R1).set_rm(Register::R2).set_rotation(None).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R1 == 0x123,
        flag N == 0,
        flag Z == 0,
        flag V == 0,
        flag C == 0
    });
}

#[test]
fn test_tb() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0x123;
        register R2 = 0x1;
        address(0x123,8) = 0x23;
        address(0x124,8) = 0x22;
        address(0x125,8) = 0x21;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = Tb::builder().set_is_tbh(Some(false)).set_rn(Register::R1).set_rm(Register::R2).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 0x48
    });

    initiate!(executor {
        register PC = 0;
        register R1 = 0x122;
        register R2 = 0x1;
        address(0x122,16) = 0x23;
        address(0x124,16) = 0x22;
        address(0x126,16) = 0x21
    });

    let instruction: Operation = Tb::builder().set_is_tbh(Some(true)).set_rn(Register::R1).set_rm(Register::R2).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register PC == 0x48
    });
}

#[test]
fn test_bfi_2() {
    let mut vm = setup_test_vm();
    let project = vm.project;

    let mut executor = GAExecutor::from_state(vm.paths.get_path().unwrap().state, &mut vm, project);

    initiate!(executor {
        register R1 = 0b110011;
        register R2 = 0x1;
        address(0x123,8) = 0x23;
        address(0x124,8) = 0x22;
        address(0x125,8) = 0x21;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = Bfi::builder().set_rn(Register::R1).set_rd(Register::R2).set_lsb(3).set_msb(5).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R2 == 0b011001
    });
    initiate!(executor {
        register R1 = 0b110011;
        register R2 = 0x1;
        address(0x123,8) = 0x23;
        address(0x124,8) = 0x22;
        address(0x125,8) = 0x21;
        flag N = 0;
        flag Z = 0;
        flag V = 0;
        flag C = 0
    });

    let instruction: Operation = Bfi::builder().set_rn(Register::R1).set_rd(Register::R2).set_lsb(5).set_msb(5).complete().into();

    let instruction = Instruction {
        operations: (16, instruction).convert(false),
        memory_access: false,
        instruction_size: 16,
        max_cycle: CycleCount::Value(0),
    };
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger).expect("Malformed instruction");

    test!(executor {
        register R2 == 0b100001
    });
}
