#![cfg(test)]

use general_assembly::operand::{DataWord, Operand};
use hashbrown::HashMap;

use crate::{
    arch::{Architecture, NoArchitectureOverride, RISCV},
    defaults::boolector::DefaultCompositionNoLogger,
    executor::{hooks::HookContainer, instruction::Instruction, state::GAState, vm::VM, GAExecutor},
    logging::NoLogger,
    path_selection::PathSelector,
    project::{dwarf_helper::SubProgramMap, Project},
    smt::{
        smt_boolector::{Boolector, BoolectorExpr},
        SmtSolver,
    },
    Endianness, WordSize,
};

struct TestRegister {
    name: &'static str,
    initial_value: u32,
    expected_value: u32,
}
struct TestData {
    instruction_bytes: [u8; 4],
    register1: TestRegister,
    register2: Option<TestRegister>,
    register3: Option<TestRegister>,
}

macro_rules! generate_test_data {
    // Three registers
    (
        $inst:expr,
            ($reg1_name:expr, $reg1_initial:expr, $reg1_expected:expr),
            ($reg2_name:expr, $reg2_initial:expr, $reg2_expected:expr),
            ($reg3_name:expr, $reg3_initial:expr, $reg3_expected:expr)
    ) => {{
        TestData {
            instruction_bytes: $inst,
            register1: TestRegister {
                name: $reg1_name,
                initial_value: $reg1_initial,
                expected_value: $reg1_expected,
            },
            register2: Some(TestRegister {
                name: $reg2_name,
                initial_value: $reg2_initial,
                expected_value: $reg2_expected,
            }),
            register3: Some(TestRegister {
                name: $reg3_name,
                initial_value: $reg3_initial,
                expected_value: $reg3_expected,
            }),
        }
    }};

    // Two registers
    (
        $inst:expr,
        ($reg1_name:expr, $reg1_initial:expr, $reg1_expected:expr),
        ($reg2_name:expr, $reg2_initial:expr, $reg2_expected:expr)
    ) => {{
        TestData {
            instruction_bytes: $inst,
            register1: TestRegister {
                name: $reg1_name,
                initial_value: $reg1_initial,
                expected_value: $reg1_expected,
            },
            register2: Some(TestRegister {
                name: $reg2_name,
                initial_value: $reg2_initial,
                expected_value: $reg2_expected,
            }),
            register3: None,
        }
    }};

    // One register
    (
        $inst:expr,
        ($reg1_name:expr, $reg1_initial:expr, $reg1_expected:expr)
    ) => {{
        TestData {
            instruction_bytes: $inst,
            register1: TestRegister {
                name: $reg1_name,
                initial_value: $reg1_initial,
                expected_value: $reg1_expected,
            },
            register2: None,
            register3: None,
        }
    }};
}

fn setup_test_vm() -> VM<DefaultCompositionNoLogger> {
    let ctx = Boolector::new();
    let project_global = Box::new(Project::manual_project(vec![], 0, 0, WordSize::Bit32, Endianness::Little, HashMap::new()));
    let project: &'static Project = Box::leak(project_global);
    let mut hooks = HookContainer::new();
    RISCV {}.add_hooks(&mut hooks, &mut SubProgramMap::empty());
    let state = GAState::<DefaultCompositionNoLogger>::create_test_state(
        project,
        ctx.clone(),
        ctx.clone(),
        0,
        0,
        hooks,
        (),
        crate::arch::SupportedArchitecture::RISCV(<RISCV as Architecture<NoArchitectureOverride>>::new()),
    );
    VM::new_test_vm(project, state, NoLogger).unwrap()
}

fn translate_instruction(instruction_bytes: [u8; 4]) -> Instruction<DefaultCompositionNoLogger> {
    let mut vm = setup_test_vm();
    let mut state = vm.paths.get_path().unwrap().state;

    RISCV {}.translate(&instruction_bytes, &state.clone()).expect("Failed to translate instruction")
}

fn init_executor(vm: &mut VM<DefaultCompositionNoLogger>) -> GAExecutor<'_, DefaultCompositionNoLogger> {
    let project = vm.project;

    let mut state = vm.paths.get_path().unwrap().state;

    GAExecutor::from_state(state, vm, project)
}

fn init_registers<'a>(executor: &'a mut GAExecutor<'_, DefaultCompositionNoLogger>, instruction: Instruction<DefaultCompositionNoLogger>, test_data: &'a TestData) {
    init_test_register(executor, test_data.register1.name, test_data.register1.initial_value);
    if let Some(register2) = &test_data.register2 {
        init_test_register(executor, register2.name, register2.initial_value);
    }
    if let Some(register3) = &test_data.register3 {
        init_test_register(executor, register3.name, register3.initial_value);
    }
}

fn init_test_register(executor: &mut GAExecutor<'_, DefaultCompositionNoLogger>, reg: &str, value: u32) {
    let register_operand = Operand::Register(reg.to_string());
    let immediate_operand = Operand::Immediate(DataWord::Word32(value));
    let operation = general_assembly::operation::Operation::Move {
        destination: register_operand,
        source: immediate_operand,
    };
    executor.execute_operation(&operation, &mut crate::logging::NoLogger).expect("Malformed test");
}

fn assert_registers(test_data: &TestData, executor: &mut GAExecutor<'_, DefaultCompositionNoLogger>) {
    let mut final_state = &mut executor.state;

    let reg1_value = final_state.get_register(test_data.register1.name).expect("Register not found");
    assert_eq!(
        reg1_value.get_constant().unwrap(),
        test_data.register1.expected_value as u64,
        "Register {} did not match expected value",
        test_data.register1.name
    );

    if let Some(register2) = &test_data.register2 {
        let reg2_value = final_state.get_register(register2.name).expect("Register not found");
        assert_eq!(
            reg2_value.get_constant().unwrap(),
            register2.expected_value as u64,
            "Register {} did not match expected value",
            register2.name
        );
    }

    if let Some(register3) = &test_data.register3 {
        let reg3_value = final_state.get_register(register3.name).expect("Register not found");
        assert_eq!(
            reg3_value.get_constant().unwrap(),
            register3.expected_value as u64,
            "Register {} did not match expected value",
            register3.name
        );
    }
}

fn init_memory(executor: &mut GAExecutor<'_, DefaultCompositionNoLogger>, mem_addr: u32, value: u32) {
    let load_addr_in_addr = general_assembly::operation::Operation::Add {
        destination: Operand::Local("ADDR".to_owned()),
        operand1: Operand::Register("ZERO".to_owned()),
        operand2: Operand::Immediate(DataWord::Word32(mem_addr)),
    };
    let load_imm_in_temp = general_assembly::operation::Operation::Add {
        destination: Operand::Register("TEMP".to_owned()),
        operand1: Operand::Register("ZERO".to_owned()),
        operand2: Operand::Immediate(DataWord::Word32(value)),
    };
    let save_into_mem = general_assembly::operation::Operation::Move {
        destination: Operand::AddressInLocal("ADDR".to_owned(), 32),
        source: Operand::Register("TEMP".to_owned()),
    };

    executor
        .execute_operation(&load_addr_in_addr, &mut crate::logging::NoLogger)
        .expect("Failed to load address into ADDR");
    executor
        .execute_operation(&load_imm_in_temp, &mut crate::logging::NoLogger)
        .expect("Failed to load immediate into TEMP");
    executor
        .execute_operation(&save_into_mem, &mut crate::logging::NoLogger)
        .expect("Failed to save TEMP into memory");
}

fn assert_memory(mem_addr: u32, expected_value: u32, executor: &mut GAExecutor<'_, DefaultCompositionNoLogger>) {
    let load_addr_in_addr = general_assembly::operation::Operation::Add {
        destination: Operand::Local("ADDR".to_owned()),
        operand1: Operand::Register("ZERO".to_owned()),
        operand2: Operand::Immediate(DataWord::Word32(mem_addr)),
    };
    let read_from_mem_into_temp = general_assembly::operation::Operation::Move {
        destination: Operand::Register("TEMP".to_owned()),
        source: Operand::AddressInLocal("ADDR".to_owned(), 32),
    };

    executor
        .execute_operation(&load_addr_in_addr, &mut crate::logging::NoLogger)
        .expect("Failed to load address into ADDR");
    executor
        .execute_operation(&read_from_mem_into_temp, &mut crate::logging::NoLogger)
        .expect("Failed to read from memory into TEMP");

    let temp = executor.state.get_register("TEMP".to_owned()).expect("Register not found");

    assert_eq!(
        temp.get_constant().unwrap(),
        expected_value as u64,
        "Memory at address {} did not match expected value",
        mem_addr
    );
}

fn run_test_no_mem(test_data: &TestData) {
    let instruction = translate_instruction(test_data.instruction_bytes);
    let mut vm = setup_test_vm();
    let mut executor = init_executor(&mut vm);
    init_registers(&mut executor, instruction.clone(), test_data);
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger);

    assert_registers(test_data, &mut executor);
}

fn run_test_with_mem(test_data: &TestData, mem_addr: u32, init_value: u32, expected_value: u32) {
    let instruction = translate_instruction(test_data.instruction_bytes);
    let mut vm = setup_test_vm();
    let mut executor = init_executor(&mut vm);
    init_registers(&mut executor, instruction.clone(), test_data);
    init_memory(&mut executor, mem_addr, init_value);
    executor.execute_instruction(&instruction, &mut crate::logging::NoLogger);

    assert_memory(mem_addr, expected_value, &mut executor);
    assert_registers(test_data, &mut executor);
}

#[test]
fn test_add() {
    let test_data = generate_test_data!(0x00B50533u32.to_le_bytes(), ("A0", 0x01, 0x02), ("A1", 0x01, 0x01));
    run_test_no_mem(&test_data);
}

#[test]
fn test_add_wrap() {
    // RISCV ignores overflow and result is wrapped, from ISA:
    //"Arithmetic overflow is ignored and the result is simply the low XLEN bits of the result."
    let test_data = generate_test_data!(0x00B50533u32.to_le_bytes(), ("A0", 0xFFFFFFFFu32, 0x0u32), ("A1", 0x1u32, 0x1u32));
    run_test_no_mem(&test_data);

    let test_data = generate_test_data!(0x00B50533u32.to_le_bytes(), ("A0", 0x7FFFFFFFu32, 0x80000000u32), ("A1", 0x1u32, 0x1u32));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sub() {
    let test_data = generate_test_data!(0x40B50533u32.to_le_bytes(), ("A0", 25, 0x06), ("A1", 19, 19));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sub_wrap() {
    // RISCV ignores overflow and result is wrapped, from ISA:
    //"Arithmetic overflow is ignored and the result is simply the low XLEN bits of the result."
    let test_data = generate_test_data!(0x40B50533u32.to_le_bytes(), ("A0", 0x80000000u32, 0x7FFFFFFFu32), ("A1", 0x01u32, 0x01u32));
    run_test_no_mem(&test_data);

    let test_data = generate_test_data!(0x40B50533u32.to_le_bytes(), ("A0", 0x7FFFFFFFu32, 0x80000000u32), ("A1", 0xFFFFFFFFu32, 0xFFFFFFFFu32));
    run_test_no_mem(&test_data);
}

#[test]
fn test_slt() {
    let test_data = generate_test_data!(0x00B52533u32.to_le_bytes(), ("A0", (-25i32) as u32, 1), ("A1", 5, 5));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sltu() {
    let test_data = generate_test_data!(0x00B53533u32.to_le_bytes(), ("A0", 3, 1), ("A1", 5, 5));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sltu_signed() {
    let test_data = generate_test_data!(0x00B53533u32.to_le_bytes(), ("A0", (-25i32) as u32, 0), ("A1", 5, 5));
    run_test_no_mem(&test_data);
}

#[test]
fn test_xor() {
    let test_data = generate_test_data!(0x00B54533u32.to_le_bytes(), ("A0", 13, 21), ("A1", 24, 24));
    run_test_no_mem(&test_data);
}

#[test]
fn test_or() {
    let test_data = generate_test_data!(0x00B56533u32.to_le_bytes(), ("A0", 0b0110111, 0b0111111), ("A1", 0b0001111, 0b0001111));
    run_test_no_mem(&test_data);
}

#[test]
fn test_and() {
    let test_data = generate_test_data!(0x00B57533u32.to_le_bytes(), ("A0", 0b0110111, 0b0000111), ("A1", 0b0001111, 0b0001111));
    run_test_no_mem(&test_data);
}

#[test]
fn test_srl() {
    let test_data = generate_test_data!(0x00B55533u32.to_le_bytes(), ("A0", 0b01111001, 0b00011110), ("A1", 0x02, 0x02));
    run_test_no_mem(&test_data);
}

#[test]
fn test_srl_shift_exceed_max_bits() {
    // This checks that the shift amount does not exceed 5 bits
    // 0xFFFFFFFF should be masked to 0x1F
    let test_data = generate_test_data!(0x00B55533u32.to_le_bytes(), ("A0", 0x80000000u32, 0x1u32), ("A1", 0xFFFFFFFFu32, 0xFFFFFFFFu32));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sra_leading_0() {
    let test_data = generate_test_data!(0x40B55533u32.to_le_bytes(), ("A0", 0b01111001, 0b00011110), ("A1", 0x02, 0x02));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sra_leading_1() {
    let test_data = generate_test_data!(0x40B55533u32.to_le_bytes(), ("A0", 0xf0000000, 0xffffffff), ("A1", 31, 31));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sll() {
    let test_data = generate_test_data!(0x00B51533u32.to_le_bytes(), ("A0", 0b01111001, 0x1e400000), ("A1", 22, 22));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sll_shift_exceeds_max_bits() {
    // This checks that the shift amount does not exceed 5 bits
    // 0xFFFFFFFF should be masked to 0x1F
    let test_data = generate_test_data!(0x00B51533u32.to_le_bytes(), ("A0", 0x1u32, 0x80000000u32), ("A1", 0xFFFFFFFFu32, 0xFFFFFFFFu32));
    run_test_no_mem(&test_data);
}

#[test]
fn test_addi() {
    let test_data = generate_test_data!(0x00A50513u32.to_le_bytes(), ("A0", 0x01, 0x01 + 10));
    run_test_no_mem(&test_data);
}

#[test]
fn test_slti() {
    let test_data = generate_test_data!(0x00A52513u32.to_le_bytes(), ("A0", (-25i32) as u32, 1));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sltiu() {
    let test_data = generate_test_data!(0x00A53513u32.to_le_bytes(), ("A0", 3, 1));
    run_test_no_mem(&test_data);
}

#[test]
fn test_sltiu_signed() {
    let test_data = generate_test_data!(0x00A53513u32.to_le_bytes(), ("A0", (-25i32) as u32, 0));
    run_test_no_mem(&test_data);
}

#[test]
fn test_xori() {
    let test_data = generate_test_data!(0x00A54513u32.to_le_bytes(), ("A0", 0xf12, 0xf18));
    run_test_no_mem(&test_data);
}

#[test]
fn test_ori() {
    let test_data = generate_test_data!(0x00f56513u32.to_le_bytes(), ("A0", 0b0110111, 0b0111111));
    run_test_no_mem(&test_data);
}

#[test]
fn test_andi() {
    let test_data = generate_test_data!(0x00f57513u32.to_le_bytes(), ("A0", 0b0110111, 0b0000111));
    run_test_no_mem(&test_data);
}

#[test]
fn test_slli() {
    let test_data = generate_test_data!(0x00451513u32.to_le_bytes(), ("A0", 0b01111001, 0b011110010000));
    run_test_no_mem(&test_data);
}

#[test]
fn test_srli() {
    let test_data = generate_test_data!(0x00455513u32.to_le_bytes(), ("A0", 0b01111001, 0b0111));
    run_test_no_mem(&test_data);
}

#[test]
fn teat_srai_leading_0() {
    let test_data = generate_test_data!(0x40455513u32.to_le_bytes(), ("A0", 0b01111001, 0b0111));
    run_test_no_mem(&test_data);
}

#[test]
fn test_srai_leading_1() {
    let test_data = generate_test_data!(0x40455513u32.to_le_bytes(), ("A0", 0xf0000000, 0xff000000));
    run_test_no_mem(&test_data);
}

#[test]
fn test_lb() {
    let test_data = generate_test_data!(
        0x00e58503u32.to_le_bytes(),
        ("A0", 0, 0xef as u8 as i8 as i32 as u32),
        ("A1", (-4i32 as u32), (-4i32 as u32))
    ); // Hacky method for sign extension

    run_test_with_mem(&test_data, 10i32 as u32, 0xdeadbeef, 0xdeadbeef);
}

#[test]
fn test_lh() {
    let test_data = generate_test_data!(
        0x00e59503u32.to_le_bytes(),
        ("A0", 0, 0xbeef as u16 as i16 as i32 as u32),
        ("A1", (-4i32 as u32), (-4i32 as u32))
    ); // Hacky method for sign extension

    run_test_with_mem(&test_data, 10i32 as u32, 0xdeadbeef, 0xdeadbeef);
}

#[test]
fn test_lw() {
    let test_data = generate_test_data!(0x00e5a503u32.to_le_bytes(), ("A0", 0, 0xdeadbeef), ("A1", (-4i32 as u32), (-4i32 as u32)));

    run_test_with_mem(&test_data, 10i32 as u32, 0xdeadbeef, 0xdeadbeef);
}

#[test]
fn test_lbu() {
    let test_data = generate_test_data!(0x00e5c503u32.to_le_bytes(), ("A0", 0, 0xef as u32), ("A1", (-4i32 as u32), (-4i32 as u32)));

    run_test_with_mem(&test_data, 10i32 as u32, 0xdeadbeef, 0xdeadbeef);
}

#[test]
fn test_lhu() {
    let test_data = generate_test_data!(0x00e5d503u32.to_le_bytes(), ("A0", 0, 0xbeef), ("A1", (-4i32 as u32), (-4i32 as u32)));

    run_test_with_mem(&test_data, 10i32 as u32, 0xdeadbeef, 0xdeadbeef);
}

#[test]
fn test_sb() {
    let test_data = generate_test_data!(0x00a58723u32.to_le_bytes(), ("A0", 0xdeadbeef, 0xdeadbeef), ("A1", (-4i32 as u32), (-4i32 as u32)));

    run_test_with_mem(&test_data, 10i32 as u32, 0x0, 0xef);
}

#[test]
fn test_sh() {
    let test_data = generate_test_data!(0x00a59723u32.to_le_bytes(), ("A0", 0xdeadbeef, 0xdeadbeef), ("A1", (-4i32 as u32), (-4i32 as u32)));

    run_test_with_mem(&test_data, 10i32 as u32, 0x0, 0xbeef);
}

#[test]
fn test_sw() {
    let test_data = generate_test_data!(0x00a5a723u32.to_le_bytes(), ("A0", 0xdeadbeef, 0xdeadbeef), ("A1", (-4i32 as u32), (-4i32 as u32)));

    run_test_with_mem(&test_data, 10i32 as u32, 0x0, 0xdeadbeef);
}

#[test]
fn test_beq_ne() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b50c63u32.to_le_bytes(), ("A0", 0x01, 0x01), ("A1", 5, 5), ("PC", start_pc, start_pc + 4));
    run_test_no_mem(&test_data);
}

#[test]
fn test_beq_eq() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b50c63u32.to_le_bytes(), ("A0", 5, 5), ("A1", 5, 5), ("PC", start_pc, start_pc + 24));
    run_test_no_mem(&test_data);
}

#[test]
fn test_bne_ne() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b51c63u32.to_le_bytes(), ("A0", 0x01, 0x01), ("A1", 5, 5), ("PC", start_pc, start_pc + 24));
    run_test_no_mem(&test_data);
}

#[test]
fn test_bne_eq() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b51c63u32.to_le_bytes(), ("A0", 5, 5), ("A1", 5, 5), ("PC", start_pc, start_pc + 4));
    run_test_no_mem(&test_data);
}

#[test]
fn test_blt_gt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b54c63u32.to_le_bytes(),
        ("A0", 10, 10),
        ("A1", (-25i32) as u32, (-25i32) as u32),
        ("PC", start_pc, start_pc + 4)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_blt_eq() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b54c63u32.to_le_bytes(), ("A0", 5, 5), ("A1", 5, 5), ("PC", start_pc, start_pc + 4));
    run_test_no_mem(&test_data);
}

#[test]
fn test_blt_lt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b54c63u32.to_le_bytes(),
        ("A0", (-25i32) as u32, (-25i32) as u32),
        ("A1", 5, 5),
        ("PC", start_pc, start_pc + 24)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_bge_gt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b55c63u32.to_le_bytes(),
        ("A0", 10, 10),
        ("A1", (-25i32) as u32, (-25i32) as u32),
        ("PC", start_pc, start_pc + 24)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_bge_eq() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b55c63u32.to_le_bytes(), ("A0", 5, 5), ("A1", 5, 5), ("PC", start_pc, start_pc + 24));
    run_test_no_mem(&test_data);
}

#[test]
fn test_bge_lt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b55c63u32.to_le_bytes(),
        ("A0", (-25i32) as u32, (-25i32) as u32),
        ("A1", 5, 5),
        ("PC", start_pc, start_pc + 4)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_bltu_gt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b56c63u32.to_le_bytes(),
        ("A0", (-25i32) as u32, (-25i32) as u32), //Unsigned interpretation: [(-25i32) = 11100111u32] > 10
        ("A1", 10, 10),
        ("PC", start_pc, start_pc + 4)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_bltu_eq() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b56c63u32.to_le_bytes(), ("A0", 5, 5), ("A1", 5, 5), ("PC", start_pc, start_pc + 4));
    run_test_no_mem(&test_data);
}

#[test]
fn test_bltu_lt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b56c63u32.to_le_bytes(),
        ("A0", 10, 10),
        ("A1", (-25i32) as u32, (-25i32) as u32), //Unsigned interpretation: [(-25i32) = 11100111u32] > 10
        ("PC", start_pc, start_pc + 24)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_bgeu_gt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b57c63u32.to_le_bytes(),
        ("A0", (-25i32) as u32, (-25i32) as u32), //Unsigned interpretation: [(-25i32) = 11100111u32] > 10
        ("A1", 10, 10),
        ("PC", start_pc, start_pc + 24)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_bgeu_eq() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00b57c63u32.to_le_bytes(), ("A0", 5, 5), ("A1", 5, 5), ("PC", start_pc, start_pc + 24));
    run_test_no_mem(&test_data);
}

#[test]
fn test_bgeu_lt() {
    let start_pc = 16;
    let test_data = generate_test_data!(
        0x00b57c63u32.to_le_bytes(),
        ("A0", 10, 10),
        ("A1", (-25i32) as u32, (-25i32) as u32), //Unsigned interpretation: [(-25i32) = 11100111u32] > 10
        ("PC", start_pc, start_pc + 4)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_jal() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x0100056fu32.to_le_bytes(), ("A0", 0x0, start_pc + 4), ("PC", start_pc, start_pc + 16));
    run_test_no_mem(&test_data);
}

#[test]
fn test_lui() {
    let test_data = generate_test_data!(0x03039537u32.to_le_bytes(), ("A0", 65829842, 12345 << 12));
    run_test_no_mem(&test_data);
}

#[test]
fn test_auipc() {
    let start_pc = 16;
    let test_data = generate_test_data!(0x00018517u32.to_le_bytes(), ("A0", 64763252, start_pc + (24 << 12)), ("PC", start_pc, start_pc + 4));
    run_test_no_mem(&test_data);
}

// Jump to an address formed by adding xs1 to a signed offset
// then clearing the least significant bit,
// and store the return address in xd.
#[test]
fn test_jalr() {
    let offset: i32 = -25; // NOTE: this is included in the instruction bytes and is only
                           // repeated here for clarity.
                           // 25 is chosen on purpose as we throw away the least significant bit

    let start_pc: i32 = 32;
    let xs1: i32 = 8;
    let address: i32 = ((xs1 + offset) & !1); // `& !1` clears the least significant bit

    let test_data = generate_test_data!(
        0xfe758567u32.to_le_bytes(),
        ("A0", 0x0, start_pc as u32 + 4),
        ("A1", xs1 as u32, xs1 as u32),
        ("PC", start_pc as u32, address as u32)
    );
    run_test_no_mem(&test_data);
}

#[test]
fn test_write_to_zero() {
    let test_data = generate_test_data!(0x00B50533u32.to_le_bytes(), ("ZERO", 0x5u32, 0x0u32), ("A1", 0x1u32, 0x1u32));
    run_test_no_mem(&test_data);
}
