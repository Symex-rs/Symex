use general_assembly::{
    operand::{DataWord, Operand},
    operation::Operation as GAOperation,
};
use risc_v_disassembler::{parsed_instructions, ParsedInstruction32};
use transpiler::pseudo;

use super::decoder::{sealed::Into, InstructionToGAOperations};

// "PC-" is a workaround to get the current PC value, which is needed because
// Symex increments the PC BEFORE executing the instruction.
// "PC-" is handled by the hook "pc_decrementer", defined in the risc_v mod.

impl InstructionToGAOperations for parsed_instructions::add {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 + rs2;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sub {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 - rs2;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::xor {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 ^ rs2;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::or {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 | rs2;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::and {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 & rs2;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sll {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rs2:u32;

            rd = rs1 << rs2<4:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::srl {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rs2:u32;

            rd = rs1 >> rs2<4:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sra {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rs2:u32;

            rd = rs1 asr rs2<4:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::slt {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rs1:i32;
            rs2:i32;
            rd:u32;

            Ite(rs1 < rs2,
                {
                    rd = 1u32;
                },
                {
                    rd = 0u32;
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sltu {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();

        pseudo!([
            rs1:u32;
            rs2:u32;
            rd:u32;

            Ite(rs1 < rs2,
                {
                    rd = 1u32;
                },
                {
                    rd = 0u32;
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::addi {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 + imm;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::xori {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 ^ imm;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::ori {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 | imm;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::andi {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rd:u32;

            rd = rs1 & imm;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::slli {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let shamt = self.shamt.local_into();

        pseudo!([
            shamt:u8;

            rd = rs1 << shamt<4:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::srli {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let shamt = self.shamt.local_into();
        pseudo!([
            shamt:u8;

            rd = rs1 >> shamt<4:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::srai {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let shamt = self.shamt.local_into();

        pseudo!([
            shamt:u8;

            rd = rs1 asr shamt<4:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::slti {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rs1:i32;
            imm:i32;
            rd:u32;

            Ite(rs1 < imm,
                {
                    rd = 1u32;

                },
                {
                    rd = 0u32;
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sltiu {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rs1:u32;
            imm:u32;
            rd:u32;

            Ite(rs1 < imm,
                {
                    rd = 1u32;
                },
                {
                    rd = 0u32;
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::lb {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            let addr:u32 = rs1 + imm;
            let value = LocalAddress(addr, 8);
            rd = SignExtend(value, 8, 32);
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::lh {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            let addr:u32 = rs1 + imm;
            let value = LocalAddress(addr, 16);
            rd = SignExtend(value, 16, 32);
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::lw {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            let addr:u32 = rs1 + imm;
            rd = LocalAddress(addr, 32);
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::lbu {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            let addr:u32 = rs1 + imm;
            let value = LocalAddress(addr, 8);
            rd = ZeroExtend(value, 32);
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::lhu {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let rs1 = self.rs1.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            let addr:u32 = rs1 + imm;
            let value = LocalAddress(addr, 16);
            rd = ZeroExtend(value, 32);
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sb {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rs2:u8;

            let addr:u32 = rs1 + imm;
            LocalAddress(addr, 8) = rs2<7:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sh {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rs2:u16;

            let addr:u32 = rs1 + imm;
            LocalAddress(addr, 16) = rs2<15:0>;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::sw {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            let addr:u32 = rs1 + imm;
            LocalAddress(addr, 32) = rs2;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::beq {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rs1:u32;
            rs2:u32;
            imm:u32;

            Ite(rs1 == rs2,
                {
                    let target = pc + imm;
                    Jump(target);
                },
                {
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::bne {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rs1:u32;
            rs2:u32;
            imm:u32;

            Ite(rs1 != rs2,
                {
                    let target = pc + imm;
                    Jump(target);
                },
                {
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::blt {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rs1:i32;
            rs2:i32;
            imm:u32;

            Ite(rs1 < rs2,
                {
                    let target = pc + imm;
                    Jump(target);
                },
                {
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::bge {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rs1:i32;
            rs2:i32;
            imm:u32;

            Ite(rs1 >= rs2,
                {
                    let target = pc + imm;
                    Jump(target);
                },
                {
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::bltu {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rs1:u32;
            rs2:u32;
            imm:u32;

            Ite(rs1 < rs2,
                {
                    let target = pc + imm;
                    Jump(target);
                },
                {
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::bgeu {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rs1 = self.rs1.local_into();
        let rs2 = self.rs2.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rs1:u32;
            rs2:u32;
            imm:u32;

            Ite(rs1 >= rs2,
                {
                    let target = pc + imm;
                    Jump(target);
                },
                {
                }
            );
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::jal {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rd:u32;
            imm:u32;

            let target = pc + imm;
            rd = pc + 4u32;
            Jump(target);
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::jalr {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let imm = self.imm.local_into();
        let rs1 = self.rs1.local_into();
        let pc = Operand::Register("PC-".to_owned());
        let least_bit_mask = Operand::Immediate(DataWord::Word32(!0b1));

        pseudo!([
            imm:u32;
            rd:u32;

            let target = rs1 + imm;
            target = target & least_bit_mask; // Clear the least significant bit
            rd = pc + 4u32;
            Jump(target);
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::lui {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let imm = self.imm.local_into();

        pseudo!([
            rd:u32;

            rd = imm;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::auipc {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        let rd = self.rd.local_into();
        let imm = self.imm.local_into();
        let pc = Operand::Register("PC-".to_owned());

        pseudo!([
            rd:u32;

            rd = pc + imm;
        ])
    }
}

impl InstructionToGAOperations for parsed_instructions::ecall {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        vec![GAOperation::Abort {
            error: "ecall requires external system modelling".to_string(),
        }]
    }
}

impl InstructionToGAOperations for parsed_instructions::ebreak {
    fn instruction_to_ga_operations(&self, _instr: &ParsedInstruction32) -> Vec<GAOperation> {
        vec![GAOperation::Abort {
            error: "ebreak requires external system modelling".to_string(),
        }]
    }
}
