use crate::cpu::AddressingMode;
use std::collections::HashMap;

use lazy_static::lazy_static;

pub struct OpCode {
    pub code: u8,
    pub mnemonic: &'static str,
    pub len: u8,
    pub cycles: u8,
    pub mode: AddressingMode,
}

impl OpCode {
    fn new(code: u8, mnemonic: &'static str, len: u8, cycles: u8, mode: AddressingMode) -> Self {
        OpCode {
            code,
            mnemonic,
            len,
            cycles,
            mode,
        }
    }
}

// https://www.nesdev.org/obelisk-6502-guide/reference.html
lazy_static! {
    pub static ref OPCODES: Vec<OpCode> = vec![
        // https://www.nesdev.org/obelisk-6502-guide/reference.html#BRK
        OpCode::new(0x00, "BRK", 1, 7, AddressingMode::NoneAddressing),
        // https://www.nesdev.org/obelisk-6502-guide/reference.html#NOP
        OpCode::new(0xea, "NOP", 1, 2, AddressingMode::NoneAddressing),

        // Arithmetic

        // https://www.nesdev.org/obelisk-6502-guide/reference.html#ADC
        OpCode::new(0x69, "ADC", 2, 2, AddressingMode::Immediate),
        OpCode::new(0x65, "ADC", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x75, "ADC", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x6d, "ADC", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x7d, "ADC", 3, 4, AddressingMode::Absolute_X),
        OpCode::new(0x79, "ADC", 3, 4, AddressingMode::Absolute_Y),
        OpCode::new(0x61, "ADC", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x71, "ADC", 2, 5, AddressingMode::Indirect_Y),

        // https://www.nesdev.org/obelisk-6502-guide/reference.html#SBC
        OpCode::new(0xe9, "SBC", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xe5, "SBC", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xf5, "SBC", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xed, "SBC", 3, 4, AddressingMode::Absolute),
        OpCode::new(0xfd, "SBC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0xf9, "SBC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0xe1, "SBC", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xf1, "SBC", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        // https://www.nesdev.org/obelisk-6502-guide/reference.html#AND
        OpCode::new(0x29, "AND", 2, 2, AddressingMode::Immediate),
        OpCode::new(0x25, "AND", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x35, "AND", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x2d, "AND", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x3d, "AND", 3, 4, AddressingMode::Absolute_X),
        OpCode::new(0x39, "AND", 3, 4, AddressingMode::Absolute_Y),
        OpCode::new(0x21, "AND", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x31, "AND", 2, 5, AddressingMode::Indirect_Y),

        // https://www.nesdev.org/obelisk-6502-guide/reference.html#EOR
        OpCode::new(0x49, "EOR", 2, 2, AddressingMode::Immediate),
        OpCode::new(0x45, "EOR", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x55, "EOR", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x4d, "EOR", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x5d, "EOR", 3, 4, AddressingMode::Absolute_X),
        OpCode::new(0x59, "EOR", 3, 4, AddressingMode::Absolute_Y),
        OpCode::new(0x41, "EOR", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x51, "EOR", 2, 5, AddressingMode::Indirect_Y),

        // https://www.nesdev.org/obelisk-6502-guide/reference.html#ASL


        //
        // https://www.nesdev.org/obelisk-6502-guide/reference.html#INX
        OpCode::new(0xe8, "INX", 1, 2, AddressingMode::NoneAddressing),

        // https://www.nesdev.org/obelisk-6502-guide/reference.html#LDA
        OpCode::new(0xa9, "LDA", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xa5, "LDA", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xb5, "LDA", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xad, "LDA", 3, 4, AddressingMode::Absolute),
        OpCode::new(0xbd, "LDA", 3, 4, AddressingMode::Absolute_X),
        OpCode::new(0xb9, "LDA", 3, 4, AddressingMode::Absolute_Y),
        OpCode::new(0xa1, "LDA", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xb1, "LDA", 2, 5, AddressingMode::Indirect_Y),

        // https://www.nesdev.org/obelisk-6502-guide/reference.html#TAX
        OpCode::new(0xaa, "TAX", 1, 1, AddressingMode::NoneAddressing),
    ];

    pub static ref OPCODES_MAP: HashMap<u8, &'static OpCode> = {
        let mut map = HashMap::new();
        for op in &*OPCODES {
            map.insert(op.code, op);
        }
        map
    };
}
