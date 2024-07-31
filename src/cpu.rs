use crate::opcodes;
use std::collections::HashMap;

use bitflags::bitflags;
use log::*;

bitflags! {
    /// # Status Register (P) http://wiki.nesdev.com/w/index.php/Status_flags
    ///
    ///  7 6 5 4 3 2 1 0
    ///  N V _ B D I Z C
    ///  | |   | | | | +--- Carry Flag
    ///  | |   | | | +----- Zero Flag
    ///  | |   | | +------- Interrupt Disable
    ///  | |   | +--------- Decimal Mode (not used on NES)
    ///  | |   +----------- Break Command
    ///  | +--------------- Overflow Flag
    ///  +----------------- Negative Flag
    ///
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIV           = 0b10000000;
    }
}

// const STACK: u16 = 0x0100;
// const STACK_RESET: u8 = 0xfd;

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    // pub stack_pointer: u8,
    memory: [u8; 0xFFFF],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::empty(),
            program_counter: 0,
            memory: [0; 0xFFFF],
        }
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter) as u16,
            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }

            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }

            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }

            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = CpuFlags::empty();
        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
        assert_eq!(self.mem_read_u16(0xFFFC), 0x8000);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    pub fn run(&mut self) {
        let opcodes: &HashMap<u8, &'static opcodes::OpCode> = &*opcodes::OPCODES_MAP;

        loop {
            let code = self.mem_read(self.program_counter);
            debug!("pc: 0x{:02x}, code: 0x{:02x}", self.program_counter, code);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes
                .get(&code)
                .expect(&format!("OpCode 0x{:x} is not recognized", code));

            match code {
                // BRK
                0x00 => {
                    return;
                }

                // ADC
                0x69 | 0x65 | 0x75 | 0x6D | 0x7D | 0x79 | 0x61 | 0x71 => self.adc(&opcode.mode),

                // SBC
                0xe9 | 0xe5 | 0xf5 | 0xed | 0xfd | 0xf9 | 0xe1 | 0xf1 => {
                    self.sbc(&opcode.mode);
                }

                /* AND */
                0x29 | 0x25 | 0x35 | 0x2d | 0x3d | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }

                /* EOR */
                0x49 | 0x45 | 0x55 | 0x4d | 0x5d | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }

                // LDA
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => self.lda(&opcode.mode),

                // TAX
                0xaa => {
                    dbg!("TAX");
                    self.tax();
                }

                // STA
                0x85 => {
                    self.sta(&AddressingMode::ZeroPage);
                    self.program_counter += 1;
                }

                0x95 => {
                    self.sta(&AddressingMode::ZeroPage_X);
                    self.program_counter += 1;
                }

                // INX
                0xE8 => {
                    self.inx();
                }
                _ => todo!(""),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }

    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn add_to_register_a(&mut self, data: u8) {
        let (sum, carry) = self.register_a.overflowing_add(data);
        let (sum, carry) = if self.status.contains(CpuFlags::CARRY) {
            let (sum, carry1) = sum.overflowing_add(1);
            (sum, carry | carry1)
        } else {
            (sum, carry)
        };

        if carry {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        // Overflow flag
        // http://www.6502.org/tutorials/vflag.html
        //
        // a + b = c
        // postive + positive = negative
        // negative + negaitve = positive
        if (data ^ sum) & (self.register_a ^ sum) & 0x80 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW);
        }

        self.set_register_a(sum);
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let data = self.mem_read(addr);
        self.add_to_register_a(((data as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.add_to_register_a(value);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(self.register_a & value);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.set_register_a(data ^ self.register_a);
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            // self.status |= 0b0000_0010;
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if result & 0b1000_000 != 0 {
            self.status.insert(CpuFlags::NEGATIV);
        } else {
            self.status.remove(CpuFlags::NEGATIV);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0x69, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0x01);
        assert!(!cpu.status.contains(CpuFlags::CARRY));

        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0x69, 0xFF, 0x69, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0x00);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_sbc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xe9, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0xFE);
        assert!(!cpu.status.contains(CpuFlags::CARRY));

        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xe9, 0xFE, 0x00]);
        assert_eq!(cpu.register_a, 0x01);
        assert!(!cpu.status.contains(CpuFlags::CARRY));

        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xe9, 0x01, 0xe9, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0xFC);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::new();

        cpu.load_and_run(vec![0x69, 0x03, 0x29, 0x00, 0x00]);
        assert_eq!(cpu.register_a, 0x00);

        cpu.load_and_run(vec![0x69, 0x03, 0x29, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0x01);

        cpu.load_and_run(vec![0x69, 0x03, 0x29, 0x02, 0x00]);
        assert_eq!(cpu.register_a, 0x02);

        cpu.load_and_run(vec![0x69, 0x03, 0x29, 0x03, 0x00]);
        assert_eq!(cpu.register_a, 0x03);

        cpu.load_and_run(vec![0x69, 0x03, 0x29, 0x04, 0x00]);
        assert_eq!(cpu.register_a, 0x00);
    }

    #[test]
    fn test_eor() {
        let mut cpu = CPU::new();

        // 11 ^ 01 == 10
        cpu.load_and_run(vec![0x69, 0x03, 0x49, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0x02);

        // 11 ^ 11 == 00
        cpu.load_and_run(vec![0x69, 0x03, 0x49, 0x03, 0x00]);
        assert_eq!(cpu.register_a, 0x00);

        // 11 ^ 00 == 11
        cpu.load_and_run(vec![0x69, 0x03, 0x49, 0x00, 0x00]);
        assert_eq!(cpu.register_a, 0x03);
    }

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);
        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let mut cpu = CPU::new();
        // cpu.register_a = 10;
        cpu.load_and_run(vec![
            // a = 5
            0xa9, 0x05, // x = a
            0xaa, 0x00,
        ]);
        assert_eq!(cpu.register_x, 5);
    }

    // #[test]
    // fn test_5_ops_working_together() {
    //     let mut cpu = CPU::new();
    //     cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

    //     assert_eq!(cpu.register_x, 0xc1)
    // }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        cpu.register_x = 0xff;
        cpu.load_and_run(vec![
            // a = 0xff
            0xa9, 0xff, // x = a
            0xaa, // inc x, inc x
            0xe8, 0xe8, 0x00,
        ]);
        assert_eq!(cpu.register_x, 1)
    }
}
