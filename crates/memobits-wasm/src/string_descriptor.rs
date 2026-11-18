//! Private Wasm32 layout shared by String literals and frame-owned descriptors.

use super::{memory_arg, Primitive};
use wasm_encoder::{Function, Instruction, MemArg};

const ADDRESS_OFFSET: u32 = 0;
const LENGTH_OFFSET: u32 = 4;
pub(super) const SIZE: u32 = 8;
pub(super) const ALIGN: u32 = 4;

pub(super) fn encode(address: u32, byte_length: u32) -> [u8; SIZE as usize] {
    let mut bytes = [0; SIZE as usize];
    for (offset, value) in [(ADDRESS_OFFSET, address), (LENGTH_OFFSET, byte_length)] {
        let start = offset as usize;
        bytes[start..start + size_of::<u32>()].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}

pub(super) fn load_address(body: &mut Function) {
    load_field(body, ADDRESS_OFFSET);
}

pub(super) fn load_length(body: &mut Function) {
    load_field(body, LENGTH_OFFSET);
}

fn load_field(body: &mut Function, offset: u32) {
    body.instruction(&Instruction::I32Load(MemArg {
        offset: u64::from(offset),
        ..memory_arg(Primitive::U32)
    }));
}

pub(super) fn store_address(body: &mut Function) {
    store_field(body, ADDRESS_OFFSET);
}

pub(super) fn store_length(body: &mut Function) {
    store_field(body, LENGTH_OFFSET);
}

fn store_field(body: &mut Function, offset: u32) {
    body.instruction(&Instruction::I32Store(MemArg {
        offset: u64::from(offset),
        ..memory_arg(Primitive::U32)
    }));
}
