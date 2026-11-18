//! Private Wasm32 descriptor for whole List owners.

use super::{memory_arg, Primitive};
use wasm_encoder::{Function, Instruction};

pub(super) const ALIGN: u32 = 4;
// Reserve a data address, element count, and allocation handle.
pub(super) const SIZE: u32 = 12;
const LENGTH_OFFSET: u64 = 4;

pub(super) fn initialize_empty(body: &mut Function) {
    body.instructions()
        .i32_const(0)
        .i32_const(SIZE as i32)
        .memory_fill(0);
}

pub(super) fn load_length(body: &mut Function) {
    body.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
        offset: LENGTH_OFFSET,
        ..memory_arg(Primitive::U32)
    }));
}
