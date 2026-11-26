//! Private Wasm32 cell of a `Box` owner: one pointer word.
//!
//! The cell holds the address of the box's heap block, or zero for an empty
//! (never filled or moved-out) box. The block is a whole-block allocation
//! (`string_heap`) whose payload, at `CONTENT_OFFSET`, is one value with the
//! element type's own layout. There is no length and no capacity.

use super::{memory_arg, string_heap, Primitive};
use wasm_encoder::{Function, Instruction};

pub(super) const SIZE: u32 = 4;
pub(super) const ALIGN: u32 = 4;
/// Offset of the boxed value inside the block.
pub(super) const CONTENT_OFFSET: i32 = string_heap::HEADER_BYTES;

/// With the cell address on the stack, load the block address.
pub(super) fn load_block(body: &mut Function) {
    body.instruction(&Instruction::I32Load(memory_arg(Primitive::U32)));
}

/// With the cell address and the block address on the stack, store the block.
pub(super) fn store_block(body: &mut Function) {
    body.instruction(&Instruction::I32Store(memory_arg(Primitive::U32)));
}

/// Zero the cell at the address on the stack: empty, or moved out.
pub(super) fn clear(body: &mut Function) {
    body.instruction(&Instruction::I32Const(0));
    store_block(body);
}
