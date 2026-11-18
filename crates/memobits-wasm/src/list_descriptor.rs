//! Private Wasm32 descriptor for whole List owners.

use super::{memory, memory_arg, string_heap, Primitive};
use wasm_encoder::{BlockType, Function, Instruction, MemArg, ValType};

pub(super) const ALIGN: u32 = 4;
// Reserve a data address, element count, and allocation handle.
pub(super) const SIZE: u32 = 12;
const DATA_OFFSET: u64 = 0;
const LENGTH_OFFSET: u64 = 4;
const ALLOCATION_OFFSET: u64 = 8;

pub(super) fn initialize_empty(body: &mut Function) {
    body.instructions()
        .i32_const(0)
        .i32_const(SIZE as i32)
        .memory_fill(0);
}

pub(super) fn load_length(body: &mut Function) {
    body.instruction(&Instruction::I32Load(field(LENGTH_OFFSET)));
}

pub(super) fn load_allocation(body: &mut Function) {
    body.instruction(&Instruction::I32Load(field(ALLOCATION_OFFSET)));
}

pub(super) fn clear_allocation(body: &mut Function) {
    body.instructions()
        .i32_const(0)
        .i32_store(field(ALLOCATION_OFFSET));
}

fn field(offset: u64) -> MemArg {
    MemArg {
        offset,
        ..memory_arg(Primitive::U32)
    }
}

/// Append a single primitive. A failed reserve leaves the old owner intact.
pub(super) fn push(reserve: u32, release: u32) -> Function {
    const OWNER: u32 = 0;
    const VALUE: u32 = 1;
    const WIDTH: u32 = 2;
    const LENGTH: u32 = 3;
    const OLD: u32 = 4;
    const BLOCK: u32 = 5;
    const DATA: u32 = 6;
    const USED: u32 = 7;
    const REQUIRED: u32 = 8;
    const WIDE: u32 = 9;
    const MAX_BYTES: i64 =
        (memory::MAX_PAGES * memory::PAGE_BYTES) as i64 - string_heap::HEADER_BYTES as i64;

    let mut body = Function::new([(6, ValType::I32), (1, ValType::I64)]);
    body.instructions().local_get(OWNER);
    load_length(&mut body);
    body.instructions()
        .local_tee(LENGTH)
        .i64_extend_i32_u()
        .i64_const(1)
        .i64_add()
        .local_get(WIDTH)
        .i64_extend_i32_u()
        .i64_mul()
        .local_tee(WIDE)
        .i64_const(MAX_BYTES)
        .i64_gt_u();
    failure_if(&mut body);
    body.instructions()
        .local_get(WIDE)
        .i32_wrap_i64()
        .local_tee(REQUIRED)
        .local_get(WIDTH)
        .i32_sub()
        .local_set(USED)
        .local_get(OWNER);
    load_allocation(&mut body);
    body.instructions()
        .local_tee(OLD)
        .local_tee(BLOCK)
        .i32_eqz()
        .if_(BlockType::Result(ValType::I32))
        .i32_const(0)
        .else_()
        .local_get(OLD);
    string_heap::load_capacity(&mut body);
    body.instructions()
        .end()
        .local_get(REQUIRED)
        .i32_lt_u()
        .if_(BlockType::Empty);

    // Double the required size when it fits. Retry the exact request if
    // the larger reservation would exceed the current memory limit.
    body.instructions()
        .i32_const(0)
        .local_set(BLOCK)
        .local_get(WIDE)
        .i64_const(2)
        .i64_mul()
        .local_tee(WIDE)
        .i64_const(MAX_BYTES)
        .i64_le_u()
        .if_(BlockType::Empty)
        .local_get(WIDE)
        .i32_wrap_i64()
        .call(reserve)
        .local_set(BLOCK)
        .end()
        .local_get(BLOCK)
        .i32_eqz()
        .if_(BlockType::Empty)
        .local_get(REQUIRED)
        .call(reserve)
        .local_set(BLOCK)
        .end()
        .local_get(BLOCK)
        .i32_eqz();
    failure_if(&mut body);
    body.instructions()
        .local_get(USED)
        .if_(BlockType::Empty)
        .local_get(BLOCK)
        .i32_const(string_heap::HEADER_BYTES)
        .i32_add()
        .local_get(OWNER)
        .i32_load(field(DATA_OFFSET))
        .local_get(USED)
        .memory_copy(0, 0)
        .end()
        .end();

    body.instructions()
        .local_get(BLOCK)
        .i32_const(string_heap::HEADER_BYTES)
        .i32_add()
        .local_set(DATA);
    for (width, element) in [(1, Primitive::U8), (4, Primitive::U32)] {
        body.instructions()
            .local_get(WIDTH)
            .i32_const(width)
            .i32_eq()
            .if_(BlockType::Empty)
            .local_get(DATA)
            .local_get(USED)
            .i32_add()
            .local_get(VALUE);
        super::emit_store(&mut body, element);
        body.instructions().end();
    }
    body.instructions()
        .local_get(OWNER)
        .local_get(DATA)
        .i32_store(field(DATA_OFFSET))
        .local_get(OWNER)
        .local_get(BLOCK)
        .i32_store(field(ALLOCATION_OFFSET))
        .local_get(OWNER)
        .local_get(LENGTH)
        .i32_const(1)
        .i32_add()
        .i32_store(field(LENGTH_OFFSET))
        .local_get(OLD)
        .local_get(BLOCK)
        .i32_ne()
        .if_(BlockType::Empty)
        .local_get(OLD)
        .call(release)
        .end()
        .i32_const(1)
        .end();
    body
}

fn failure_if(body: &mut Function) {
    body.instructions()
        .if_(BlockType::Empty)
        .i32_const(0)
        .return_()
        .end();
}
