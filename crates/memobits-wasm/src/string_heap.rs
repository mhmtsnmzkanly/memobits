//! Private whole-block free list for scoped String owners.

use super::{memory, memory_arg, string_descriptor, Primitive};
use wasm_encoder::{BlockType, Function, Instruction as I, MemArg, ValType};

pub(super) const CURSOR_GLOBAL: u32 = 3;
pub(super) const FREE_GLOBAL: u32 = 4;
pub(super) const BLOCK_ALIGN: u32 = 4;
const CAPACITY_OFFSET: u64 = 0;
const NEXT_OFFSET: u64 = 4;
const HEADER_BYTES: i32 = 8;

const LEFT: u32 = 0;
const RIGHT: u32 = 1;
const DESTINATION: u32 = 2;
const LEFT_LEN: u32 = 3;
const RIGHT_LEN: u32 = 4;
const LEN: u32 = 5;
const BLOCK: u32 = 6;
const PREVIOUS: u32 = 7;
const PAGES: u32 = 8;
const END: u32 = 9;

/// Return false on size or growth failure, leaving allocator state and
/// the destination untouched. Inputs are live, so none can be free blocks.
pub(super) fn initializer() -> Function {
    let mut body = Function::new([(6, ValType::I32), (1, ValType::I64)]);
    for (descriptor, length) in [(LEFT, LEFT_LEN), (RIGHT, RIGHT_LEN)] {
        body.instruction(&I::LocalGet(descriptor));
        string_descriptor::load_length(&mut body);
        body.instruction(&I::LocalSet(length));
    }
    body.instructions()
        .local_get(LEFT_LEN)
        .i64_extend_i32_u()
        .local_get(RIGHT_LEN)
        .i64_extend_i32_u()
        .i64_add()
        .local_tee(END)
        .i64_const((memory::MAX_PAGES * memory::PAGE_BYTES) as i64)
        .i64_gt_u();
    failure_if(&mut body);
    body.instructions()
        .local_get(END)
        .i32_wrap_i64()
        .local_set(LEN);

    // Search without changing the list. Every linked block came from this
    // allocator and has an aligned header in already committed memory.
    body.instructions()
        .global_get(FREE_GLOBAL)
        .local_set(BLOCK)
        .block(BlockType::Empty)
        .loop_(BlockType::Empty)
        .local_get(BLOCK)
        .i32_eqz()
        .br_if(1)
        .local_get(BLOCK)
        .i32_load(header_field(CAPACITY_OFFSET))
        .local_get(LEN)
        .i32_ge_u()
        .br_if(1)
        .local_get(BLOCK)
        .local_tee(PREVIOUS)
        .i32_load(header_field(NEXT_OFFSET))
        .local_set(BLOCK)
        .br(0)
        .end()
        .end();

    body.instructions()
        .local_get(BLOCK)
        .i32_eqz()
        .if_(BlockType::Empty);
    extend_heap(&mut body);
    body.instruction(&I::Else);
    unlink_block(&mut body);
    body.instruction(&I::End);

    for (descriptor, length) in [(LEFT, LEFT_LEN), (RIGHT, RIGHT_LEN)] {
        body.instructions()
            .local_get(BLOCK)
            .i32_const(HEADER_BYTES)
            .i32_add();
        if descriptor == RIGHT {
            body.instructions().local_get(LEFT_LEN).i32_add();
        }
        body.instruction(&I::LocalGet(descriptor));
        string_descriptor::load_address(&mut body);
        body.instructions().local_get(length).memory_copy(0, 0);
    }

    body.instructions()
        .local_get(DESTINATION)
        .local_get(BLOCK)
        .i32_const(HEADER_BYTES)
        .i32_add();
    string_descriptor::store_address(&mut body);
    body.instructions().local_get(DESTINATION).local_get(LEN);
    string_descriptor::store_length(&mut body);
    body.instructions().local_get(DESTINATION).local_get(BLOCK);
    string_descriptor::store_allocation(&mut body);
    body.instructions().i32_const(1).end();
    body
}

fn extend_heap(body: &mut Function) {
    // Calculate the aligned exclusive end in i64, including the block header.
    body.instructions()
        .global_get(CURSOR_GLOBAL)
        .local_tee(BLOCK)
        .i64_extend_i32_u()
        .i64_const(i64::from(HEADER_BYTES))
        .i64_add()
        .local_get(LEN)
        .i64_extend_i32_u()
        .i64_add()
        .i64_const(i64::from(BLOCK_ALIGN - 1))
        .i64_add()
        .i64_const(-i64::from(BLOCK_ALIGN))
        .i64_and()
        .local_tee(END)
        .i64_const((memory::MAX_PAGES * memory::PAGE_BYTES) as i64)
        .i64_gt_u();
    failure_if(body);

    body.instructions()
        .local_get(END)
        .i64_const((memory::PAGE_BYTES - 1) as i64)
        .i64_add()
        .i64_const(16)
        .i64_shr_u()
        .i32_wrap_i64()
        .local_tee(PAGES)
        .memory_size(0)
        .i32_gt_u()
        .if_(BlockType::Empty)
        .local_get(PAGES)
        .memory_size(0)
        .i32_sub()
        .memory_grow(0)
        .i32_const(-1)
        .i32_eq();
    failure_if(body);
    body.instruction(&I::End);

    // Only publish the new extent after all checks, including memory.grow.
    body.instructions()
        .local_get(BLOCK)
        .local_get(END)
        .i32_wrap_i64()
        .local_get(BLOCK)
        .i32_sub()
        .i32_const(HEADER_BYTES)
        .i32_sub()
        .i32_store(header_field(CAPACITY_OFFSET))
        .local_get(END)
        .i32_wrap_i64()
        .global_set(CURSOR_GLOBAL);
}

fn unlink_block(body: &mut Function) {
    body.instructions()
        .local_get(PREVIOUS)
        .i32_eqz()
        .if_(BlockType::Empty)
        .local_get(BLOCK)
        .i32_load(header_field(NEXT_OFFSET))
        .global_set(FREE_GLOBAL)
        .else_()
        .local_get(PREVIOUS)
        .local_get(BLOCK)
        .i32_load(header_field(NEXT_OFFSET))
        .i32_store(header_field(NEXT_OFFSET))
        .end();
}

fn failure_if(body: &mut Function) {
    body.instructions()
        .if_(BlockType::Empty)
        .i32_const(0)
        .return_()
        .end();
}

/// Receives the descriptor address. Zero provenance denotes static storage.
pub(super) fn releaser() -> Function {
    let mut body = Function::new([(1, ValType::I32)]);
    body.instruction(&I::LocalGet(0));
    string_descriptor::load_allocation(&mut body);
    body.instructions()
        .local_tee(1)
        .if_(BlockType::Empty)
        .local_get(1)
        .global_get(FREE_GLOBAL)
        .i32_store(header_field(NEXT_OFFSET))
        .local_get(1)
        .global_set(FREE_GLOBAL)
        .end()
        .end();
    body
}

fn header_field(offset: u64) -> MemArg {
    MemArg {
        offset,
        ..memory_arg(Primitive::U32)
    }
}
