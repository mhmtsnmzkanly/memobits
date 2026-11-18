//! A private LIFO byte heap for non-escaping lexical String owners.

use super::{memory, string_descriptor};
use wasm_encoder::{BlockType, Function, Instruction as I, ValType};

pub(super) const CURSOR_GLOBAL: u32 = 3;

const LEFT: u32 = 0;
const RIGHT: u32 = 1;
const DESTINATION: u32 = 2;
const LEFT_LEN: u32 = 3;
const RIGHT_LEN: u32 = 4;
const START: u32 = 5;
const PAGES: u32 = 6;
const END: u32 = 7;

/// Build the private guest helper. A false result leaves
/// the cursor and destination untouched.
pub(super) fn initializer() -> Function {
    let mut body = Function::new([(4, ValType::I32), (1, ValType::I64)]);
    for (descriptor, length) in [(LEFT, LEFT_LEN), (RIGHT, RIGHT_LEN)] {
        body.instruction(&I::LocalGet(descriptor));
        string_descriptor::load_length(&mut body);
        body.instruction(&I::LocalSet(length));
    }

    body.instructions()
        .global_get(CURSOR_GLOBAL)
        .local_tee(START)
        .i64_extend_i32_u()
        .local_get(LEFT_LEN)
        .i64_extend_i32_u()
        .i64_add()
        .local_get(RIGHT_LEN)
        .i64_extend_i32_u()
        .i64_add()
        .local_tee(END)
        .i64_const((memory::MAX_PAGES * memory::PAGE_BYTES) as i64)
        .i64_gt_u();
    failure_if(&mut body);

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
    failure_if(&mut body);
    body.instruction(&I::End);

    for (descriptor, length) in [(LEFT, LEFT_LEN), (RIGHT, RIGHT_LEN)] {
        body.instruction(&I::LocalGet(START));
        if descriptor == RIGHT {
            body.instructions().local_get(LEFT_LEN).i32_add();
        }
        body.instruction(&I::LocalGet(descriptor));
        string_descriptor::load_address(&mut body);
        body.instructions().local_get(length).memory_copy(0, 0);
    }

    body.instructions().local_get(DESTINATION).local_get(START);
    string_descriptor::store_address(&mut body);
    body.instructions()
        .local_get(DESTINATION)
        .local_get(LEFT_LEN)
        .local_get(RIGHT_LEN)
        .i32_add();
    string_descriptor::store_length(&mut body);
    body.instructions()
        .local_get(END)
        .i32_wrap_i64()
        .global_set(CURSOR_GLOBAL)
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

/// The IR validator proves this descriptor is the most recent allocation.
pub(super) fn release(body: &mut Function) {
    string_descriptor::load_address(body);
    body.instruction(&I::GlobalSet(CURSOR_GLOBAL));
}
