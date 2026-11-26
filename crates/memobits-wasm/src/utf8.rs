//! Strict validation of a fixed buffer's logical prefix.

use super::{
    emit_address, emit_store, memory_arg, FrameState, Primitive, Program, StructLayout, Type,
    TypeDefKind,
};
use wasm_encoder::{BlockType, Function, ValType};

const BYTES: u32 = 0;
const LENGTH: u32 = 1;
const BOUND: u32 = 2;
const INDEX: u32 = 3;
const COUNT: u32 = 4;
const LEAD: u32 = 5;
const REMAINING: u32 = 6;
const LOW: u32 = 7;
const HIGH: u32 = 8;
const BYTE: u32 = 9;

/// The high word holds the error code (zero on success). The low word is
/// the scalar count on success, or the byte offset for encoding errors.
pub(super) fn validator() -> Function {
    let mut body = Function::new([(7, ValType::I32)]);
    body.instructions()
        .local_get(LENGTH)
        .i32_const(0)
        .i32_lt_s()
        .local_get(LENGTH)
        .local_get(BOUND)
        .i32_gt_u()
        .i32_or()
        .if_(BlockType::Empty);
    return_status(&mut body, 1, INDEX);
    body.instructions()
        .end()
        .loop_(BlockType::Empty)
        .local_get(INDEX)
        .local_get(LENGTH)
        .i32_eq()
        .if_(BlockType::Empty);
    return_status(&mut body, 0, COUNT);
    body.instructions().end();
    load_byte(&mut body, LEAD);
    increment(&mut body, COUNT);
    body.instructions()
        .local_get(LEAD)
        .i32_const(127)
        .i32_le_u()
        .if_(BlockType::Empty);
    increment(&mut body, INDEX);
    body.instructions()
        .br(1)
        .end()
        .local_get(LEAD)
        .i32_const(194)
        .i32_lt_u()
        .local_get(LEAD)
        .i32_const(244)
        .i32_gt_u()
        .i32_or()
        .if_(BlockType::Empty);
    return_status(&mut body, 2, INDEX);
    body.instructions()
        .end()
        // Continuation count is one, plus one at each wider lead class.
        .i32_const(1)
        .local_get(LEAD)
        .i32_const(224)
        .i32_ge_u()
        .i32_add()
        .local_get(LEAD)
        .i32_const(240)
        .i32_ge_u()
        .i32_add()
        .local_set(REMAINING);
    continuation_limits(&mut body);
    increment(&mut body, INDEX);
    body.instructions()
        .loop_(BlockType::Empty)
        .local_get(INDEX)
        .local_get(LENGTH)
        .i32_eq()
        .if_(BlockType::Empty);
    return_status(&mut body, 3, INDEX);
    body.instructions().end();
    load_byte(&mut body, BYTE);
    body.instructions()
        .local_get(BYTE)
        .local_get(LOW)
        .i32_lt_u()
        .local_get(BYTE)
        .local_get(HIGH)
        .i32_gt_u()
        .i32_or()
        .if_(BlockType::Empty);
    return_status(&mut body, 4, INDEX);
    body.instructions().end();
    increment(&mut body, INDEX);
    body.instructions()
        .i32_const(128)
        .local_set(LOW)
        .i32_const(191)
        .local_set(HIGH)
        .local_get(REMAINING)
        .i32_const(1)
        .i32_sub()
        .local_tee(REMAINING)
        .br_if(0)
        .end()
        .br(0)
        .end()
        .unreachable()
        .end();
    body
}

fn continuation_limits(body: &mut Function) {
    body.instructions()
        .i32_const(128)
        .local_set(LOW)
        .i32_const(191)
        .local_set(HIGH);
    // E0 and F0 exclude overlong forms, ED excludes surrogates, and F4
    // excludes values greater than U+10FFFF.
    for (lead, limit, local) in [
        (224, 160, LOW),
        (237, 159, HIGH),
        (240, 144, LOW),
        (244, 143, HIGH),
    ] {
        body.instructions()
            .local_get(LEAD)
            .i32_const(lead)
            .i32_eq()
            .if_(BlockType::Empty)
            .i32_const(limit)
            .local_set(local)
            .end();
    }
}

fn load_byte(body: &mut Function, target: u32) {
    body.instructions()
        .local_get(BYTES)
        .local_get(INDEX)
        .i32_add()
        .i32_load8_u(memory_arg(Primitive::U8))
        .local_set(target);
}

fn increment(body: &mut Function, local: u32) {
    body.instructions()
        .local_get(local)
        .i32_const(1)
        .i32_add()
        .local_set(local);
}

fn return_status(body: &mut Function, code: i64, value: u32) {
    body.instructions()
        .local_get(value)
        .i64_extend_i32_u()
        .i64_const(code << 32)
        .i64_or()
        .return_();
}

pub(super) fn write_outcome(
    body: &mut Function,
    program: &Program,
    layouts: &[StructLayout],
    destination: (FrameState, u32),
    types: (&Type, &Type),
    status: u32,
    write_success: impl FnOnce(&mut Function, u32) -> Result<(), String>,
) -> Result<(), String> {
    let (frame, cell) = destination;
    let (ty, success) = types;
    let error = program
        .utf8_outcome_error(ty, success)
        .ok_or("invalid UTF-8 outcome")?;
    let Type::Enum(result) = ty else {
        unreachable!("checked UTF-8 outcome")
    };
    let TypeDefKind::Struct { fields } = &program.types[error.0 as usize].kind else {
        unreachable!("checked UTF-8 error")
    };
    let Type::Enum(option) = fields[1].ty else {
        unreachable!("checked UTF-8 offset")
    };
    let result = layouts[result.0 as usize].enum_layout.as_ref().unwrap();
    let error_layout = &layouts[error.0 as usize];
    let option_layout = layouts[option.0 as usize].enum_layout.as_ref().unwrap();
    let error_cell = cell + result.variants[1].offsets[0];
    let offset_cell = error_cell + error_layout.offsets[1];

    load_code(body, status);
    body.instructions().if_(BlockType::Empty);
    emit_address(body, frame, error_cell);
    body.instructions()
        .i32_const(error_layout.error_identity.unwrap() as i32);
    emit_store(body, Primitive::U32);
    emit_address(body, frame, error_cell + error_layout.offsets[0]);
    load_code(body, status);
    emit_store(body, Primitive::U32);
    emit_address(body, frame, offset_cell);
    load_code(body, status);
    body.instructions().i32_const(1).i32_eq(); // None for invalid length
    emit_store(body, Primitive::U8);
    emit_word(
        body,
        frame,
        offset_cell + option_layout.variants[0].offsets[0],
        status,
    );
    body.instructions().else_();
    write_success(body, cell + result.variants[0].offsets[0])?;
    body.instructions().end();
    emit_address(body, frame, cell);
    load_code(body, status);
    body.instructions().i32_const(0).i32_ne();
    emit_store(body, Primitive::U8);
    Ok(())
}

fn load_code(body: &mut Function, status: u32) {
    body.instructions()
        .local_get(status)
        .i64_const(32)
        .i64_shr_u()
        .i32_wrap_i64();
}

pub(super) fn emit_word(body: &mut Function, frame: FrameState, offset: u32, status: u32) {
    emit_address(body, frame, offset);
    body.instructions().local_get(status).i32_wrap_i64();
    emit_store(body, Primitive::I32);
}
