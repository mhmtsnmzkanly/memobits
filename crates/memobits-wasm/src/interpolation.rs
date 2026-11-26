//! String interpolation: one length pass, one allocation, one write pass.
//!
//! `InitInterpolatedString` computes the exact byte length of every part,
//! reserves a single heap block and writes the parts in order. The decimal and
//! UTF-8 formatting loops live in three small helper functions that are added
//! to the module only when an interpolation is reachable.

use super::{
    array_cell_of, emit_address, emit_operand, string_descriptor, string_heap, trap_if, value_type,
    FrameLayout, FrameState, Slot, TrapReason, Traps,
};
use memobits_ir::{Function, Instruction, InterpolationPart, LocalId, Operand, Primitive, Type};
use std::collections::BTreeMap;
use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

/// `int_len`, `int_write` and `char_write`, in this order.
pub(super) const HELPER_COUNT: u32 = 3;

const ASCII_ZERO: i32 = 48;
const ASCII_MINUS: i32 = 45;

fn byte_arg(offset: u64) -> MemArg {
    MemArg {
        offset,
        align: 0,
        target: wasm_encoder::MemArgTarget::Memory(0),
        ordering: None,
    }
}

/// `(value: i64, signed: i32) -> i32`: the number of bytes of the decimal
/// text of `value`, read as an `i64` when `signed` and as a `u64` otherwise.
pub(super) fn int_len() -> WasmFunction {
    const VALUE: u32 = 0;
    const SIGNED: u32 = 1;
    const MAGNITUDE: u32 = 2;
    const LEN: u32 = 3;
    let mut body = WasmFunction::new([(1, ValType::I64), (1, ValType::I32)]);
    body.instructions()
        .local_get(VALUE)
        .local_set(MAGNITUDE)
        .local_get(SIGNED)
        .local_get(VALUE)
        .i64_const(0)
        .i64_lt_s()
        .i32_and()
        .if_(BlockType::Empty)
        // Wrapping negation also yields the magnitude of the minimum.
        .i64_const(0)
        .local_get(VALUE)
        .i64_sub()
        .local_set(MAGNITUDE)
        .i32_const(1)
        .local_set(LEN)
        .end()
        .loop_(BlockType::Empty)
        .local_get(LEN)
        .i32_const(1)
        .i32_add()
        .local_set(LEN)
        .local_get(MAGNITUDE)
        .i64_const(10)
        .i64_div_u()
        .local_tee(MAGNITUDE)
        .i64_const(0)
        .i64_ne()
        .br_if(0)
        .end()
        .local_get(LEN)
        .end();
    body
}

/// `(destination: i32, value: i64, signed: i32) -> i32`: write the decimal
/// text at `destination` and return its length (the same as `int_len`).
pub(super) fn int_write() -> WasmFunction {
    const DESTINATION: u32 = 0;
    const VALUE: u32 = 1;
    const SIGNED: u32 = 2;
    const MAGNITUDE: u32 = 3;
    const COUNTER: u32 = 4;
    const LEN: u32 = 5;
    const POSITION: u32 = 6;
    const NEGATIVE: u32 = 7;
    let mut body = WasmFunction::new([(2, ValType::I64), (3, ValType::I32), (1, ValType::I32)]);
    body.instructions()
        .local_get(VALUE)
        .local_set(MAGNITUDE)
        .local_get(SIGNED)
        .local_get(VALUE)
        .i64_const(0)
        .i64_lt_s()
        .i32_and()
        .local_tee(NEGATIVE)
        .if_(BlockType::Empty)
        .i64_const(0)
        .local_get(VALUE)
        .i64_sub()
        .local_set(MAGNITUDE)
        .end()
        // Count the digits on a copy of the magnitude.
        .local_get(MAGNITUDE)
        .local_set(COUNTER)
        .loop_(BlockType::Empty)
        .local_get(LEN)
        .i32_const(1)
        .i32_add()
        .local_set(LEN)
        .local_get(COUNTER)
        .i64_const(10)
        .i64_div_u()
        .local_tee(COUNTER)
        .i64_const(0)
        .i64_ne()
        .br_if(0)
        .end()
        .local_get(LEN)
        .local_get(NEGATIVE)
        .i32_add()
        .local_set(LEN)
        // Write the digits from the end.
        .local_get(DESTINATION)
        .local_get(LEN)
        .i32_add()
        .local_set(POSITION)
        .loop_(BlockType::Empty)
        .local_get(POSITION)
        .i32_const(1)
        .i32_sub()
        .local_tee(POSITION)
        .local_get(MAGNITUDE)
        .i64_const(10)
        .i64_rem_u()
        .i32_wrap_i64()
        .i32_const(ASCII_ZERO)
        .i32_add()
        .i32_store8(byte_arg(0))
        .local_get(MAGNITUDE)
        .i64_const(10)
        .i64_div_u()
        .local_tee(MAGNITUDE)
        .i64_const(0)
        .i64_ne()
        .br_if(0)
        .end()
        .local_get(NEGATIVE)
        .if_(BlockType::Empty)
        .local_get(DESTINATION)
        .i32_const(ASCII_MINUS)
        .i32_store8(byte_arg(0))
        .end()
        .local_get(LEN)
        .end();
    body
}

/// `(destination: i32, scalar: i32) -> i32`: write the UTF-8 encoding of a
/// Unicode scalar value and return its length.
pub(super) fn char_write() -> WasmFunction {
    const DESTINATION: u32 = 0;
    const SCALAR: u32 = 1;
    let mut body = WasmFunction::new([]);
    // continuation(shift): 0x80 | ((scalar >> shift) & 0x3f)
    let continuation = |body: &mut WasmFunction, offset: u64, shift: i32| {
        body.instructions()
            .local_get(DESTINATION)
            .local_get(SCALAR)
            .i32_const(shift)
            .i32_shr_u()
            .i32_const(0x3f)
            .i32_and()
            .i32_const(0x80)
            .i32_or()
            .i32_store8(byte_arg(offset));
    };
    let lead = |body: &mut WasmFunction, marker: i32, shift: i32| {
        body.instructions()
            .local_get(DESTINATION)
            .local_get(SCALAR)
            .i32_const(shift)
            .i32_shr_u()
            .i32_const(marker)
            .i32_or()
            .i32_store8(byte_arg(0));
    };
    body.instructions()
        .local_get(SCALAR)
        .i32_const(0x80)
        .i32_lt_u()
        .if_(BlockType::Empty)
        .local_get(DESTINATION)
        .local_get(SCALAR)
        .i32_store8(byte_arg(0))
        .i32_const(1)
        .return_()
        .end()
        .local_get(SCALAR)
        .i32_const(0x800)
        .i32_lt_u()
        .if_(BlockType::Empty);
    lead(&mut body, 0xc0, 6);
    continuation(&mut body, 1, 0);
    body.instructions().i32_const(2).return_().end();
    body.instructions()
        .local_get(SCALAR)
        .i32_const(0x10000)
        .i32_lt_u()
        .if_(BlockType::Empty);
    lead(&mut body, 0xe0, 12);
    continuation(&mut body, 1, 6);
    continuation(&mut body, 2, 0);
    body.instructions().i32_const(3).return_().end();
    lead(&mut body, 0xf0, 18);
    continuation(&mut body, 1, 12);
    continuation(&mut body, 2, 6);
    continuation(&mut body, 3, 0);
    body.instructions().i32_const(4).end();
    body
}

/// How a value part is formatted.
enum Kind {
    Text,
    Bool,
    Char,
    /// A signed or unsigned integer; `wide` means a Wasm `i64` operand.
    Integer {
        signed: bool,
        wide: bool,
    },
    /// `f32` (`wide` false) or `f64`; formatted from its bit pattern.
    Float {
        wide: bool,
    },
}

fn kind_of(ty: &Type) -> Result<Kind, String> {
    match ty {
        Type::Reference { inner, .. } if **inner == Type::String => Ok(Kind::Text),
        Type::Primitive(Primitive::Bool) => Ok(Kind::Bool),
        Type::Primitive(Primitive::Char) => Ok(Kind::Char),
        Type::Primitive(
            kind @ (Primitive::I8
            | Primitive::I16
            | Primitive::I32
            | Primitive::I64
            | Primitive::U8
            | Primitive::U16
            | Primitive::U32
            | Primitive::U64),
        ) => Ok(Kind::Integer {
            signed: matches!(
                kind,
                Primitive::I8 | Primitive::I16 | Primitive::I32 | Primitive::I64
            ),
            wide: matches!(kind, Primitive::I64 | Primitive::U64),
        }),
        Type::Primitive(Primitive::F32) => Ok(Kind::Float { wide: false }),
        Type::Primitive(Primitive::F64) => Ok(Kind::Float { wide: true }),
        _ => Err("unsupported interpolation operand type".into()),
    }
}

/// Push the operand's IEEE bit pattern as an `i64` plus the width flag
/// (`1` for `f32`) for the float helpers.
fn push_float(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    operand: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
    wide: bool,
) -> Result<(), String> {
    emit_operand(body, function, param_count, operand, layout, frame)?;
    body.instruction(&if wide {
        I::I64ReinterpretF64
    } else {
        I::I32ReinterpretF32
    });
    if !wide {
        body.instruction(&I::I64ExtendI32U);
    }
    body.instruction(&I::I32Const(i32::from(!wide)));
    Ok(())
}

/// Push the operand as an `i64` plus its signedness flag for the helpers.
fn push_integer(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    operand: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
    signed: bool,
    wide: bool,
) -> Result<(), String> {
    emit_operand(body, function, param_count, operand, layout, frame)?;
    if !wide {
        body.instruction(if signed {
            &I::I64ExtendI32S
        } else {
            &I::I64ExtendI32U
        });
    }
    body.instruction(&I::I32Const(i32::from(signed)));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn emit(
    body: &mut WasmFunction,
    instruction: &Instruction,
    function: &Function,
    param_count: u32,
    scratch64: u32,
    cursor: u32,
    layout: &FrameLayout,
    frame: Option<FrameState>,
    strings: &BTreeMap<&str, u32>,
    heap_copy_index: Option<u32>,
    helpers: Option<u32>,
    traps: &mut Traps,
    target: LocalId,
    parts: &[InterpolationPart],
) -> Result<(), String> {
    let reserve = heap_copy_index.ok_or("missing String allocation helper")? + 2;
    let int_len = helpers.ok_or("missing formatting helpers")?;
    let int_write = int_len + 1;
    let char_write = int_len + 2;
    // `float_text` and `float_write` are the last two of the float helpers
    // that follow the three above (present only when a float is reachable).
    let float_text = int_len + HELPER_COUNT + super::float_format::FUNCTION_COUNT - 2;
    let float_write = float_text + 1;
    let frame_state = frame.ok_or("interpolation local requires a frame")?;
    let cell = array_cell_of(layout, Slot::Local(target.0))?;

    // Pass 1: the exact length as a 64-bit sum.
    body.instruction(&I::I64Const(0));
    for part in parts {
        match part {
            InterpolationPart::Text(text) => {
                body.instruction(&I::I64Const(text.len() as i64));
            }
            InterpolationPart::Value(operand) => match kind_of(&value_type(function, operand)?)? {
                Kind::Text => {
                    emit_operand(body, function, param_count, operand, layout, frame)?;
                    string_descriptor::load_length(body);
                    body.instruction(&I::I64ExtendI32U);
                }
                Kind::Bool => {
                    body.instruction(&I::I64Const(4));
                    body.instruction(&I::I64Const(5));
                    emit_operand(body, function, param_count, operand, layout, frame)?;
                    body.instruction(&I::Select);
                }
                Kind::Char => {
                    body.instruction(&I::I32Const(1));
                    for bound in [0x80, 0x800, 0x10000] {
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        body.instruction(&I::I32Const(bound));
                        body.instruction(&I::I32GeU);
                        body.instruction(&I::I32Add);
                    }
                    body.instruction(&I::I64ExtendI32U);
                }
                Kind::Integer { signed, wide } => {
                    push_integer(
                        body,
                        function,
                        param_count,
                        operand,
                        layout,
                        frame,
                        signed,
                        wide,
                    )?;
                    body.instruction(&I::Call(int_len));
                    body.instruction(&I::I64ExtendI32U);
                }
                Kind::Float { wide } => {
                    push_float(body, function, param_count, operand, layout, frame, wide)?;
                    body.instruction(&I::Call(float_text));
                    body.instruction(&I::I64ExtendI32U);
                }
            },
        }
        body.instruction(&I::I64Add);
    }
    body.instruction(&I::LocalTee(scratch64));
    body.instruction(&I::I64Const(
        (super::memory::MAX_PAGES * super::memory::PAGE_BYTES) as i64,
    ));
    body.instruction(&I::I64GtU);
    trap_if(
        body,
        traps.site(instruction.span),
        TrapReason::HeapAllocation,
    );

    // One allocation. Nothing after it can fail.
    body.instruction(&I::LocalGet(scratch64));
    body.instruction(&I::I32WrapI64);
    body.instruction(&I::Call(reserve));
    body.instruction(&I::LocalTee(cursor));
    body.instruction(&I::I32Eqz);
    trap_if(
        body,
        traps.site(instruction.span),
        TrapReason::HeapAllocation,
    );
    emit_address(body, frame_state, cell.offset);
    body.instruction(&I::LocalGet(cursor));
    body.instruction(&I::I32Const(string_heap::HEADER_BYTES));
    body.instruction(&I::I32Add);
    string_descriptor::store_address(body);
    emit_address(body, frame_state, cell.offset);
    body.instruction(&I::LocalGet(scratch64));
    body.instruction(&I::I32WrapI64);
    string_descriptor::store_length(body);
    emit_address(body, frame_state, cell.offset);
    body.instruction(&I::LocalGet(cursor));
    string_descriptor::store_allocation(body);
    body.instruction(&I::LocalGet(cursor));
    body.instruction(&I::I32Const(string_heap::HEADER_BYTES));
    body.instruction(&I::I32Add);
    body.instruction(&I::LocalSet(cursor));

    // Pass 2: write the parts in order, advancing the cursor.
    let advance = |body: &mut WasmFunction| {
        body.instruction(&I::LocalGet(cursor));
        body.instruction(&I::I32Add);
        body.instruction(&I::LocalSet(cursor));
    };
    for part in parts {
        match part {
            InterpolationPart::Text(text) => {
                let descriptor = *strings
                    .get(text.as_str())
                    .ok_or("missing interpolation text data")?;
                body.instruction(&I::LocalGet(cursor));
                body.instruction(&I::I32Const((descriptor + string_descriptor::SIZE) as i32));
                body.instruction(&I::I32Const(text.len() as i32));
                body.instruction(&I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                body.instruction(&I::I32Const(text.len() as i32));
                advance(body);
            }
            InterpolationPart::Value(operand) => {
                match kind_of(&value_type(function, operand)?)? {
                    Kind::Text => {
                        body.instruction(&I::LocalGet(cursor));
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        string_descriptor::load_address(body);
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        string_descriptor::load_length(body);
                        body.instruction(&I::MemoryCopy {
                            src_mem: 0,
                            dst_mem: 0,
                        });
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        string_descriptor::load_length(body);
                        advance(body);
                    }
                    Kind::Bool => {
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        body.instruction(&I::If(BlockType::Empty));
                        body.instruction(&I::LocalGet(cursor));
                        body.instruction(&I::I32Const(i32::from_le_bytes(*b"true")));
                        body.instruction(&I::I32Store(byte_arg(0)));
                        body.instruction(&I::Else);
                        body.instruction(&I::LocalGet(cursor));
                        body.instruction(&I::I32Const(i32::from_le_bytes(*b"fals")));
                        body.instruction(&I::I32Store(byte_arg(0)));
                        body.instruction(&I::LocalGet(cursor));
                        body.instruction(&I::I32Const(i32::from(b'e')));
                        body.instruction(&I::I32Store8(byte_arg(4)));
                        body.instruction(&I::End);
                        // true = 4 bytes, false = 5 bytes.
                        body.instruction(&I::I32Const(4));
                        body.instruction(&I::I32Const(5));
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        body.instruction(&I::Select);
                        advance(body);
                    }
                    Kind::Char => {
                        body.instruction(&I::LocalGet(cursor));
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        body.instruction(&I::Call(char_write));
                        advance(body);
                    }
                    Kind::Integer { signed, wide } => {
                        body.instruction(&I::LocalGet(cursor));
                        push_integer(
                            body,
                            function,
                            param_count,
                            operand,
                            layout,
                            frame,
                            signed,
                            wide,
                        )?;
                        body.instruction(&I::Call(int_write));
                        advance(body);
                    }
                    Kind::Float { wide } => {
                        body.instruction(&I::LocalGet(cursor));
                        push_float(body, function, param_count, operand, layout, frame, wide)?;
                        // `float_write(destination, bits, is32)`.
                        body.instruction(&I::Call(float_write));
                        advance(body);
                    }
                }
            }
        }
    }
    Ok(())
}
