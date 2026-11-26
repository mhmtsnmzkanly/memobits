//! Wasm lowering for bitwise, shift, wrapping, saturating and checked integer
//! operations at every width.
//!
//! Narrow integers (8, 16 and 32 bits) live in `i32` locals, normalized: signed
//! values are sign-extended and unsigned values zero-extended. 64-bit integers
//! live in `i64` locals. Every result is normalized again for the source width.
use super::{
    emit_address, emit_store, scalar_option_offsets, trap_if, FrameLayout, FrameState, Site,
    TrapReason,
};
use memobits_ir::{BinaryOp, Function, Primitive, ValueId};
use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Arith {
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy)]
struct Kind {
    primitive: Primitive,
    bits: u32,
    signed: bool,
}

impl Kind {
    fn of(primitive: Primitive) -> Result<Self, String> {
        let (bits, signed) = match primitive {
            Primitive::I8 => (8, true),
            Primitive::I16 => (16, true),
            Primitive::I32 => (32, true),
            Primitive::I64 => (64, true),
            Primitive::U8 => (8, false),
            Primitive::U16 => (16, false),
            Primitive::U32 => (32, false),
            Primitive::U64 => (64, false),
            _ => return Err("integer operation requires an integer type".into()),
        };
        Ok(Self {
            primitive,
            bits,
            signed,
        })
    }

    fn wide(self) -> bool {
        self.bits == 64
    }

    fn min(self) -> i64 {
        if !self.signed {
            0
        } else if self.wide() {
            i64::MIN
        } else {
            -(1i64 << (self.bits - 1))
        }
    }

    /// The maximum as an `i64` bit pattern (all ones for `u64`).
    fn max(self) -> i64 {
        match (self.signed, self.bits) {
            (_, 64) if !self.signed => -1,
            (_, 64) => i64::MAX,
            (true, bits) => (1i64 << (bits - 1)) - 1,
            (false, bits) => (1i64 << bits) - 1,
        }
    }
}

/// Re-normalize an `i32` result of a narrow type after an operation that can
/// leave bits above the width (`u8`, `u16`, `i8`, `i16`).
fn normalize(body: &mut WasmFunction, kind: Kind) {
    if kind.bits == 8 || kind.bits == 16 {
        if kind.signed {
            let shift = 32 - kind.bits as i32;
            body.instruction(&I::I32Const(shift));
            body.instruction(&I::I32Shl);
            body.instruction(&I::I32Const(shift));
            body.instruction(&I::I32ShrS);
        } else {
            body.instruction(&I::I32Const(((1u32 << kind.bits) - 1) as i32));
            body.instruction(&I::I32And);
        }
    }
}

/// Push the bitwise complement of the integer in local `input`. Signed narrow
/// values stay sign-extended under `xor -1`; unsigned ones are masked.
pub(super) fn emit_complement(
    body: &mut WasmFunction,
    input: u32,
    primitive: Primitive,
) -> Result<(), String> {
    let kind = Kind::of(primitive)?;
    body.instruction(&I::LocalGet(input));
    if kind.wide() {
        body.instruction(&I::I64Const(-1));
        body.instruction(&I::I64Xor);
    } else {
        body.instruction(&I::I32Const(-1));
        body.instruction(&I::I32Xor);
        normalize(body, kind);
    }
    Ok(())
}

fn arith_of(op: BinaryOp) -> Option<Arith> {
    Some(match op {
        BinaryOp::WrappingAdd | BinaryOp::SaturatingAdd | BinaryOp::CheckedAdd => Arith::Add,
        BinaryOp::WrappingSubtract | BinaryOp::SaturatingSubtract | BinaryOp::CheckedSubtract => {
            Arith::Sub
        }
        BinaryOp::WrappingMultiply | BinaryOp::SaturatingMultiply | BinaryOp::CheckedMultiply => {
            Arith::Mul
        }
        _ => return None,
    })
}

/// Whether this module lowers the operation (every width).
pub(super) fn handles(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::WrappingAdd
            | BinaryOp::WrappingMultiply
            | BinaryOp::WrappingSubtract
            | BinaryOp::WrappingShiftLeft
            | BinaryOp::WrappingShiftRight
            | BinaryOp::SaturatingAdd
            | BinaryOp::SaturatingSubtract
            | BinaryOp::SaturatingMultiply
            | BinaryOp::BitwiseAnd
            | BinaryOp::BitwiseXor
            | BinaryOp::BitwiseOr
            | BinaryOp::ShiftLeft
            | BinaryOp::ShiftRight
    )
}

pub(super) fn is_checked(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::CheckedAdd
            | BinaryOp::CheckedSubtract
            | BinaryOp::CheckedMultiply
            | BinaryOp::CheckedDivide
            | BinaryOp::CheckedRemainder
            | BinaryOp::CheckedShiftLeft
            | BinaryOp::CheckedShiftRight
    )
}

/// Push the shifted value; `count` is a `u32` local. `strict` traps for a
/// count at or above the width, otherwise the count is masked.
fn emit_shift(
    body: &mut WasmFunction,
    left_shift: bool,
    kind: Kind,
    left: u32,
    count: u32,
    strict: Option<Site>,
    masked: bool,
) {
    if let Some(site) = strict {
        body.instruction(&I::LocalGet(count));
        body.instruction(&I::I32Const(kind.bits as i32));
        body.instruction(&I::I32GeU);
        trap_if(body, site, TrapReason::ShiftCount);
    }
    body.instruction(&I::LocalGet(left));
    body.instruction(&I::LocalGet(count));
    if masked {
        body.instruction(&I::I32Const(kind.bits as i32 - 1));
        body.instruction(&I::I32And);
    }
    if kind.wide() {
        body.instruction(&I::I64ExtendI32U);
        body.instruction(match (left_shift, kind.signed) {
            (true, _) => &I::I64Shl,
            (false, true) => &I::I64ShrS,
            (false, false) => &I::I64ShrU,
        });
    } else {
        body.instruction(match (left_shift, kind.signed) {
            (true, _) => &I::I32Shl,
            (false, true) => &I::I32ShrS,
            (false, false) => &I::I32ShrU,
        });
        if left_shift {
            normalize(body, kind);
        }
    }
}

/// Compute `left op right` into the i64 `scratch` (the exact result for narrow
/// types, the wrapped result for 64-bit types) and push an `i32` overflow flag.
fn emit_arith_flag(
    body: &mut WasmFunction,
    op: Arith,
    kind: Kind,
    left: u32,
    right: u32,
    scratch: u32,
) {
    let get = |body: &mut WasmFunction, local: u32| {
        body.instruction(&I::LocalGet(local));
    };
    if !kind.wide() {
        for local in [left, right] {
            get(body, local);
            body.instruction(if kind.signed {
                &I::I64ExtendI32S
            } else {
                &I::I64ExtendI32U
            });
        }
        body.instruction(match op {
            Arith::Add => &I::I64Add,
            Arith::Sub => &I::I64Sub,
            Arith::Mul => &I::I64Mul,
        });
        body.instruction(&I::LocalSet(scratch));
        if kind.signed {
            get(body, scratch);
            body.instruction(&I::I64Const(kind.min()));
            body.instruction(&I::I64LtS);
            get(body, scratch);
            body.instruction(&I::I64Const(kind.max()));
            body.instruction(&I::I64GtS);
            body.instruction(&I::I32Or);
        } else {
            get(body, scratch);
            body.instruction(&I::I64Const(kind.max()));
            body.instruction(&I::I64GtU);
        }
        return;
    }
    get(body, left);
    get(body, right);
    body.instruction(match op {
        Arith::Add => &I::I64Add,
        Arith::Sub => &I::I64Sub,
        Arith::Mul => &I::I64Mul,
    });
    body.instruction(&I::LocalSet(scratch));
    match (op, kind.signed) {
        (Arith::Add, true) => {
            // Overflow when both operands differ in sign from the result.
            for local in [left, right] {
                get(body, local);
                get(body, scratch);
                body.instruction(&I::I64Xor);
            }
            body.instruction(&I::I64And);
            body.instruction(&I::I64Const(0));
            body.instruction(&I::I64LtS);
        }
        (Arith::Add, false) => {
            get(body, scratch);
            get(body, left);
            body.instruction(&I::I64LtU);
        }
        (Arith::Sub, true) => {
            get(body, left);
            get(body, right);
            body.instruction(&I::I64Xor);
            get(body, left);
            get(body, scratch);
            body.instruction(&I::I64Xor);
            body.instruction(&I::I64And);
            body.instruction(&I::I64Const(0));
            body.instruction(&I::I64LtS);
        }
        (Arith::Sub, false) => {
            get(body, left);
            get(body, right);
            body.instruction(&I::I64LtU);
        }
        (Arith::Mul, signed) => {
            // The quotient check below can itself trap for MIN / -1, so that
            // pair (in either order) is reported as overflow first.
            let inner = |body: &mut WasmFunction| {
                get(body, left);
                body.instruction(&I::I64Eqz);
                body.instruction(&I::If(BlockType::Result(wasm_encoder::ValType::I32)));
                body.instruction(&I::I32Const(0));
                body.instruction(&I::Else);
                get(body, scratch);
                get(body, left);
                body.instruction(if signed { &I::I64DivS } else { &I::I64DivU });
                get(body, right);
                body.instruction(&I::I64Ne);
                body.instruction(&I::End);
            };
            if signed {
                for (index, (a, b)) in [(left, right), (right, left)].into_iter().enumerate() {
                    get(body, a);
                    body.instruction(&I::I64Const(i64::MIN));
                    body.instruction(&I::I64Eq);
                    get(body, b);
                    body.instruction(&I::I64Const(-1));
                    body.instruction(&I::I64Eq);
                    body.instruction(&I::I32And);
                    if index == 1 {
                        body.instruction(&I::I32Or);
                    }
                }
                body.instruction(&I::If(BlockType::Result(wasm_encoder::ValType::I32)));
                body.instruction(&I::I32Const(1));
                body.instruction(&I::Else);
                inner(body);
                body.instruction(&I::End);
            } else {
                inner(body);
            }
        }
    }
}

/// Push the result in `scratch` as the value of `kind` (wrap narrow types).
fn push_payload(body: &mut WasmFunction, kind: Kind, scratch: u32) {
    body.instruction(&I::LocalGet(scratch));
    if !kind.wide() {
        body.instruction(&I::I32WrapI64);
    }
}

/// Non-checked operations: the result is stored in `output`.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    primitive: Primitive,
    output: u32,
    scratch: u32,
    site: Site,
) -> Result<(), String> {
    let kind = Kind::of(primitive)?;
    match op {
        BinaryOp::BitwiseAnd | BinaryOp::BitwiseXor | BinaryOp::BitwiseOr => {
            body.instruction(&I::LocalGet(left));
            body.instruction(&I::LocalGet(right));
            body.instruction(match (op, kind.wide()) {
                (BinaryOp::BitwiseAnd, false) => &I::I32And,
                (BinaryOp::BitwiseXor, false) => &I::I32Xor,
                (BinaryOp::BitwiseOr, false) => &I::I32Or,
                (BinaryOp::BitwiseAnd, true) => &I::I64And,
                (BinaryOp::BitwiseXor, true) => &I::I64Xor,
                _ => &I::I64Or,
            });
        }
        BinaryOp::ShiftLeft | BinaryOp::ShiftRight => {
            emit_shift(
                body,
                op == BinaryOp::ShiftLeft,
                kind,
                left,
                right,
                Some(site),
                false,
            );
        }
        BinaryOp::WrappingShiftLeft | BinaryOp::WrappingShiftRight => {
            emit_shift(
                body,
                op == BinaryOp::WrappingShiftLeft,
                kind,
                left,
                right,
                None,
                true,
            );
        }
        BinaryOp::WrappingAdd | BinaryOp::WrappingSubtract | BinaryOp::WrappingMultiply => {
            let arith = arith_of(op).expect("wrapping arithmetic");
            body.instruction(&I::LocalGet(left));
            body.instruction(&I::LocalGet(right));
            body.instruction(match (arith, kind.wide()) {
                (Arith::Add, false) => &I::I32Add,
                (Arith::Sub, false) => &I::I32Sub,
                (Arith::Mul, false) => &I::I32Mul,
                (Arith::Add, true) => &I::I64Add,
                (Arith::Sub, true) => &I::I64Sub,
                (Arith::Mul, true) => &I::I64Mul,
            });
            normalize(body, kind);
        }
        BinaryOp::SaturatingAdd | BinaryOp::SaturatingSubtract | BinaryOp::SaturatingMultiply => {
            let arith = arith_of(op).expect("saturating arithmetic");
            emit_arith_flag(body, arith, kind, left, right, scratch);
            if kind.wide() {
                // Saturated value when the flag is set.
                body.instruction(&I::If(BlockType::Result(wasm_encoder::ValType::I64)));
                if !kind.signed {
                    body.instruction(&I::I64Const(if arith == Arith::Sub { 0 } else { -1 }));
                } else {
                    body.instruction(&I::I64Const(i64::MIN));
                    body.instruction(&I::I64Const(i64::MAX));
                    match arith {
                        Arith::Add => {
                            // Negative addend: underflow to MIN.
                            body.instruction(&I::LocalGet(right));
                        }
                        Arith::Sub => {
                            // Negative subtrahend: overflow to MAX, so pick MIN
                            // for the opposite condition.
                            body.instruction(&I::LocalGet(right));
                            body.instruction(&I::I64Const(0));
                            body.instruction(&I::I64GeS);
                        }
                        Arith::Mul => {
                            body.instruction(&I::LocalGet(left));
                            body.instruction(&I::LocalGet(right));
                            body.instruction(&I::I64Xor);
                        }
                    }
                    if arith != Arith::Sub {
                        body.instruction(&I::I64Const(0));
                        body.instruction(&I::I64LtS);
                    }
                    body.instruction(&I::Select);
                }
                body.instruction(&I::Else);
                body.instruction(&I::LocalGet(scratch));
                body.instruction(&I::End);
            } else {
                // The exact result is in `scratch`: clamp it.
                body.instruction(&I::Drop);
                if kind.signed {
                    for (limit, below) in [(kind.min(), true), (kind.max(), false)] {
                        body.instruction(&I::I64Const(limit));
                        body.instruction(&I::LocalGet(scratch));
                        body.instruction(&I::LocalGet(scratch));
                        body.instruction(&I::I64Const(limit));
                        body.instruction(if below { &I::I64LtS } else { &I::I64GtS });
                        body.instruction(&I::Select);
                        body.instruction(&I::LocalSet(scratch));
                    }
                } else {
                    // A negative exact result looks huge when compared unsigned.
                    body.instruction(&I::I64Const(if arith == Arith::Sub {
                        0
                    } else {
                        kind.max()
                    }));
                    body.instruction(&I::LocalGet(scratch));
                    body.instruction(&I::LocalGet(scratch));
                    body.instruction(&I::I64Const(kind.max()));
                    body.instruction(&I::I64GtU);
                    body.instruction(&I::Select);
                    body.instruction(&I::LocalSet(scratch));
                }
                body.instruction(&I::LocalGet(scratch));
                body.instruction(&I::I32WrapI64);
            }
        }
        _ => return Err("unsupported integer operation".into()),
    }
    body.instruction(&I::LocalSet(output));
    Ok(())
}

/// Checked operations: build the scalar option `T?` in the frame cell of the
/// output value. `flag_local` is an `i32` scratch (the output's own local).
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_checked(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    primitive: Primitive,
    flag_local: u32,
    scratch: u32,
    function: &Function,
    value: ValueId,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    let kind = Kind::of(primitive)?;
    let frame = frame.ok_or("checked integer operation requires a frame")?;
    let (tag, payload) = scalar_option_offsets(layout, function, value)?;
    match op {
        BinaryOp::CheckedAdd | BinaryOp::CheckedSubtract | BinaryOp::CheckedMultiply => {
            emit_arith_flag(
                body,
                arith_of(op).expect("checked arithmetic"),
                kind,
                left,
                right,
                scratch,
            );
            body.instruction(&I::LocalSet(flag_local));
        }
        BinaryOp::CheckedShiftLeft | BinaryOp::CheckedShiftRight => {
            body.instruction(&I::LocalGet(right));
            body.instruction(&I::I32Const(kind.bits as i32));
            body.instruction(&I::I32GeU);
            body.instruction(&I::LocalSet(flag_local));
            emit_shift(
                body,
                op == BinaryOp::CheckedShiftLeft,
                kind,
                left,
                right,
                None,
                true,
            );
            widen_into(body, kind, scratch);
        }
        BinaryOp::CheckedDivide | BinaryOp::CheckedRemainder => {
            let divide = op == BinaryOp::CheckedDivide;
            let (zero, minus_one, min_value) = if kind.wide() {
                (I::I64Const(0), I::I64Const(-1), I::I64Const(kind.min()))
            } else {
                (
                    I::I32Const(0),
                    I::I32Const(-1),
                    I::I32Const(kind.min() as i32),
                )
            };
            let eq = if kind.wide() { I::I64Eq } else { I::I32Eq };
            body.instruction(&I::LocalGet(right));
            body.instruction(&zero);
            body.instruction(&eq);
            if divide && kind.signed {
                body.instruction(&I::LocalGet(left));
                body.instruction(&min_value);
                body.instruction(&eq);
                body.instruction(&I::LocalGet(right));
                body.instruction(&minus_one);
                body.instruction(&eq);
                body.instruction(&I::I32And);
                body.instruction(&I::I32Or);
            }
            body.instruction(&I::LocalSet(flag_local));
            body.instruction(&I::LocalGet(flag_local));
            body.instruction(&I::I32Eqz);
            body.instruction(&I::If(BlockType::Empty));
            body.instruction(&I::LocalGet(left));
            body.instruction(&I::LocalGet(right));
            body.instruction(match (divide, kind.signed, kind.wide()) {
                (true, true, false) => &I::I32DivS,
                (true, false, false) => &I::I32DivU,
                (false, true, false) => &I::I32RemS,
                (false, false, false) => &I::I32RemU,
                (true, true, true) => &I::I64DivS,
                (true, false, true) => &I::I64DivU,
                (false, true, true) => &I::I64RemS,
                (false, false, true) => &I::I64RemU,
            });
            widen_top(body, kind);
            body.instruction(&I::LocalSet(scratch));
            body.instruction(&I::End);
        }
        _ => return Err("unsupported checked integer operation".into()),
    }
    // Some = 0 and None = 1, so the overflow flag is the tag.
    emit_address(body, frame, payload);
    push_payload(body, kind, scratch);
    emit_store(body, kind.primitive);
    emit_address(body, frame, tag);
    body.instruction(&I::LocalGet(flag_local));
    emit_store(body, Primitive::U8);
    Ok(())
}

/// Extend the `i32` on the stack to `i64` for narrow kinds.
fn widen_top(body: &mut WasmFunction, kind: Kind) {
    if !kind.wide() {
        body.instruction(if kind.signed {
            &I::I64ExtendI32S
        } else {
            &I::I64ExtendI32U
        });
    }
}

fn widen_into(body: &mut WasmFunction, kind: Kind, scratch: u32) {
    widen_top(body, kind);
    body.instruction(&I::LocalSet(scratch));
}
