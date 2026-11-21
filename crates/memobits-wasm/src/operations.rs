//! Wasm lowering for explicit numeric conversions.
use memobits_ir::Primitive;
use wasm_encoder::{Function, Instruction};

fn is_float(ty: Primitive) -> bool {
    matches!(ty, Primitive::F32 | Primitive::F64)
}

fn is_signed(ty: Primitive) -> bool {
    matches!(
        ty,
        Primitive::I8 | Primitive::I16 | Primitive::I32 | Primitive::I64
    )
}

fn width(ty: Primitive) -> u32 {
    match ty {
        Primitive::I8 | Primitive::U8 => 8,
        Primitive::I16 | Primitive::U16 => 16,
        Primitive::I32 | Primitive::U32 | Primitive::F32 => 32,
        Primitive::I64 | Primitive::U64 | Primitive::F64 => 64,
        _ => unreachable!("IR validation excludes non-numeric casts"),
    }
}

fn normalize_integer(body: &mut Function, ty: Primitive) {
    let bits = width(ty);
    if bits == 8 || bits == 16 {
        if is_signed(ty) {
            let shift = 32 - bits;
            body.instruction(&Instruction::I32Const(shift as i32));
            body.instruction(&Instruction::I32Shl);
            body.instruction(&Instruction::I32Const(shift as i32));
            body.instruction(&Instruction::I32ShrS);
        } else {
            body.instruction(&Instruction::I32Const(((1u32 << bits) - 1) as i32));
            body.instruction(&Instruction::I32And);
        }
    }
}

pub(super) fn emit_numeric_cast(
    body: &mut Function,
    source: Primitive,
    target: Primitive,
) -> Result<(), String> {
    let source_float = is_float(source);
    let target_float = is_float(target);
    let source_width = width(source);
    let target_width = width(target);

    if source_float && target_float {
        match (source, target) {
            (Primitive::F32, Primitive::F64) => {
                body.instruction(&Instruction::F64PromoteF32);
            }
            (Primitive::F64, Primitive::F32) => {
                body.instruction(&Instruction::F32DemoteF64);
            }
            _ => {}
        }
        return Ok(());
    }

    if source_float {
        if target_width < 32 {
            let bits = target_width as i32;
            let (min, max) = if is_signed(target) {
                (-(2f64).powi(bits - 1), (2f64).powi(bits - 1) - 1.0)
            } else {
                (0.0, (2f64).powi(bits) - 1.0)
            };
            match source {
                Primitive::F32 => {
                    body.instruction(&Instruction::F32Const((min as f32).into()));
                    body.instruction(&Instruction::F32Max);
                    body.instruction(&Instruction::F32Const((max as f32).into()));
                    body.instruction(&Instruction::F32Min);
                }
                Primitive::F64 => {
                    body.instruction(&Instruction::F64Const(min.into()));
                    body.instruction(&Instruction::F64Max);
                    body.instruction(&Instruction::F64Const(max.into()));
                    body.instruction(&Instruction::F64Min);
                }
                _ => unreachable!(),
            }
        }
        let target_lane = if target_width == 64 { 64 } else { 32 };
        let instruction = match (target_lane, source, is_signed(target)) {
            (32, Primitive::F32, true) => Instruction::I32TruncSatF32S,
            (32, Primitive::F32, false) => Instruction::I32TruncSatF32U,
            (32, Primitive::F64, true) => Instruction::I32TruncSatF64S,
            (32, Primitive::F64, false) => Instruction::I32TruncSatF64U,
            (64, Primitive::F32, true) => Instruction::I64TruncSatF32S,
            (64, Primitive::F32, false) => Instruction::I64TruncSatF32U,
            (64, Primitive::F64, true) => Instruction::I64TruncSatF64S,
            (64, Primitive::F64, false) => Instruction::I64TruncSatF64U,
            _ => return Err("invalid floating-point cast source".into()),
        };
        body.instruction(&instruction);
        normalize_integer(body, target);
        return Ok(());
    }

    if target_float {
        normalize_integer(body, source);
        let source_lane = if source_width == 64 { 64 } else { 32 };
        let instruction = match (target, source_lane, is_signed(source)) {
            (Primitive::F32, 32, true) => Instruction::F32ConvertI32S,
            (Primitive::F32, 32, false) => Instruction::F32ConvertI32U,
            (Primitive::F32, 64, true) => Instruction::F32ConvertI64S,
            (Primitive::F32, 64, false) => Instruction::F32ConvertI64U,
            (Primitive::F64, 32, true) => Instruction::F64ConvertI32S,
            (Primitive::F64, 32, false) => Instruction::F64ConvertI32U,
            (Primitive::F64, 64, true) => Instruction::F64ConvertI64S,
            (Primitive::F64, 64, false) => Instruction::F64ConvertI64U,
            _ => return Err("invalid integer cast source".into()),
        };
        body.instruction(&instruction);
        return Ok(());
    }

    if source_width == 64 && target_width < 64 {
        body.instruction(&Instruction::I32WrapI64);
    } else if source_width < 64 && target_width == 64 {
        normalize_integer(body, source);
        body.instruction(if is_signed(source) {
            &Instruction::I64ExtendI32S
        } else {
            &Instruction::I64ExtendI32U
        });
    }
    normalize_integer(body, target);
    Ok(())
}
