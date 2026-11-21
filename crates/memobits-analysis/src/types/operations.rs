//! Primitive numeric categories used by operator and cast checking.
use super::Ty;

pub(super) fn numeric(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Primitive("i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "f32" | "f64")
    )
}

pub(super) fn integer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Primitive("i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64")
    )
}

pub(super) fn int_limit(kind: &str) -> Option<u128> {
    match kind {
        "i8" => Some(127),
        "i16" => Some(32767),
        "i32" => Some(2147483647),
        "i64" => Some(9223372036854775807),
        "u8" => Some(255),
        "u16" => Some(65535),
        "u32" => Some(4294967295),
        "u64" => Some(u64::MAX as u128),
        _ => None,
    }
}

pub(super) fn floating(ty: &Ty) -> bool {
    matches!(ty, Ty::Primitive("f32" | "f64"))
}
