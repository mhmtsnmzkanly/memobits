//! Primitive method dispatch (Rust-core-inspired), with unsupported stubs.

use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;

use crate::value::{EvalResult, HeapObject, RuntimeError, Value};

pub fn call_primitive(name: &str, args: &[Value]) -> Option<EvalResult> {
    if args.is_empty() {
        return None;
    }
    match &args[0] {
        Value::Int(v) => Some(call_int(name, *v, &args[1..])),
        Value::UInt(v) => Some(call_uint(name, *v, &args[1..])),
        Value::Float(v) => Some(call_float(name, *v, &args[1..])),
        Value::Bool(v) => Some(call_bool(name, *v, &args[1..])),
        Value::Char(v) => Some(call_char(name, *v, &args[1..])),
        Value::HeapRef(h) => match h.as_ref() {
            HeapObject::String(s) => Some(call_string(name, s.as_str(), &args[1..])),
            _ => None,
        },
        _ => None,
    }
}

fn unsupported(name: &str, ty: &str) -> EvalResult {
    Err(RuntimeError(format!(
        "unsupported primitive method `{}` for {}",
        name, ty
    )))
}

fn expect_args_len(name: &str, got: usize, want: usize) -> EvalResult {
    if got == want {
        Ok(Value::Unit)
    } else {
        Err(RuntimeError(format!(
            "arity mismatch in `{}`: expected {}, got {}",
            name, want, got
        )))
    }
}

fn as_int(v: &Value) -> Option<i64> {
    match v {
        Value::Int(i) => Some(*i),
        _ => None,
    }
}

fn as_uint(v: &Value) -> Option<u64> {
    match v {
        Value::UInt(u) => Some(*u),
        _ => None,
    }
}

fn as_float(v: &Value) -> Option<f64> {
    match v {
        Value::Float(f) => Some(*f),
        _ => None,
    }
}

fn as_str(v: &Value) -> Option<&str> {
    match v {
        Value::HeapRef(h) => match h.as_ref() {
            HeapObject::String(s) => Some(s.as_str()),
            _ => None,
        },
        _ => None,
    }
}

fn tuple2(a: Value, b: Value) -> Value {
    Value::heap(HeapObject::Tuple {
        labels: vec![None, None],
        values: vec![a, b],
    })
}

fn call_int(name: &str, v: i64, args: &[Value]) -> EvalResult {
    match name {
        "to_int" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Int(v))
        }
        "to_uint" => {
            expect_args_len(name, args.len(), 0)?;
            if v < 0 {
                return Err(RuntimeError("cannot convert negative Int to UInt".into()));
            }
            Ok(Value::UInt(v as u64))
        }
        "abs" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Int(v.abs()))
        }
        "signum" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Int(v.signum()))
        }
        "is_positive" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Bool(v.is_positive()))
        }
        "is_negative" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Bool(v.is_negative()))
        }
        "is_zero" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Bool(v == 0))
        }
        "min" => {
            expect_args_len(name, args.len(), 1)?;
            let o = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
            Ok(Value::Int(v.min(o)))
        }
        "max" => {
            expect_args_len(name, args.len(), 1)?;
            let o = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
            Ok(Value::Int(v.max(o)))
        }
        "clamp" => {
            expect_args_len(name, args.len(), 2)?;
            let lo = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
            let hi = as_int(&args[1]).ok_or_else(|| RuntimeError("expected Int".into()))?;
            Ok(Value::Int(v.clamp(lo, hi)))
        }
        "pow" => {
            expect_args_len(name, args.len(), 1)?;
            let e = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
            if e < 0 {
                return Err(RuntimeError("pow exponent must be non-negative".into()));
            }
            Ok(Value::Int(v.pow(e as u32)))
        }
        "checked_add" => checked_i64(name, v, args, i64::checked_add),
        "checked_sub" => checked_i64(name, v, args, i64::checked_sub),
        "checked_mul" => checked_i64(name, v, args, i64::checked_mul),
        "checked_div" => checked_i64(name, v, args, i64::checked_div),
        "checked_rem" => checked_i64(name, v, args, i64::checked_rem),
        "saturating_add" => sat_i64(name, v, args, i64::saturating_add),
        "saturating_sub" => sat_i64(name, v, args, i64::saturating_sub),
        "saturating_mul" => sat_i64(name, v, args, i64::saturating_mul),
        "wrapping_add" => wrap_i64(name, v, args, i64::wrapping_add),
        "wrapping_sub" => wrap_i64(name, v, args, i64::wrapping_sub),
        "wrapping_mul" => wrap_i64(name, v, args, i64::wrapping_mul),
        "wrapping_div" => wrap_i64(name, v, args, i64::wrapping_div),
        "wrapping_rem" => wrap_i64(name, v, args, i64::wrapping_rem),
        "wrapping_shl" => wrap_shl_i64(name, v, args),
        "wrapping_shr" => wrap_shr_i64(name, v, args),
        "overflowing_add" => overflowing_i64(name, v, args, i64::overflowing_add),
        "overflowing_sub" => overflowing_i64(name, v, args, i64::overflowing_sub),
        "overflowing_mul" => overflowing_i64(name, v, args, i64::overflowing_mul),
        "overflowing_div" => overflowing_i64(name, v, args, i64::overflowing_div),
        "overflowing_rem" => overflowing_i64(name, v, args, i64::overflowing_rem),
        "overflowing_shl" => overflowing_shl_i64(name, v, args),
        "overflowing_shr" => overflowing_shr_i64(name, v, args),
        "count_ones" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.count_ones() as u64))
        }
        "count_zeros" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.count_zeros() as u64))
        }
        "leading_zeros" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.leading_zeros() as u64))
        }
        "trailing_zeros" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.trailing_zeros() as u64))
        }
        "leading_ones" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.leading_ones() as u64))
        }
        "trailing_ones" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.trailing_ones() as u64))
        }
        "rotate_left" => rotate_left_i64(name, v, args),
        "rotate_right" => rotate_right_i64(name, v, args),
        "reverse_bits" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Int(v.reverse_bits()))
        }
        "swap_bytes" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Int(v.swap_bytes()))
        }
        "to_be" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Int(v.to_be()))
        }
        "to_le" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Int(v.to_le()))
        }
        "to_string" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::string(v.to_string()))
        }
        _ => unsupported(name, "Int"),
    }
}

fn call_uint(name: &str, v: u64, args: &[Value]) -> EvalResult {
    match name {
        "to_int" => {
            expect_args_len(name, args.len(), 0)?;
            if v > i64::MAX as u64 {
                return Err(RuntimeError("UInt too large for Int".into()));
            }
            Ok(Value::Int(v as i64))
        }
        "to_uint" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v))
        }
        "is_zero" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Bool(v == 0))
        }
        "is_power_of_two" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::Bool(v.is_power_of_two()))
        }
        "next_power_of_two" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.next_power_of_two()))
        }
        "min" => {
            expect_args_len(name, args.len(), 1)?;
            let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
            Ok(Value::UInt(v.min(o)))
        }
        "max" => {
            expect_args_len(name, args.len(), 1)?;
            let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
            Ok(Value::UInt(v.max(o)))
        }
        "clamp" => {
            expect_args_len(name, args.len(), 2)?;
            let lo = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
            let hi = as_uint(&args[1]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
            Ok(Value::UInt(v.clamp(lo, hi)))
        }
        "pow" => {
            expect_args_len(name, args.len(), 1)?;
            let e = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
            Ok(Value::UInt(v.pow(e as u32)))
        }
        "checked_add" => checked_u64(name, v, args, u64::checked_add),
        "checked_sub" => checked_u64(name, v, args, u64::checked_sub),
        "checked_mul" => checked_u64(name, v, args, u64::checked_mul),
        "checked_div" => checked_u64(name, v, args, u64::checked_div),
        "checked_rem" => checked_u64(name, v, args, u64::checked_rem),
        "saturating_add" => sat_u64(name, v, args, u64::saturating_add),
        "saturating_sub" => sat_u64(name, v, args, u64::saturating_sub),
        "saturating_mul" => sat_u64(name, v, args, u64::saturating_mul),
        "wrapping_add" => wrap_u64(name, v, args, u64::wrapping_add),
        "wrapping_sub" => wrap_u64(name, v, args, u64::wrapping_sub),
        "wrapping_mul" => wrap_u64(name, v, args, u64::wrapping_mul),
        "wrapping_div" => wrap_u64(name, v, args, u64::wrapping_div),
        "wrapping_rem" => wrap_u64(name, v, args, u64::wrapping_rem),
        "wrapping_shl" => wrap_shl_u64(name, v, args),
        "wrapping_shr" => wrap_shr_u64(name, v, args),
        "overflowing_add" => overflowing_u64(name, v, args, u64::overflowing_add),
        "overflowing_sub" => overflowing_u64(name, v, args, u64::overflowing_sub),
        "overflowing_mul" => overflowing_u64(name, v, args, u64::overflowing_mul),
        "overflowing_div" => overflowing_u64(name, v, args, u64::overflowing_div),
        "overflowing_rem" => overflowing_u64(name, v, args, u64::overflowing_rem),
        "overflowing_shl" => overflowing_shl_u64(name, v, args),
        "overflowing_shr" => overflowing_shr_u64(name, v, args),
        "count_ones" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.count_ones() as u64))
        }
        "count_zeros" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.count_zeros() as u64))
        }
        "leading_zeros" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.leading_zeros() as u64))
        }
        "trailing_zeros" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.trailing_zeros() as u64))
        }
        "leading_ones" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.leading_ones() as u64))
        }
        "trailing_ones" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.trailing_ones() as u64))
        }
        "rotate_left" => rotate_left_u64(name, v, args),
        "rotate_right" => rotate_right_u64(name, v, args),
        "reverse_bits" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.reverse_bits()))
        }
        "swap_bytes" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.swap_bytes()))
        }
        "to_be" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.to_be()))
        }
        "to_le" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::UInt(v.to_le()))
        }
        "to_string" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::string(v.to_string()))
        }
        _ => unsupported(name, "UInt"),
    }
}

fn call_float(name: &str, v: f64, args: &[Value]) -> EvalResult {
    match name {
        "to_int" => {
            expect_args_len(name, args.len(), 0)?;
            if !v.is_finite() {
                return Err(RuntimeError("cannot convert non-finite Float to Int".into()));
            }
            let t = v.trunc();
            if t < i64::MIN as f64 || t > i64::MAX as f64 {
                return Err(RuntimeError("Float out of Int range".into()));
            }
            Ok(Value::Int(t as i64))
        }
        "to_uint" => {
            expect_args_len(name, args.len(), 0)?;
            if !v.is_finite() {
                return Err(RuntimeError("cannot convert non-finite Float to UInt".into()));
            }
            let t = v.trunc();
            if t < 0.0 || t > u64::MAX as f64 {
                return Err(RuntimeError("Float out of UInt range".into()));
            }
            Ok(Value::UInt(t as u64))
        }
        "abs" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.abs())) }
        "signum" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.signum())) }
        "is_nan" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_nan())) }
        "is_infinite" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_infinite())) }
        "is_finite" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_finite())) }
        "is_normal" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_normal())) }
        "is_sign_positive" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_sign_positive())) }
        "is_sign_negative" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_sign_negative())) }
        "floor" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.floor())) }
        "ceil" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.ceil())) }
        "round" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.round())) }
        "trunc" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.trunc())) }
        "fract" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.fract())) }
        "sqrt" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.sqrt())) }
        "cbrt" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.cbrt())) }
        "powf" => {
            expect_args_len(name, args.len(), 1)?;
            let e = as_float(&args[0]).ok_or_else(|| RuntimeError("expected Float".into()))?;
            Ok(Value::Float(v.powf(e)))
        }
        "powi" => {
            expect_args_len(name, args.len(), 1)?;
            let e = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
            Ok(Value::Float(v.powi(e as i32)))
        }
        "exp" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.exp())) }
        "exp2" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.exp2())) }
        "ln" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.ln())) }
        "log" => {
            expect_args_len(name, args.len(), 1)?;
            let base = as_float(&args[0]).ok_or_else(|| RuntimeError("expected Float".into()))?;
            Ok(Value::Float(v.log(base)))
        }
        "log2" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.log2())) }
        "log10" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.log10())) }
        "sin" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.sin())) }
        "cos" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.cos())) }
        "tan" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.tan())) }
        "asin" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.asin())) }
        "acos" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.acos())) }
        "atan" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.atan())) }
        "atan2" => {
            expect_args_len(name, args.len(), 1)?;
            let o = as_float(&args[0]).ok_or_else(|| RuntimeError("expected Float".into()))?;
            Ok(Value::Float(v.atan2(o)))
        }
        "min" => {
            expect_args_len(name, args.len(), 1)?;
            let o = as_float(&args[0]).ok_or_else(|| RuntimeError("expected Float".into()))?;
            Ok(Value::Float(v.min(o)))
        }
        "max" => {
            expect_args_len(name, args.len(), 1)?;
            let o = as_float(&args[0]).ok_or_else(|| RuntimeError("expected Float".into()))?;
            Ok(Value::Float(v.max(o)))
        }
        "clamp" => {
            expect_args_len(name, args.len(), 2)?;
            let lo = as_float(&args[0]).ok_or_else(|| RuntimeError("expected Float".into()))?;
            let hi = as_float(&args[1]).ok_or_else(|| RuntimeError("expected Float".into()))?;
            Ok(Value::Float(v.clamp(lo, hi)))
        }
        "to_degrees" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.to_degrees())) }
        "to_radians" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Float(v.to_radians())) }
        "to_string" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(v.to_string())) }
        _ => unsupported(name, "Float"),
    }
}

fn call_bool(name: &str, v: bool, args: &[Value]) -> EvalResult {
    match name {
        "to_int" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Int(if v { 1 } else { 0 })) }
        "to_uint" => { expect_args_len(name, args.len(), 0)?; Ok(Value::UInt(if v { 1 } else { 0 })) }
        "not" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(!v)) }
        "to_string" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(v.to_string())) }
        _ => unsupported(name, "Bool"),
    }
}

fn call_char(name: &str, v: char, args: &[Value]) -> EvalResult {
    match name {
        "to_int" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Int(v as u32 as i64)) }
        "to_uint" => { expect_args_len(name, args.len(), 0)?; Ok(Value::UInt(v as u32 as u64)) }
        "to_string" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(v.to_string())) }
        "is_alphabetic" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_alphabetic())) }
        "is_numeric" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_numeric())) }
        "is_alphanumeric" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_alphanumeric())) }
        "is_whitespace" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_whitespace())) }
        "is_uppercase" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_uppercase())) }
        "is_lowercase" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(v.is_lowercase())) }
        "is_digit" => {
            expect_args_len(name, args.len(), 1)?;
            let radix = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
            Ok(Value::Bool(v.is_digit(radix as u32)))
        }
        "to_uppercase" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::string(v.to_uppercase().to_string()))
        }
        "to_lowercase" => {
            expect_args_len(name, args.len(), 0)?;
            Ok(Value::string(v.to_lowercase().to_string()))
        }
        _ => unsupported(name, "Char"),
    }
}

fn call_string(name: &str, s: &str, args: &[Value]) -> EvalResult {
    match name {
        "len" => { expect_args_len(name, args.len(), 0)?; Ok(Value::UInt(s.len() as u64)) }
        "is_empty" => { expect_args_len(name, args.len(), 0)?; Ok(Value::Bool(s.is_empty())) }
        "contains" => {
            expect_args_len(name, args.len(), 1)?;
            let sub = as_str(&args[0]).ok_or_else(|| RuntimeError("expected String".into()))?;
            Ok(Value::Bool(s.contains(sub)))
        }
        "starts_with" => {
            expect_args_len(name, args.len(), 1)?;
            let sub = as_str(&args[0]).ok_or_else(|| RuntimeError("expected String".into()))?;
            Ok(Value::Bool(s.starts_with(sub)))
        }
        "ends_with" => {
            expect_args_len(name, args.len(), 1)?;
            let sub = as_str(&args[0]).ok_or_else(|| RuntimeError("expected String".into()))?;
            Ok(Value::Bool(s.ends_with(sub)))
        }
        "trim" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(s.trim().to_string())) }
        "trim_start" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(s.trim_start().to_string())) }
        "trim_end" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(s.trim_end().to_string())) }
        "to_uppercase" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(s.to_uppercase())) }
        "to_lowercase" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(s.to_lowercase())) }
        "replace" => {
            expect_args_len(name, args.len(), 2)?;
            let from = as_str(&args[0]).ok_or_else(|| RuntimeError("expected String".into()))?;
            let to = as_str(&args[1]).ok_or_else(|| RuntimeError("expected String".into()))?;
            Ok(Value::string(s.replace(from, to)))
        }
        "split" => {
            expect_args_len(name, args.len(), 1)?;
            let sep = as_str(&args[0]).ok_or_else(|| RuntimeError("expected String".into()))?;
            let parts: Vec<Value> = s.split(sep).map(|p| Value::string(p.to_string())).collect();
            Ok(Value::heap(HeapObject::List(core::cell::RefCell::new(parts))))
        }
        "chars" => {
            expect_args_len(name, args.len(), 0)?;
            let parts: Vec<Value> = s.chars().map(Value::Char).collect();
            Ok(Value::heap(HeapObject::List(core::cell::RefCell::new(parts))))
        }
        "repeat" => {
            expect_args_len(name, args.len(), 1)?;
            let n = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
            Ok(Value::string(s.repeat(n as usize)))
        }
        "slice" => {
            expect_args_len(name, args.len(), 2)?;
            let start = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))? as usize;
            let len = as_uint(&args[1]).ok_or_else(|| RuntimeError("expected UInt".into()))? as usize;
            let chars: Vec<char> = s.chars().collect();
            if start > chars.len() || start + len > chars.len() {
                return Err(RuntimeError("string slice out of bounds".into()));
            }
            let out: String = chars[start..start + len].iter().collect();
            Ok(Value::string(out))
        }
        "to_string" => { expect_args_len(name, args.len(), 0)?; Ok(Value::string(s.to_string())) }
        _ => unsupported(name, "String"),
    }
}

fn checked_i64(
    name: &str,
    v: i64,
    args: &[Value],
    f: fn(i64, i64) -> Option<i64>,
) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
    Ok(match f(v, o) {
        Some(r) => Value::heap(HeapObject::Enum {
            type_id: "Option".into(),
            variant_id: 1,
            payload: vec![Value::Int(r)],
        }),
        None => Value::heap(HeapObject::Enum {
            type_id: "Option".into(),
            variant_id: 0,
            payload: Vec::new(),
        }),
    })
}

fn checked_u64(
    name: &str,
    v: u64,
    args: &[Value],
    f: fn(u64, u64) -> Option<u64>,
) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(match f(v, o) {
        Some(r) => Value::heap(HeapObject::Enum {
            type_id: "Option".into(),
            variant_id: 1,
            payload: vec![Value::UInt(r)],
        }),
        None => Value::heap(HeapObject::Enum {
            type_id: "Option".into(),
            variant_id: 0,
            payload: Vec::new(),
        }),
    })
}

fn sat_i64(name: &str, v: i64, args: &[Value], f: fn(i64, i64) -> i64) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
    Ok(Value::Int(f(v, o)))
}

fn sat_u64(name: &str, v: u64, args: &[Value], f: fn(u64, u64) -> u64) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::UInt(f(v, o)))
}

fn wrap_i64(name: &str, v: i64, args: &[Value], f: fn(i64, i64) -> i64) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
    Ok(Value::Int(f(v, o)))
}

fn wrap_u64(name: &str, v: u64, args: &[Value], f: fn(u64, u64) -> u64) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::UInt(f(v, o)))
}

fn overflowing_i64(
    name: &str,
    v: i64,
    args: &[Value],
    f: fn(i64, i64) -> (i64, bool),
) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_int(&args[0]).ok_or_else(|| RuntimeError("expected Int".into()))?;
    let (r, of) = f(v, o);
    Ok(tuple2(Value::Int(r), Value::Bool(of)))
}

fn overflowing_u64(
    name: &str,
    v: u64,
    args: &[Value],
    f: fn(u64, u64) -> (u64, bool),
) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    let (r, of) = f(v, o);
    Ok(tuple2(Value::UInt(r), Value::Bool(of)))
}

fn wrap_shl_i64(name: &str, v: i64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::Int(v.wrapping_shl(o as u32)))
}

fn wrap_shr_i64(name: &str, v: i64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::Int(v.wrapping_shr(o as u32)))
}

fn wrap_shl_u64(name: &str, v: u64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::UInt(v.wrapping_shl(o as u32)))
}

fn wrap_shr_u64(name: &str, v: u64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::UInt(v.wrapping_shr(o as u32)))
}

fn overflowing_shl_i64(name: &str, v: i64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    let (r, of) = v.overflowing_shl(o as u32);
    Ok(tuple2(Value::Int(r), Value::Bool(of)))
}

fn overflowing_shr_i64(name: &str, v: i64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    let (r, of) = v.overflowing_shr(o as u32);
    Ok(tuple2(Value::Int(r), Value::Bool(of)))
}

fn overflowing_shl_u64(name: &str, v: u64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    let (r, of) = v.overflowing_shl(o as u32);
    Ok(tuple2(Value::UInt(r), Value::Bool(of)))
}

fn overflowing_shr_u64(name: &str, v: u64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    let (r, of) = v.overflowing_shr(o as u32);
    Ok(tuple2(Value::UInt(r), Value::Bool(of)))
}

fn rotate_left_i64(name: &str, v: i64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::Int(v.rotate_left(o as u32)))
}

fn rotate_right_i64(name: &str, v: i64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::Int(v.rotate_right(o as u32)))
}

fn rotate_left_u64(name: &str, v: u64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::UInt(v.rotate_left(o as u32)))
}

fn rotate_right_u64(name: &str, v: u64, args: &[Value]) -> EvalResult {
    expect_args_len(name, args.len(), 1)?;
    let o = as_uint(&args[0]).ok_or_else(|| RuntimeError("expected UInt".into()))?;
    Ok(Value::UInt(v.rotate_right(o as u32)))
}
