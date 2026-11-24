//! Shared integer semantics for static evaluation.
//!
//! Constant items (`memobits-resolve`) and the static-expression checks
//! (`memobits-analysis`) both evaluate integer operators and methods here, so
//! they cannot drift from each other. Values are carried as `i128`; every
//! function takes operands already in range for `kind` and matches the Rust
//! standard-library method of the same name.

use crate::{Expr, ExprKind};

/// Whether an expression is built only from untyped integer literals and
/// arithmetic, bitwise or shift operators. With no other type information such
/// a bitwise or shift expression defaults to `u32` (the hashing convention),
/// while arithmetic literals default to `i32`.
pub fn is_literal_tree(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Number(raw) => !raw.contains(['.', 'e', 'E']),
        ExprKind::Unary { operator, operand } => {
            matches!(operator.as_str(), "+" | "-" | "~") && is_literal_tree(operand)
        }
        ExprKind::Binary {
            operator,
            left,
            right,
        } => {
            matches!(
                operator.as_str(),
                "+" | "-" | "*" | "/" | "%" | "&" | "^" | "|" | "<<" | ">>"
            ) && is_literal_tree(left)
                && is_literal_tree(right)
        }
        _ => false,
    }
}

/// The width and signedness of one integer type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IntKind {
    pub bits: u32,
    pub signed: bool,
}

impl IntKind {
    pub fn from_name(name: &str) -> Option<Self> {
        let (signed, bits) = match name {
            "i8" => (true, 8),
            "i16" => (true, 16),
            "i32" => (true, 32),
            "i64" => (true, 64),
            "u8" => (false, 8),
            "u16" => (false, 16),
            "u32" => (false, 32),
            "u64" => (false, 64),
            _ => return None,
        };
        Some(Self { bits, signed })
    }

    /// The source spelling, such as `u32`.
    pub fn name(self) -> String {
        format!("{}{}", if self.signed { 'i' } else { 'u' }, self.bits)
    }

    pub fn min(self) -> i128 {
        if self.signed {
            -(1i128 << (self.bits - 1))
        } else {
            0
        }
    }

    pub fn max(self) -> i128 {
        if self.signed {
            (1i128 << (self.bits - 1)) - 1
        } else {
            (1i128 << self.bits) - 1
        }
    }

    pub fn contains(self, value: i128) -> bool {
        (self.min()..=self.max()).contains(&value)
    }

    /// Reduce any value modulo 2^bits into the type's range.
    pub fn wrap(self, value: i128) -> i128 {
        let modulus = 1i128 << self.bits;
        let reduced = value.rem_euclid(modulus);
        if self.signed && reduced > self.max() {
            reduced - modulus
        } else {
            reduced
        }
    }

    pub fn clamp(self, value: i128) -> i128 {
        value.clamp(self.min(), self.max())
    }
}

/// An arithmetic operation shared by the checked, wrapping and saturating
/// families.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

/// The exact (unbounded) result, or `None` for division by zero.
fn exact(op: Arith, left: i128, right: i128) -> Option<i128> {
    match op {
        Arith::Add => Some(left + right),
        Arith::Sub => Some(left - right),
        // A product beyond i128 is out of range for every width; keep its sign.
        Arith::Mul => Some(
            left.checked_mul(right)
                .unwrap_or(if (left < 0) == (right < 0) {
                    i128::MAX
                } else {
                    i128::MIN
                }),
        ),
        Arith::Div => (right != 0).then(|| left / right),
        Arith::Rem => (right != 0).then(|| left % right),
    }
}

/// `checked_*`: `None` on overflow or division by zero. `MIN / -1` overflows,
/// `MIN % -1` is `Some(0)`.
pub fn checked(kind: IntKind, op: Arith, left: i128, right: i128) -> Option<i128> {
    exact(op, left, right).filter(|value| kind.contains(*value))
}

/// `wrapping_add`, `wrapping_sub` and `wrapping_mul`.
pub fn wrapping(kind: IntKind, op: Arith, left: i128, right: i128) -> i128 {
    kind.wrap(match op {
        Arith::Mul => left.wrapping_mul(right),
        _ => exact(op, left, right).expect("wrapping add, sub and mul are total"),
    })
}

/// `saturating_add`, `saturating_sub` and `saturating_mul`.
pub fn saturating(kind: IntKind, op: Arith, left: i128, right: i128) -> i128 {
    kind.clamp(exact(op, left, right).expect("saturating add, sub and mul are total"))
}

/// `wrapping_neg` is `0 - value` at the operand width.
pub fn wrapping_neg(kind: IntKind, value: i128) -> i128 {
    kind.wrap(-value)
}

/// `checked_neg` is `0 - value` and fails on overflow.
pub fn checked_neg(kind: IntKind, value: i128) -> Option<i128> {
    Some(-value).filter(|result| kind.contains(*result))
}

/// `~value`: the bitwise complement at the operand width (`!value` in Rust).
pub fn complement(kind: IntKind, value: i128) -> i128 {
    kind.wrap(!value)
}

/// A bitwise operator on two in-range operands.
pub fn bitwise(operator: char, left: i128, right: i128) -> i128 {
    match operator {
        '&' => left & right,
        '|' => left | right,
        _ => left ^ right,
    }
}

/// `<<` or `>>` with a count below the width (`None` otherwise). `<<` discards
/// the bits shifted out; `>>` is arithmetic for signed types.
pub fn shift(kind: IntKind, left_shift: bool, value: i128, count: u128) -> Option<i128> {
    (count < u128::from(kind.bits)).then(|| shift_in_range(kind, left_shift, value, count as u32))
}

fn shift_in_range(kind: IntKind, left_shift: bool, value: i128, count: u32) -> i128 {
    if left_shift {
        kind.wrap(value << count)
    } else {
        value >> count
    }
}

/// `wrapping_shl` and `wrapping_shr`: the count is masked to the width.
pub fn wrapping_shift(kind: IntKind, left_shift: bool, value: i128, count: u128) -> i128 {
    shift_in_range(
        kind,
        left_shift,
        value,
        (count % u128::from(kind.bits)) as u32,
    )
}
