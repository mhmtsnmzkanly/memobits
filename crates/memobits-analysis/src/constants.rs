//! Static checks for integer operations whose operands are numeric literals.
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity};
use memobits_ir::{Primitive, Type};
use memobits_syntax::numeric::{self, Arith, IntKind};
use memobits_syntax::{Block, Expr, ExprKind, ItemKind, Module, StatementKind};
use std::collections::HashMap;

use crate::types::FunctionFacts;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Value {
    Integer(i128),
    Float(f64),
    Overflow,
    DivisionByZero,
    ShiftCountOutOfRange(IntKind),
    Unknown,
}

fn integer_type(ty: &Type) -> Option<(i128, i128)> {
    let Type::Primitive(primitive) = ty else {
        return None;
    };
    Some(match primitive {
        Primitive::I8 => (i8::MIN as i128, i8::MAX as i128),
        Primitive::I16 => (i16::MIN as i128, i16::MAX as i128),
        Primitive::I32 => (i32::MIN as i128, i32::MAX as i128),
        Primitive::I64 => (i64::MIN as i128, i64::MAX as i128),
        Primitive::U8 => (0, u8::MAX as i128),
        Primitive::U16 => (0, u16::MAX as i128),
        Primitive::U32 => (0, u32::MAX as i128),
        Primitive::U64 => (0, u64::MAX as i128),
        _ => return None,
    })
}

pub(crate) fn int_kind(ty: &Type) -> Option<IntKind> {
    let Type::Primitive(primitive) = ty else {
        return None;
    };
    IntKind::from_name(match primitive {
        Primitive::I8 => "i8",
        Primitive::I16 => "i16",
        Primitive::I32 => "i32",
        Primitive::I64 => "i64",
        Primitive::U8 => "u8",
        Primitive::U16 => "u16",
        Primitive::U32 => "u32",
        Primitive::U64 => "u64",
        _ => return None,
    })
}

fn evaluate(expr: &Expr, types: &HashMap<usize, Option<Type>>) -> Value {
    match &expr.kind {
        ExprKind::Number(raw) if !raw.contains(['.', 'e', 'E']) => raw
            .replace('_', "")
            .parse::<i128>()
            .map(Value::Integer)
            .unwrap_or(Value::Unknown),
        ExprKind::TypedNumber { raw, .. } if !raw.contains(['.', 'e', 'E', 'N', 'i']) => raw
            .parse::<i128>()
            .map(Value::Integer)
            .unwrap_or(Value::Unknown),
        ExprKind::TypedNumber { raw, .. } => raw
            .parse::<f64>()
            .map(Value::Float)
            .unwrap_or(Value::Unknown),
        ExprKind::CharLiteral(_) => Value::Unknown,
        ExprKind::Number(raw) => raw
            .replace('_', "")
            .parse::<f64>()
            .map(Value::Float)
            .unwrap_or(Value::Unknown),
        ExprKind::Unary { operator, operand } if operator == "+" || operator == "-" => {
            let Some(ty) = types
                .get(&(expr as *const Expr as usize))
                .and_then(Option::as_ref)
            else {
                return Value::Unknown;
            };
            let evaluated = evaluate(operand, types);
            if matches!(ty, Type::Primitive(Primitive::F32 | Primitive::F64)) {
                return match evaluated {
                    Value::Float(value) => {
                        Value::Float(if operator == "-" { -value } else { value })
                    }
                    Value::Integer(value) => Value::Float(if operator == "-" {
                        -(value as f64)
                    } else {
                        value as f64
                    }),
                    _ => Value::Unknown,
                };
            }
            let Some((min, max)) = integer_type(ty) else {
                return Value::Unknown;
            };
            let Value::Integer(value) = evaluated else {
                return Value::Unknown;
            };
            let value = if operator == "-" {
                let Some(value) = value.checked_neg() else {
                    return Value::Overflow;
                };
                value
            } else {
                value
            };
            if !(min..=max).contains(&value) {
                Value::Overflow
            } else {
                Value::Integer(value)
            }
        }
        ExprKind::Unary { operator, operand } if operator == "~" => {
            let Some(kind) = types
                .get(&(expr as *const Expr as usize))
                .and_then(Option::as_ref)
                .and_then(int_kind)
            else {
                return Value::Unknown;
            };
            match evaluate(operand, types) {
                Value::Integer(value) if kind.contains(value) => {
                    Value::Integer(numeric::complement(kind, value))
                }
                _ => Value::Unknown,
            }
        }
        ExprKind::Cast {
            value: source_expr,
            target,
        } => {
            let integer_cast = |value: i128, name: &str| -> Option<i128> {
                let (bits, signed) = match name {
                    "i8" => (8, true),
                    "i16" => (16, true),
                    "i32" => (32, true),
                    "i64" => (64, true),
                    "u8" => (8, false),
                    "u16" => (16, false),
                    "u32" => (32, false),
                    "u64" => (64, false),
                    _ => return None,
                };
                let mask = if bits == 64 {
                    u64::MAX as u128
                } else {
                    (1u128 << bits) - 1
                };
                let wrapped = (value as u128) & mask;
                if signed && wrapped & (1u128 << (bits - 1)) != 0 {
                    Some((wrapped as i128) - (1i128 << bits))
                } else {
                    Some(wrapped as i128)
                }
            };
            let Some(target_name) = target.path.last().map(String::as_str) else {
                return Value::Unknown;
            };
            match evaluate(source_expr, types) {
                Value::Integer(value) => {
                    if matches!(target_name, "f32" | "f64") {
                        let number = match types
                            .get(&(source_expr.as_ref() as *const Expr as usize))
                            .and_then(Option::as_ref)
                        {
                            Some(Type::Primitive(Primitive::I8)) => (value as i8) as f64,
                            Some(Type::Primitive(Primitive::I16)) => (value as i16) as f64,
                            Some(Type::Primitive(Primitive::I32)) => (value as i32) as f64,
                            Some(Type::Primitive(Primitive::I64)) => (value as i64) as f64,
                            Some(Type::Primitive(Primitive::U8)) => (value as u8) as f64,
                            Some(Type::Primitive(Primitive::U16)) => (value as u16) as f64,
                            Some(Type::Primitive(Primitive::U32)) => (value as u32) as f64,
                            Some(Type::Primitive(Primitive::U64)) => (value as u64) as f64,
                            _ => value as f64,
                        };
                        if target_name == "f32" {
                            Value::Float((number as f32) as f64)
                        } else {
                            Value::Float(number)
                        }
                    } else {
                        integer_cast(value, target_name)
                            .map(Value::Integer)
                            .unwrap_or(Value::Unknown)
                    }
                }
                Value::Float(value) => match target_name {
                    "f32" => Value::Float((value as f32) as f64),
                    "f64" => Value::Float(value),
                    "i8" => Value::Integer(value as i8 as i128),
                    "i16" => Value::Integer(value as i16 as i128),
                    "i32" => Value::Integer(value as i32 as i128),
                    "i64" => Value::Integer(value as i64 as i128),
                    "u8" => Value::Integer(value as u8 as i128),
                    "u16" => Value::Integer(value as u16 as i128),
                    "u32" => Value::Integer(value as u32 as i128),
                    "u64" => Value::Integer(value as u64 as i128),
                    _ => Value::Unknown,
                },
                _ => Value::Unknown,
            }
        }
        ExprKind::Call {
            callee, arguments, ..
        } => {
            let ExprKind::Field { base, name } = &callee.kind else {
                return Value::Unknown;
            };
            let Some(kind) = types
                .get(&(expr as *const Expr as usize))
                .and_then(Option::as_ref)
                .and_then(int_kind)
            else {
                // `checked_*` results are options; they never fold.
                return Value::Unknown;
            };
            let name = name.as_str();
            let arity = usize::from(!matches!(name, "wrapping_neg"));
            if arguments.len() != arity {
                return Value::Unknown;
            }
            let Value::Integer(left) = evaluate(base, types) else {
                return Value::Unknown;
            };
            if name == "wrapping_neg" {
                return Value::Integer(numeric::wrapping_neg(kind, left));
            }
            let Value::Integer(right) = evaluate(&arguments[0], types) else {
                return Value::Unknown;
            };
            let arith = |name: &str| match name.rsplit('_').next() {
                Some("add") => Some(Arith::Add),
                Some("sub") => Some(Arith::Sub),
                Some("mul") => Some(Arith::Mul),
                _ => None,
            };
            Value::Integer(match name {
                "wrapping_add" | "wrapping_sub" | "wrapping_mul" => {
                    numeric::wrapping(kind, arith(name).expect("arith"), left, right)
                }
                "saturating_add" | "saturating_sub" | "saturating_mul" => {
                    numeric::saturating(kind, arith(name).expect("arith"), left, right)
                }
                "wrapping_shl" | "wrapping_shr" => {
                    numeric::wrapping_shift(kind, name == "wrapping_shl", left, right as u128)
                }
                "bit_and" => numeric::bitwise('&', left, right),
                "bit_xor" => numeric::bitwise('^', left, right),
                "bit_or" => numeric::bitwise('|', left, right),
                _ => return Value::Unknown,
            })
        }
        ExprKind::Binary {
            operator,
            left,
            right,
        } if matches!(
            operator.as_str(),
            "+" | "-" | "*" | "/" | "%" | "&" | "^" | "|" | "<<" | ">>"
        ) =>
        {
            let Some(kind) = types
                .get(&(expr as *const Expr as usize))
                .and_then(Option::as_ref)
                .and_then(int_kind)
            else {
                return Value::Unknown;
            };
            // A zero divisor is invalid even when the numerator is dynamic.
            if matches!(operator.as_str(), "/" | "%") && evaluate(right, types) == Value::Integer(0)
            {
                return Value::DivisionByZero;
            }
            let shifting = matches!(operator.as_str(), "<<" | ">>");
            if shifting {
                if let Value::Integer(count) = evaluate(right, types) {
                    if !(0..i128::from(kind.bits)).contains(&count) {
                        return Value::ShiftCountOutOfRange(kind);
                    }
                }
            }
            let (Value::Integer(left), Value::Integer(right)) =
                (evaluate(left, types), evaluate(right, types))
            else {
                return Value::Unknown;
            };
            let result = match operator.as_str() {
                "+" => numeric::checked(kind, Arith::Add, left, right),
                "-" => numeric::checked(kind, Arith::Sub, left, right),
                "*" => numeric::checked(kind, Arith::Mul, left, right),
                "/" if right == 0 => return Value::DivisionByZero,
                "%" if right == 0 => return Value::DivisionByZero,
                "/" => numeric::checked(kind, Arith::Div, left, right),
                "%" => numeric::checked(kind, Arith::Rem, left, right),
                "<<" | ">>" => numeric::shift(kind, operator == "<<", left, right as u128),
                op => Some(numeric::bitwise(
                    op.chars().next().expect("operator"),
                    left,
                    right,
                )),
            };
            match result {
                Some(result) if kind.contains(result) => Value::Integer(result),
                _ => Value::Overflow,
            }
        }
        _ => Value::Unknown,
    }
}

fn check_expr(
    expr: &Expr,
    types: &HashMap<usize, Option<Type>>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match &expr.kind {
        ExprKind::Number(_)
        | ExprKind::TypedNumber { .. }
        | ExprKind::StringLiteral(_)
        | ExprKind::CharLiteral(_)
        | ExprKind::Bool(_)
        | ExprKind::Path(_)
        | ExprKind::Interpolation(_) => {}
        ExprKind::Array(elements) => {
            for element in elements {
                check_expr(element, types, diagnostics);
            }
        }
        ExprKind::Tuple(elements) => {
            for element in elements {
                check_expr(&element.value, types, diagnostics);
            }
        }
        ExprKind::RepeatArray { value, .. } => check_expr(value, types, diagnostics),
        ExprKind::Index { base, index } => {
            check_expr(base, types, diagnostics);
            check_expr(index, types, diagnostics);
        }
        ExprKind::Unary { operand, .. } => check_expr(operand, types, diagnostics),
        ExprKind::Cast { value, .. } => check_expr(value, types, diagnostics),
        ExprKind::Binary { left, right, .. } => {
            check_expr(left, types, diagnostics);
            check_expr(right, types, diagnostics);
        }
        ExprKind::Call {
            callee, arguments, ..
        } => {
            check_expr(callee, types, diagnostics);
            for argument in arguments {
                check_expr(argument, types, diagnostics);
            }
        }
        ExprKind::Field { base, .. } => check_expr(base, types, diagnostics),
        ExprKind::Struct { fields, .. } => {
            for field in fields {
                check_expr(&field.value, types, diagnostics);
            }
        }
        ExprKind::Block(block) => check_block(block, types, diagnostics),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            check_expr(condition, types, diagnostics);
            check_block(then_branch, types, diagnostics);
            if let Some(other) = else_branch {
                check_expr(other, types, diagnostics);
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            check_expr(scrutinee, types, diagnostics);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    check_expr(guard, types, diagnostics);
                }
                check_expr(&arm.body, types, diagnostics);
            }
        }
    }
    match evaluate(expr, types) {
        Value::Overflow => diagnostics.push(diagnostic(
            1,
            expr.span,
            "integer overflow in statically known expression",
        )),
        Value::DivisionByZero => diagnostics.push(diagnostic(
            2,
            expr.span,
            "division or remainder by zero in statically known expression",
        )),
        Value::ShiftCountOutOfRange(kind) => {
            diagnostics.push(diagnostic(3, expr.span, &shift_message(kind)))
        }
        Value::Integer(_) | Value::Float(_) | Value::Unknown => {}
    }
}

fn check_block(
    block: &Block,
    types: &HashMap<usize, Option<Type>>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Binding { value, .. }
            | StatementKind::Destructure { value, .. }
            | StatementKind::TupleDestructure { value, .. }
            | StatementKind::Expression(value) => check_expr(value, types, diagnostics),
            StatementKind::Assign { target, value, .. } => {
                check_expr(target, types, diagnostics);
                check_expr(value, types, diagnostics);
            }
            StatementKind::Return(Some(value)) => check_expr(value, types, diagnostics),
            StatementKind::Return(None) | StatementKind::Break | StatementKind::Continue => {}
            StatementKind::Loop(body) => check_block(body, types, diagnostics),
            StatementKind::ForEach { items, body, .. } => {
                check_expr(items, types, diagnostics);
                check_block(body, types, diagnostics);
            }
            StatementKind::RangeLoop {
                start, end, body, ..
            } => {
                check_expr(start, types, diagnostics);
                check_expr(end, types, diagnostics);
                check_block(body, types, diagnostics);
            }
        }
    }
    if let Some(tail) = &block.tail {
        check_expr(tail, types, diagnostics);
    }
}

fn diagnostic(number: u16, span: memobits_diagnostics::Span, message: &str) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(
        DiagnosticCode::new(Category::StaticOperation, number).expect("static LE code"),
        Severity::Error,
        message,
    );
    diagnostic.span = Some(span);
    diagnostic
}

fn shift_message(kind: IntKind) -> String {
    format!(
        "{} shift count must be less than {}",
        kind.name(),
        kind.bits
    )
}

pub(crate) fn shift_assignment_count_error(
    span: memobits_diagnostics::Span,
    kind: IntKind,
) -> Diagnostic {
    diagnostic(3, span, &shift_message(kind))
}

pub(crate) fn shift_assignment_count_out_of_range(expr: &Expr, bits: u32) -> bool {
    fn integer(expr: &Expr) -> Option<i128> {
        match &expr.kind {
            ExprKind::Number(raw)
                if raw
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || byte == b'_') =>
            {
                raw.replace('_', "").parse().ok()
            }
            ExprKind::TypedNumber { raw, ty } if !ty.path.iter().any(|p| p.starts_with('f')) => {
                raw.parse().ok()
            }
            ExprKind::Unary { operator, operand } if operator == "+" || operator == "-" => {
                let value = integer(operand)?;
                if operator == "-" {
                    value.checked_neg()
                } else {
                    Some(value)
                }
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                let left = integer(left)?;
                let right = integer(right)?;
                match operator.as_str() {
                    "+" => left.checked_add(right),
                    "-" => left.checked_sub(right),
                    "*" => left.checked_mul(right),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    integer(expr).is_some_and(|count| count >= i128::from(bits))
}

/// Check one syntax module against facts already captured by its type pass.
pub(crate) fn check_module(module: &Module, facts: &[FunctionFacts]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for item in &module.items {
        if let ItemKind::Function { name, body, .. } = &item.kind {
            for facts in facts
                .iter()
                .filter(|facts| facts.span == item.span && facts.source_name == *name)
            {
                let types = facts
                    .expressions
                    .iter()
                    .map(|fact| (fact.node_addr, fact.ty.clone()))
                    .collect::<HashMap<_, _>>();
                check_block(body, &types, &mut diagnostics);
            }
        }
    }
    diagnostics
}

#[cfg(test)]
mod tests {
    use super::{evaluate, Value};
    use memobits_diagnostics::{SourceId, Span};
    use memobits_ir::{Primitive, Type as IrType};
    use memobits_syntax::{Expr, ExprKind, Type as SyntaxType};
    use std::collections::HashMap;

    fn span() -> Span {
        Span {
            source: SourceId(0),
            start: 0,
            end: 1,
        }
    }

    fn widened_sum(right: &str) -> (Box<Expr>, HashMap<usize, Option<IrType>>) {
        let cast = Expr {
            span: span(),
            kind: ExprKind::Cast {
                value: Box::new(Expr {
                    span: span(),
                    kind: ExprKind::Number("255".into()),
                }),
                target: SyntaxType {
                    span: span(),
                    path: vec!["u32".into()],
                    arguments: vec![],
                },
            },
        };
        let sum = Box::new(Expr {
            span: span(),
            kind: ExprKind::Binary {
                operator: "+".into(),
                left: Box::new(cast),
                right: Box::new(Expr {
                    span: span(),
                    kind: ExprKind::Number(right.into()),
                }),
            },
        });
        let types = HashMap::from([(
            &*sum as *const Expr as usize,
            Some(IrType::Primitive(Primitive::U32)),
        )]);
        (sum, types)
    }

    #[test]
    fn widened_casts_preserve_constants_and_detect_u32_overflow() {
        let (valid, types) = widened_sum("1");
        assert_eq!(evaluate(&valid, &types), Value::Integer(256));

        let (overflow, types) = widened_sum("4294967295");
        assert_eq!(evaluate(&overflow, &types), Value::Overflow);
    }
}
