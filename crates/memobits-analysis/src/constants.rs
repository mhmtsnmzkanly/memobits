//! Static checks for integer operations whose operands are numeric literals.
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity};
use memobits_ir::{Primitive, Type};
use memobits_syntax::{Block, Expr, ExprKind, ItemKind, Module, StatementKind};
use std::collections::HashMap;

use crate::types::FunctionFacts;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Integer(i128),
    Overflow,
    DivisionByZero,
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

fn evaluate(expr: &Expr, types: &HashMap<usize, Option<Type>>) -> Value {
    match &expr.kind {
        ExprKind::Number(raw) if !raw.contains(['.', 'e', 'E']) => raw
            .replace('_', "")
            .parse::<i128>()
            .map(Value::Integer)
            .unwrap_or(Value::Unknown),
        ExprKind::Unary { operator, operand } if operator == "+" || operator == "-" => {
            let Some((min, max)) = types
                .get(&(expr as *const Expr as usize))
                .and_then(Option::as_ref)
                .and_then(integer_type)
            else {
                return Value::Unknown;
            };
            let Value::Integer(value) = evaluate(operand, types) else {
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
        ExprKind::Binary {
            operator,
            left,
            right,
        } if matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%") => {
            let Some((min, max)) = types
                .get(&(expr as *const Expr as usize))
                .and_then(Option::as_ref)
                .and_then(integer_type)
            else {
                return Value::Unknown;
            };
            // A zero divisor is invalid even when the numerator is dynamic.
            if matches!(operator.as_str(), "/" | "%") && evaluate(right, types) == Value::Integer(0)
            {
                return Value::DivisionByZero;
            }
            let (Value::Integer(left), Value::Integer(right)) =
                (evaluate(left, types), evaluate(right, types))
            else {
                return Value::Unknown;
            };
            let result = match operator.as_str() {
                "+" => left.checked_add(right),
                "-" => left.checked_sub(right),
                "*" => left.checked_mul(right),
                "/" if right == 0 => return Value::DivisionByZero,
                "%" if right == 0 => return Value::DivisionByZero,
                "/" => left.checked_div(right),
                "%" => left.checked_rem(right),
                _ => unreachable!(),
            };
            let Some(result) = result else {
                return Value::Overflow;
            };
            if !(min..=max).contains(&result) {
                Value::Overflow
            } else {
                Value::Integer(result)
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
        ExprKind::Number(_) | ExprKind::Bool(_) | ExprKind::Path(_) => {}
        ExprKind::Array(elements) => {
            for element in elements {
                check_expr(element, types, diagnostics);
            }
        }
        ExprKind::RepeatArray { value, .. } => check_expr(value, types, diagnostics),
        ExprKind::Index { base, index } => {
            check_expr(base, types, diagnostics);
            check_expr(index, types, diagnostics);
        }
        ExprKind::Unary { operand, .. } => check_expr(operand, types, diagnostics),
        ExprKind::Binary { left, right, .. } => {
            check_expr(left, types, diagnostics);
            check_expr(right, types, diagnostics);
        }
        ExprKind::Call { callee, arguments } => {
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
        Value::Integer(_) | Value::Unknown => {}
    }
}

fn check_block(
    block: &Block,
    types: &HashMap<usize, Option<Type>>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Binding { value, .. } | StatementKind::Expression(value) => {
                check_expr(value, types, diagnostics)
            }
            StatementKind::Assign { target, value, .. } => {
                check_expr(target, types, diagnostics);
                check_expr(value, types, diagnostics);
            }
            StatementKind::Return(Some(value)) => check_expr(value, types, diagnostics),
            StatementKind::Return(None) | StatementKind::Break | StatementKind::Continue => {}
            StatementKind::Loop(body) => check_block(body, types, diagnostics),
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

/// Check one syntax module against facts already captured by its type pass.
pub(crate) fn check_module(module: &Module, facts: &[FunctionFacts]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut function_index = 0;
    for item in &module.items {
        if let ItemKind::Function { body, .. } = &item.kind {
            let Some(facts) = facts.get(function_index) else {
                continue;
            };
            function_index += 1;
            let types = facts
                .expressions
                .iter()
                .map(|fact| (fact.node_addr, fact.ty.clone()))
                .collect::<HashMap<_, _>>();
            check_block(body, &types, &mut diagnostics);
        }
    }
    diagnostics
}
