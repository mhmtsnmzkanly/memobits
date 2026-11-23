//! Lower source numeric and Boolean operators into their typed IR variants.
use memobits_ir::{BinaryOp, Primitive, Type, UnaryOp};

pub(super) fn binary_op(value: &str) -> BinaryOp {
    match value {
        "+" | "+=" => BinaryOp::Add,
        "-" | "-=" => BinaryOp::Subtract,
        "*" | "*=" => BinaryOp::Multiply,
        "&" | "&=" => BinaryOp::BitwiseAnd,
        "|=" => BinaryOp::BitwiseOr,
        "^=" => BinaryOp::BitwiseXor,
        "<<=" => BinaryOp::ShiftLeft,
        ">>=" => BinaryOp::ShiftRight,
        "^" => BinaryOp::BitwiseXor,
        "|" => BinaryOp::BitwiseOr,
        "<<" => BinaryOp::ShiftLeft,
        ">>" => BinaryOp::ShiftRight,
        "/" | "/=" => BinaryOp::Divide,
        "%" | "%=" => BinaryOp::Remainder,
        "<" => BinaryOp::Less,
        "<=" => BinaryOp::LessEqual,
        ">" => BinaryOp::Greater,
        ">=" => BinaryOp::GreaterEqual,
        "==" => BinaryOp::Equal,
        "!=" => BinaryOp::NotEqual,
        "&&" => BinaryOp::And,
        "||" => BinaryOp::Or,
        _ => unreachable!("checked operator"),
    }
}

pub(super) fn unary_op(value: &str) -> UnaryOp {
    match value {
        "+" => UnaryOp::Plus,
        "-" => UnaryOp::Negate,
        "!" => UnaryOp::Not,
        _ => unreachable!("checked operator"),
    }
}

pub(super) fn primitive_type(ty: &Type) -> Option<Primitive> {
    match ty {
        Type::Primitive(primitive) => Some(*primitive),
        _ => None,
    }
}
