//! Tip sistemi: Type enum ve yardımcılar.

use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    // NOTE: Tip cikarimi asamasinda gecici olarak kullanilan tip.
    Unknown,
    Int,
    Float,
    Bool,
    Char,
    String,
    Unit,

    Array(Box<Type>, usize),
    List(Box<Type>),
    Map(Box<Type>, Box<Type>),

    Option(Box<Type>),
    Result(Box<Type>, Box<Type>),

    Fn(Vec<Type>, Box<Type>),

    Struct { name: String, fields: HashMap<String, Type> },
    Enum { name: String, variants: Vec<EnumVariant> },
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    pub data: Option<Type>,
}

impl Type {
    pub fn unit() -> Self {
        Type::Unit
    }

    pub fn fn_type(params: Vec<Type>, ret: Type) -> Self {
        Type::Fn(params, Box::new(ret))
    }
}
