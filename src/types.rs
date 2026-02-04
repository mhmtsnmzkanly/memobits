//! Tip sistemi: Type enum ve yardımcılar.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use crate::collections::HashMap;

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

    Tuple(Vec<TupleField>),
    Struct { name: String, fields: HashMap<String, Type> },
    Enum { name: String, variants: Vec<EnumVariant> },
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    pub data: Option<Type>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TupleField {
    pub typ: Type,
    pub label: Option<String>,
}

impl Type {
    pub fn unit() -> Self {
        Type::Unit
    }

    pub fn fn_type(params: Vec<Type>, ret: Type) -> Self {
        Type::Fn(params, Box::new(ret))
    }
}
