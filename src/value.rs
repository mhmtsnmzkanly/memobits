//! Runtime değerler (Value) ve interpreter tarafı kullanımı.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub type NativeFn = fn(args: &[Value]) -> EvalResult;

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    String(Rc<str>),
    Unit,

    Option(Option<Box<Value>>),
    Result(Result<Box<Value>, Box<Value>>),

    Struct { name: String, fields: HashMap<String, Value> },
    Variant { enum_name: String, variant: String, data: Option<Box<Value>> },

    List(Rc<RefCell<Vec<Value>>>),
    Array(Rc<[Value]>),
    Map(Rc<RefCell<Vec<(Value, Value)>>>),

    NativeFn(String, NativeFn),
    Lambda(LambdaClosure),
}

#[derive(Clone)]
pub struct LambdaClosure {
    pub params: Vec<String>,
    pub body: crate::ast::Expr,
    pub env: Rc<RefCell<crate::environment::Environment>>,
}

impl std::fmt::Debug for LambdaClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LambdaClosure")
            .field("params", &self.params)
            .field("body", &"...")
            .finish()
    }
}

pub type EvalResult = Result<Value, RuntimeError>;

#[derive(Debug, Clone)]
pub struct RuntimeError(pub String);

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for RuntimeError {}

impl Value {
    pub fn string(s: impl Into<String>) -> Self {
        Value::String(Rc::from(s.into().as_str()))
    }
}
