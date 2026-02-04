//! Runtime değerler (Value) ve heap nesneleri.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;
use core::mem;
use core::cell::RefCell;
use core::hash::{Hash, Hasher};
use crate::collections::HashMap;

pub type EvalResult = Result<Value, RuntimeError>;

#[derive(Debug, Clone)]
pub struct RuntimeError(pub String);

impl core::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RuntimeError {}

pub type FunctionId = usize;
pub type EnvRef = Rc<HashMap<String, Value>>;

#[derive(Clone)]
pub enum Value {
    Int(i64),
    UInt(u64),
    Float(f64),
    Bool(bool),
    Char(char),
    Unit,
    HeapRef(Rc<HeapObject>),
}

impl core::fmt::Debug for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "Int({})", i),
            Value::UInt(u) => write!(f, "UInt({})", u),
            Value::Float(x) => write!(f, "Float({})", x),
            Value::Bool(b) => write!(f, "Bool({})", b),
            Value::Char(c) => write!(f, "Char({})", c),
            Value::Unit => write!(f, "Unit"),
            Value::HeapRef(h) => write!(f, "HeapRef({:?})", h),
        }
    }
}

impl Value {
    pub fn string(s: impl Into<String>) -> Self {
        Value::HeapRef(Rc::new(HeapObject::String(s.into())))
    }

    pub fn heap(obj: HeapObject) -> Self {
        Value::HeapRef(Rc::new(obj))
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::HeapRef(h) => match h.as_ref() {
                HeapObject::String(s) => Some(s.as_str()),
                _ => None,
            },
            _ => None,
        }
    }
}

pub fn value_type_name(v: &Value) -> String {
    match v {
        Value::Int(_) => "Int".into(),
        Value::UInt(_) => "UInt".into(),
        Value::Float(_) => "Float".into(),
        Value::Bool(_) => "Bool".into(),
        Value::Char(_) => "Char".into(),
        Value::Unit => "Unit".into(),
        Value::HeapRef(h) => match h.as_ref() {
            HeapObject::String(_) => "String".into(),
            HeapObject::Struct { type_id, .. } => format!("Struct({})", type_id),
            HeapObject::Enum { type_id, .. } => format!("Enum({})", type_id),
            HeapObject::Tuple { .. } => "Tuple".into(),
            HeapObject::List(_) => "List".into(),
            HeapObject::Array(_) => "Array".into(),
            HeapObject::Map(_) => "Map".into(),
            HeapObject::Closure { .. } => "Closure".into(),
        },
    }
}

#[derive(Debug)]
pub enum HeapObject {
    String(String),

    Struct {
        type_id: String,
        fields: Vec<Value>,
    },

    Enum {
        type_id: String,
        variant_id: usize,
        payload: Vec<Value>,
    },

    Tuple {
        labels: Vec<Option<String>>,
        values: Vec<Value>,
    },

    List(RefCell<Vec<Value>>),
    Array(Vec<Value>),
    Map(RefCell<HashMap<Value, Value>>),

    Closure {
        fn_id: FunctionId,
        env: EnvRef,
    },
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::UInt(a), Value::UInt(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a.to_bits() == b.to_bits(),
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Char(a), Value::Char(b)) => a == b,
            (Value::Unit, Value::Unit) => true,
            (Value::HeapRef(a), Value::HeapRef(b)) => match (a.as_ref(), b.as_ref()) {
                (HeapObject::String(sa), HeapObject::String(sb)) => sa == sb,
                _ => Rc::ptr_eq(a, b),
            },
            _ => false,
        }
    }
}

impl Eq for Value {}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        let ta = variant_rank(self);
        let tb = variant_rank(other);
        if ta != tb {
            return ta.cmp(&tb);
        }
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a.cmp(b),
            (Value::UInt(a), Value::UInt(b)) => a.cmp(b),
            (Value::Float(a), Value::Float(b)) => a.to_bits().cmp(&b.to_bits()),
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
            (Value::Char(a), Value::Char(b)) => a.cmp(b),
            (Value::Unit, Value::Unit) => Ordering::Equal,
            (Value::HeapRef(a), Value::HeapRef(b)) => match (a.as_ref(), b.as_ref()) {
                (HeapObject::String(sa), HeapObject::String(sb)) => sa.cmp(sb),
                _ => {
                    let pa = Rc::as_ptr(a) as usize;
                    let pb = Rc::as_ptr(b) as usize;
                    pa.cmp(&pb)
                }
            },
            _ => Ordering::Equal,
        }
    }
}

fn variant_rank(v: &Value) -> u8 {
    match v {
        Value::Int(_) => 0,
        Value::UInt(_) => 1,
        Value::Float(_) => 2,
        Value::Bool(_) => 3,
        Value::Char(_) => 4,
        Value::Unit => 5,
        Value::HeapRef(_) => 6,
    }
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        mem::discriminant(self).hash(state);
        match self {
            Value::Int(i) => i.hash(state),
            Value::UInt(u) => u.hash(state),
            Value::Float(f) => f.to_bits().hash(state),
            Value::Bool(b) => b.hash(state),
            Value::Char(c) => c.hash(state),
            Value::Unit => {}
            Value::HeapRef(h) => match h.as_ref() {
                HeapObject::String(s) => s.hash(state),
                _ => {
                    let ptr = Rc::as_ptr(h) as usize;
                    ptr.hash(state);
                }
            },
        }
    }
}
