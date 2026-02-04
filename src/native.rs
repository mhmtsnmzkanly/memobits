//! native:: namespace — host fonksiyonları kaydı ve çağrı.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use crate::collections::HashMap;

#[cfg(feature = "std")]
use std::io::{self, Write};

use crate::value::{HeapObject, Value, EvalResult};
#[cfg(feature = "std")]
use crate::value::RuntimeError;

#[derive(Clone)]
pub struct NativeRegistry {
    fns: HashMap<String, NativeFnType>,
}

type NativeFnType = fn(&[Value]) -> EvalResult;

impl NativeRegistry {
    #[cfg(feature = "std")]
    pub fn new() -> Self {
        let mut fns = HashMap::new();
        fns.insert("print".into(), native_print as NativeFnType);
        fns.insert("debug".into(), native_debug as NativeFnType);
        fns.insert("input".into(), native_input as NativeFnType);
        fns.insert("return".into(), native_return as NativeFnType);
        Self { fns }
    }

    pub fn empty() -> Self {
        Self { fns: HashMap::new() }
    }

    pub fn register(&mut self, name: impl Into<String>, f: NativeFnType) {
        self.fns.insert(name.into(), f);
    }

    pub fn get(&self, name: &str) -> Option<NativeFnType> {
        self.fns.get(name).copied()
    }
}

#[cfg(feature = "std")]
fn native_print(args: &[Value]) -> EvalResult {
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            print!(" ");
        }
        print!("{}", value_to_string(a));
    }
    println!();
    io::stdout().flush().map_err(|e| RuntimeError(e.to_string()))?;
    Ok(Value::Unit)
}

#[cfg(feature = "std")]
fn native_debug(args: &[Value]) -> EvalResult {
    dbg!(args);
    println!();
    io::stdout().flush().map_err(|e| RuntimeError(e.to_string()))?;
    Ok(Value::Unit)
}

pub fn value_to_string(v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Float(f) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Char(c) => c.to_string(),
        Value::Unit => "()".to_string(),
        Value::HeapRef(h) => match h.as_ref() {
            HeapObject::String(s) => s.to_string(),
            HeapObject::Struct { type_id, fields } => {
                let fs: Vec<_> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, v)| format!("#{}: {}", i, value_to_string(v)))
                    .collect();
                format!("{} {{ {} }}", type_id, fs.join(", "))
            }
            HeapObject::Enum { type_id, variant_id, payload } => {
                if type_id == "Option" {
                    return match (variant_id, payload.as_slice()) {
                        (0, []) => "None".to_string(),
                        (1, [d]) => format!("Some({})", value_to_string(d)),
                        _ => format!("{}::#{}", type_id, variant_id),
                    };
                }
                if type_id == "Result" {
                    return match (variant_id, payload.as_slice()) {
                        (0, [d]) => format!("Ok({})", value_to_string(d)),
                        (1, [d]) => format!("Err({})", value_to_string(d)),
                        _ => format!("{}::#{}", type_id, variant_id),
                    };
                }
                match payload.as_slice() {
                    [] => format!("{}::#{}", type_id, variant_id),
                    [d] => format!("{}::#{}({})", type_id, variant_id, value_to_string(d)),
                    _ => {
                        let inner: Vec<_> = payload.iter().map(value_to_string).collect();
                        format!("{}::#{}({})", type_id, variant_id, inner.join(", "))
                    }
                }
            }
            HeapObject::List(vec) => {
                let inner: Vec<_> = vec.borrow().iter().map(value_to_string).collect();
                format!("[{}]", inner.join(", "))
            }
            HeapObject::Array(arr) => {
                let inner: Vec<_> = arr.iter().map(value_to_string).collect();
                format!("[{}]", inner.join(", "))
            }
            HeapObject::Map(m) => {
                let inner: Vec<_> = m
                    .borrow()
                    .iter()
                    .map(|(k, v)| format!("{} => {}", value_to_string(k), value_to_string(v)))
                    .collect();
                format!("{{ {} }}", inner.join(", "))
            }
            HeapObject::Tuple { labels, values } => {
                let inner: Vec<_> = values
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        if let Some(label) = labels.get(i).and_then(|l| l.as_ref()) {
                            format!("{}: {}", label, value_to_string(v))
                        } else {
                            value_to_string(v)
                        }
                    })
                    .collect();
                format!("({})", inner.join(", "))
            }
            HeapObject::Closure { .. } => "<closure>".to_string(),
        },
    }
}

#[cfg(feature = "std")]
fn native_input(_args: &[Value]) -> EvalResult {
    let mut s = String::new();
    io::stdin()
        .read_line(&mut s)
        .map_err(|e| RuntimeError(e.to_string()))?;
    if s.ends_with('\n') {
        s.pop();
    }
    Ok(Value::string(s))
}

#[cfg(feature = "std")]
fn native_return(args: &[Value]) -> EvalResult {
    let code = match args.first() {
        Some(Value::Int(i)) => *i,
        _ => 0,
    };
    Err(RuntimeError(format!("exit:{}", code)))
}
