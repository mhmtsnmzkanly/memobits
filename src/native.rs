//! native:: namespace — host fonksiyonları kaydı ve çağrı.

use std::collections::HashMap;
use std::io::{self, Write};

use crate::value::{Value, EvalResult, RuntimeError};

#[derive(Clone)]
pub struct NativeRegistry {
    fns: HashMap<String, NativeFnType>,
}

type NativeFnType = fn(&[Value]) -> EvalResult;

impl NativeRegistry {
    pub fn new() -> Self {
        let mut fns = HashMap::new();
        fns.insert("print".into(), native_print as NativeFnType);
        fns.insert("debug".into(), native_debug as NativeFnType);
        fns.insert("input".into(), native_input as NativeFnType);
        fns.insert("return".into(), native_return as NativeFnType);
        Self { fns }
    }

    pub fn register(&mut self, name: impl Into<String>, f: NativeFnType) {
        self.fns.insert(name.into(), f);
    }

    pub fn get(&self, name: &str) -> Option<NativeFnType> {
        self.fns.get(name).copied()
    }
}

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
        Value::String(s) => s.to_string(),
        Value::Unit => "()".to_string(),
        Value::Option(Some(x)) => value_to_string(x),
        Value::Option(None) => "None".to_string(),
        Value::Result(Ok(x)) => format!("Ok({})", value_to_string(x)),
        Value::Result(Err(e)) => format!("Err({})", value_to_string(e)),
        Value::Struct { name, fields } => {
            let fs: Vec<_> = fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, value_to_string(v)))
                .collect();
            format!("{} {{ {} }}", name, fs.join(", "))
        }
        Value::Variant { enum_name, variant, data } => match data {
            Some(d) => format!("{}::{}({})", enum_name, variant, value_to_string(d.as_ref())),
            None => format!("{}::{}", enum_name, variant),
        },
        Value::List(vec) => {
            let inner: Vec<_> = vec.borrow().iter().map(value_to_string).collect();
            format!("[{}]", inner.join(", "))
        }
        Value::Array(arr) => {
            let inner: Vec<_> = arr.iter().map(value_to_string).collect();
            format!("[{}]", inner.join(", "))
        }
        Value::Map(m) => {
            let inner: Vec<_> = m
                .borrow()
                .iter()
                .map(|(k, v)| format!("{} => {}", value_to_string(k), value_to_string(v)))
                .collect();
            format!("{{ {} }}", inner.join(", "))
        }
        Value::NativeFn(name, _) => format!("<native {}>", name),
        Value::Lambda(_) => "<lambda>".to_string(),
    }
}

fn native_input(_args: &[Value]) -> EvalResult {
    let mut s = String::new();
    io::stdin()
        .read_line(&mut s)
        .map_err(|e| RuntimeError(e.to_string()))?;
    if s.ends_with('\n') {
        s.pop();
    }
    Ok(Value::String(s.into()))
}

fn native_return(args: &[Value]) -> EvalResult {
    let code = match args.first() {
        Some(Value::Int(i)) => *i,
        _ => 0,
    };
    Err(RuntimeError(format!("exit:{}", code)))
}
