//! AST-walking interpreter.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;
use crate::environment::Environment;
use crate::native::NativeRegistry;
use crate::value::{Value, EvalResult, RuntimeError, LambdaClosure};
use crate::value::MapKey;

#[derive(Clone)]
pub struct Interpreter {
    pub env: Rc<RefCell<Environment>>,
    pub native: NativeRegistry,
    struct_defs: HashMap<String, StructDef>,
    enum_defs: HashMap<String, EnumDef>,
}

#[derive(Clone, Debug)]
pub enum Flow {
    Next,
    Break,
    Continue,
    Return(Value),
}

impl Interpreter {
    pub fn new(native: NativeRegistry) -> Self {
        Self {
            env: Rc::new(RefCell::new(Environment::new())),
            native,
            struct_defs: HashMap::new(),
            enum_defs: HashMap::new(),
        }
    }

    pub fn run(&mut self, program: &Program) -> EvalResult {
        for item in &program.items {
            self.run_item(item)?;
        }
        Ok(Value::Unit)
    }

    fn run_item(&mut self, item: &Item) -> EvalResult {
        match item {
            Item::StructDef(d) => {
                self.struct_defs.insert(d.name.clone(), d.clone());
                Ok(Value::Unit)
            }
            Item::EnumDef(d) => {
                self.enum_defs.insert(d.name.clone(), d.clone());
                Ok(Value::Unit)
            }
            Item::FnDef(d) => {
                let name = d.name.clone();
                let params: Vec<String> = d.params.iter().map(|(p, _)| p.clone()).collect();
                let body = d.body.clone();
                let env = self.env.clone();
                let f = Value::Lambda(LambdaClosure {
                    params,
                    body: Expr::Block(body),
                    env,
                });
                self.env.borrow_mut().define(name, f, false);
                Ok(Value::Unit)
            }
            Item::GlobalLet(b) => {
                let v = self.eval(&b.init)?;
                self.env.borrow_mut().define(b.name.clone(), v, false);
                Ok(Value::Unit)
            }
            Item::GlobalVar(b) => {
                let v = self.eval(&b.init)?;
                self.env.borrow_mut().define(b.name.clone(), v, true);
                Ok(Value::Unit)
            }
            Item::TopLevelStmt(s) => {
                let f = self.run_stmt(s)?;
                match f {
                    Flow::Next => Ok(Value::Unit),
                    Flow::Break => Err(RuntimeError("break outside loop".into())),
                    Flow::Continue => Err(RuntimeError("continue outside loop".into())),
                    Flow::Return(_) => Err(RuntimeError("return outside function".into())),
                }
            }
        }
    }

    fn run_stmts(&mut self, stmts: &[Stmt]) -> Result<Flow, RuntimeError> {
        for s in stmts {
            match self.run_stmt(s)? {
                Flow::Next => {}
                f => return Ok(f),
            }
        }
        Ok(Flow::Next)
    }

    fn run_stmt(&mut self, s: &Stmt) -> Result<Flow, RuntimeError> {
        match s {
            Stmt::Let(b) => {
                let v = self.eval(&b.init)?;
                self.env.borrow_mut().define(b.name.clone(), v, false);
                Ok(Flow::Next)
            }
            Stmt::Var(b) => {
                let v = self.eval(&b.init)?;
                self.env.borrow_mut().define(b.name.clone(), v, true);
                Ok(Flow::Next)
            }
            Stmt::Assign { name, value } => {
                let v = self.eval(value)?;
                if !self.env.borrow_mut().set(name, v) {
                    return Err(RuntimeError(format!("cannot assign to immutable binding `{}`", name)));
                }
                Ok(Flow::Next)
            }
            Stmt::Expr(e) => {
                self.eval(e)?;
                Ok(Flow::Next)
            }
            Stmt::If { cond, then_b, else_b } => {
                let c = self.eval(cond)?;
                let b = match &c {
                    Value::Bool(true) => true,
                    Value::Bool(false) => false,
                    _ => return Err(RuntimeError("if condition must be Bool".into())),
                };
                if b {
                    self.run_stmts(then_b)
                } else if let Some(eb) = else_b {
                    self.run_stmts(eb)
                } else {
                    Ok(Flow::Next)
                }
            }
            Stmt::Loop(body) => loop {
                match self.run_stmts(body) {
                    Ok(Flow::Break) => return Ok(Flow::Next),
                    Ok(Flow::Continue) | Ok(Flow::Next) => {}
                    Ok(Flow::Return(v)) => return Ok(Flow::Return(v)),
                    Err(e) => {
                        if e.0.starts_with("exit:") {
                            let code = e.0.strip_prefix("exit:").and_then(|s| s.parse().ok()).unwrap_or(0);
                            std::process::exit(code);
                        }
                        return Err(e);
                    }
                }
            },
            Stmt::Match { scrutinee, arms } => {
                let v = self.eval(scrutinee)?;
                for arm in arms {
                    if let Some(env_ext) = self.match_pattern(&arm.pattern, &v)? {
                        let prev = self.env.clone();
                        self.env = env_ext;
                        let f = self.run_stmts(&arm.body)?;
                        self.env = prev;
                        return Ok(f);
                    }
                }
                Err(RuntimeError("non-exhaustive match".into()))
            }
            Stmt::Return(expr) => {
                let v = match expr {
                    Some(e) => self.eval(e)?,
                    None => Value::Unit,
                };
                Ok(Flow::Return(v))
            }
            Stmt::Break => Ok(Flow::Break),
            Stmt::Continue => Ok(Flow::Continue),
        }
    }

    fn match_pattern(
        &mut self,
        p: &Pattern,
        v: &Value,
    ) -> Result<Option<Rc<RefCell<Environment>>>, RuntimeError> {
        // NOTE: Tek bir env uzerinde birden fazla binding'i biriktirebilmek icin
        // her eslesmede yeni bir child env olusturuyoruz.
        let ext = Rc::new(RefCell::new(Environment::with_parent(self.env.clone())));
        if self.match_pattern_into(p, v, ext.clone())? {
            Ok(Some(ext))
        } else {
            Ok(None)
        }
    }

    fn match_pattern_into(
        &mut self,
        p: &Pattern,
        v: &Value,
        env: Rc<RefCell<Environment>>,
    ) -> Result<bool, RuntimeError> {
        match (p, v) {
            (Pattern::Wildcard, _) => Ok(true),
            (Pattern::Ident(name), _) => {
                env.borrow_mut().define(name.clone(), v.clone(), false);
                Ok(true)
            }
            (Pattern::Literal(Literal::Int(i)), Value::Int(j)) => Ok(*i == *j),
            (Pattern::Literal(Literal::Float(a)), Value::Float(b)) => Ok(*a == *b),
            (Pattern::Literal(Literal::Bool(a)), Value::Bool(b)) => Ok(*a == *b),
            (Pattern::Literal(Literal::Char(a)), Value::Char(b)) => Ok(*a == *b),
            (Pattern::Literal(Literal::String(a)), Value::String(b)) => Ok(a.as_str() == b.as_ref()),
            // NOTE: Option degerleri Variant(Option::Some/None) olarak temsil ediliyor.
            (Pattern::Literal(Literal::None), Value::Variant { enum_name, variant, data })
                if enum_name == "Option" && variant == "None" && data.is_none() =>
            {
                Ok(true)
            }
            (Pattern::StructLiteral { name, fields }, Value::Struct { name: vn, fields: vals }) => {
                if name != vn {
                    return Ok(false);
                }
                self.validate_struct_pattern(name, fields)?;
                for (fname, pat) in fields {
                    let Some(fv) = vals.get(fname) else { return Ok(false) };
                    if !self.match_pattern_into(pat, fv, env.clone())? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Pattern::Variant { enum_name, variant, inner }, Value::Variant { enum_name: en, variant: vn, data })
                if enum_name == en && variant == vn =>
            {
                let expects_data = self.enum_variant_expects_data(enum_name, variant)?;
                match (expects_data, inner, data) {
                    (Some(true), Some(pat), Some(d)) => self.match_pattern_into(pat, d, env),
                    (Some(true), None, Some(_)) => Ok(true),
                    (Some(true), _, None) => Ok(false),
                    (Some(false), None, None) => Ok(true),
                    (Some(false), Some(_), _) => Err(RuntimeError(format!(
                        "pattern has data but variant `{}`::`{}` has no data",
                        enum_name, variant
                    ))),
                    _ => Ok(false),
                }
            }
            _ => Ok(false),
        }
    }

    pub fn eval(&mut self, e: &Expr) -> EvalResult {
        match e {
            Expr::Literal(l) => self.eval_literal(l),
            Expr::Ident(name) => self.env
                .borrow()
                .get(name)
                .ok_or_else(|| RuntimeError(format!("undefined variable `{}`", name))),
            Expr::NativeCall(name, args) => {
                let f = self.native.get(name).ok_or_else(|| RuntimeError(format!("unknown native `{}`", name)))?;
                let vals: Vec<Value> = args.iter().map(|a| self.eval(a)).collect::<Result<Vec<_>, _>>()?;
                let r = f(&vals);
                if let Err(ref e) = r {
                    if e.0.starts_with("exit:") {
                        let code = e.0.strip_prefix("exit:").and_then(|s| s.parse().ok()).unwrap_or(0);
                        std::process::exit(code);
                    }
                }
                r
            }
            Expr::Binary { op, left, right } => {
                let l = self.eval(left)?;
                let r = self.eval(right)?;
                self.eval_binop(*op, &l, &r)
            }
            Expr::Unary { op, inner } => {
                let v = self.eval(inner)?;
                self.eval_unop(*op, &v)
            }
            Expr::Call { callee, args } => {
                let f = self.eval(callee)?;
                let arg_vals: Vec<Value> = args.iter().map(|a| self.eval(a)).collect::<Result<Vec<_>, _>>()?;
                self.call(&f, &arg_vals)
            }
            Expr::Block(stmts) => {
                self.eval_block_value(stmts)
            }
            Expr::StructLiteral { name, fields } => {
                self.validate_struct_literal(name, fields)?;
                let mut map = HashMap::new();
                for (f, ex) in fields {
                    map.insert(f.clone(), self.eval(ex)?);
                }
                Ok(Value::Struct { name: name.clone(), fields: map })
            }
            Expr::VariantLiteral { enum_name, variant, data } => {
                self.validate_variant_literal(enum_name, variant, data.as_deref())?;
                let d = match data {
                    Some(e) => Some(Box::new(self.eval(e)?)),
                    None => None,
                };
                Ok(Value::Variant { enum_name: enum_name.clone(), variant: variant.clone(), data: d })
            }
            Expr::FieldAccess { base, field } => {
                let b = self.eval(base)?;
                match &b {
                    Value::Struct { fields, .. } => fields.get(field).cloned().ok_or_else(|| RuntimeError(format!("no field `{}`", field))),
                    _ => Err(RuntimeError("field access on non-struct".into())),
                }
            }
            Expr::ListLiteral(elems) => {
                let v: Vec<Value> = elems.iter().map(|e| self.eval(e)).collect::<Result<Vec<_>, _>>()?;
                Ok(Value::List(Rc::new(RefCell::new(v))))
            }
            Expr::ArrayLiteral(elems) => {
                let v: Vec<Value> = elems.iter().map(|e| self.eval(e)).collect::<Result<Vec<_>, _>>()?;
                let a: Rc<[Value]> = v.into();
                Ok(Value::Array(a))
            }
            Expr::Template { parts } => {
                let mut s = String::new();
                for p in parts {
                    match p {
                        TemplatePart::Lit(l) => s.push_str(l),
                        TemplatePart::Interp(id) => {
                            let v = self.env.borrow().get(id).ok_or_else(|| RuntimeError(format!("undefined `{}` in template", id)))?;
                            s.push_str(&crate::native::value_to_string(&v));
                        }
                    }
                }
                Ok(Value::String(Rc::from(s.into_boxed_str())))
            }
            Expr::Index { base, index } => {
                let b = self.eval(base)?;
                let i = self.eval(index)?;
                match (&b, &i) {
                    (Value::List(vec), Value::Int(idx)) => {
                        let idx = *idx as usize;
                        vec.borrow().get(idx).cloned().ok_or_else(|| RuntimeError("index out of bounds".into()))
                    }
                    (Value::Array(arr), Value::Int(idx)) => {
                        let idx = *idx as usize;
                        arr.get(idx).cloned().ok_or_else(|| RuntimeError("index out of bounds".into()))
                    }
                    _ => Err(RuntimeError("invalid index".into())),
                }
            }
            Expr::Lambda { params, body } => {
                let ps: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
                Ok(Value::Lambda(LambdaClosure {
                    params: ps,
                    body: body.as_ref().clone(),
                    env: self.env.clone(),
                }))
            }
            Expr::MapLiteral(pairs) => {
                let mut m = HashMap::new();
                for (k, v) in pairs {
                    let key_val = self.eval(k)?;
                    let key = MapKey::from_value(&key_val).ok_or_else(|| {
                        RuntimeError("map key must be Int/Bool/Char/String".into())
                    })?;
                    let val = self.eval(v)?;
                    m.insert(key, val);
                }
                Ok(Value::Map(Rc::new(RefCell::new(m))))
            }
            Expr::If { cond, then_b, else_b } => {
                let c = self.eval(cond)?;
                let b = match &c {
                    Value::Bool(true) => true,
                    Value::Bool(false) => false,
                    _ => return Err(RuntimeError("if condition must be Bool".into())),
                };
                if b {
                    self.eval_block_value(then_b)
                } else if let Some(eb) = else_b {
                    self.eval_block_value(eb)
                } else {
                    Ok(Value::Unit)
                }
            }
            Expr::Match { scrutinee, arms } => {
                let v = self.eval(scrutinee)?;
                for arm in arms {
                    if let Some(env_ext) = self.match_pattern(&arm.pattern, &v)? {
                        let prev = self.env.clone();
                        self.env = env_ext;
                        let r = self.eval_block_value(&arm.body);
                        self.env = prev;
                        return r;
                    }
                }
                Err(RuntimeError("non-exhaustive match".into()))
            }
        }
    }

    fn eval_block_value(&mut self, stmts: &[Stmt]) -> EvalResult {
        // NOTE: Block expression icin yeni scope olusturulur.
        let prev = self.env.clone();
        self.env = Rc::new(RefCell::new(Environment::with_parent(prev.clone())));
        let mut last = Value::Unit;
        for s in stmts {
            match s {
                Stmt::Expr(e) => last = self.eval(e)?,
                _ => match self.run_stmt(s)? {
                    Flow::Next => {}
                    Flow::Break => {
                        self.env = prev;
                        return Err(RuntimeError("break in expression block".into()));
                    }
                    Flow::Continue => {
                        self.env = prev;
                        return Err(RuntimeError("continue in expression block".into()));
                    }
                    Flow::Return(_) => {
                        self.env = prev;
                        return Err(RuntimeError("return in expression block".into()));
                    }
                },
            }
        }
        self.env = prev;
        Ok(last)
    }

    fn eval_literal(&mut self, l: &Literal) -> EvalResult {
        match l {
            Literal::Int(i) => Ok(Value::Int(*i)),
            Literal::Float(f) => Ok(Value::Float(*f)),
            Literal::Bool(b) => Ok(Value::Bool(*b)),
            Literal::Char(c) => Ok(Value::Char(*c)),
            Literal::String(s) => Ok(Value::String((*s).clone().into())),
            Literal::Unit => Ok(Value::Unit),
            // NOTE: Option/Result literal'leri de Variant olarak temsili ediliyor.
            Literal::None => Ok(Value::Variant {
                enum_name: "Option".to_string(),
                variant: "None".to_string(),
                data: None,
            }),
            Literal::Some(e) => Ok(Value::Variant {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                data: Some(Box::new(self.eval(e)?)),
            }),
            Literal::Ok(e) => Ok(Value::Variant {
                enum_name: "Result".to_string(),
                variant: "Ok".to_string(),
                data: Some(Box::new(self.eval(e)?)),
            }),
            Literal::Err(e) => Ok(Value::Variant {
                enum_name: "Result".to_string(),
                variant: "Err".to_string(),
                data: Some(Box::new(self.eval(e)?)),
            }),
        }
    }

    fn validate_struct_literal(&self, name: &str, fields: &[(String, Expr)]) -> Result<(), RuntimeError> {
        let def = self
            .struct_defs
            .get(name)
            .ok_or_else(|| RuntimeError(format!("unknown struct `{}`", name)))?;
        let mut def_fields: std::collections::HashSet<&str> =
            def.fields.iter().map(|(n, _)| n.as_str()).collect();
        for (f, _) in fields {
            if !def_fields.remove(f.as_str()) {
                return Err(RuntimeError(format!(
                    "unknown field `{}` for struct `{}`",
                    f, name
                )));
            }
        }
        if !def_fields.is_empty() {
            let missing: Vec<&str> = def_fields.into_iter().collect();
            return Err(RuntimeError(format!(
                "missing field(s) for struct `{}`: {}",
                name,
                missing.join(", ")
            )));
        }
        Ok(())
    }

    fn validate_struct_pattern(
        &self,
        name: &str,
        fields: &[(String, Pattern)],
    ) -> Result<(), RuntimeError> {
        let def = self
            .struct_defs
            .get(name)
            .ok_or_else(|| RuntimeError(format!("unknown struct `{}`", name)))?;
        let def_fields: std::collections::HashSet<&str> =
            def.fields.iter().map(|(n, _)| n.as_str()).collect();
        for (f, _) in fields {
            if !def_fields.contains(f.as_str()) {
                return Err(RuntimeError(format!(
                    "unknown field `{}` in pattern for struct `{}`",
                    f, name
                )));
            }
        }
        Ok(())
    }

    fn validate_variant_literal(
        &self,
        enum_name: &str,
        variant: &str,
        data: Option<&Expr>,
    ) -> Result<(), RuntimeError> {
        let expects_data = self.enum_variant_expects_data(enum_name, variant)?;
        match (expects_data, data) {
            (Some(true), Some(_)) => Ok(()),
            (Some(true), None) => Err(RuntimeError(format!(
                "variant `{}`::`{}` expects data",
                enum_name, variant
            ))),
            (Some(false), None) => Ok(()),
            (Some(false), Some(_)) => Err(RuntimeError(format!(
                "variant `{}`::`{}` does not take data",
                enum_name, variant
            ))),
            (None, _) => Err(RuntimeError(format!(
                "unknown enum `{}`",
                enum_name
            ))),
        }
    }

    fn enum_variant_expects_data(
        &self,
        enum_name: &str,
        variant: &str,
    ) -> Result<Option<bool>, RuntimeError> {
        if enum_name == "Option" {
            return match variant {
                "Some" => Ok(Some(true)),
                "None" => Ok(Some(false)),
                _ => Err(RuntimeError(format!(
                    "unknown variant `{}` for enum `Option`",
                    variant
                ))),
            };
        }
        if enum_name == "Result" {
            return match variant {
                "Ok" => Ok(Some(true)),
                "Err" => Ok(Some(true)),
                _ => Err(RuntimeError(format!(
                    "unknown variant `{}` for enum `Result`",
                    variant
                ))),
            };
        }
        let def = self
            .enum_defs
            .get(enum_name)
            .ok_or_else(|| RuntimeError(format!("unknown enum `{}`", enum_name)))?;
        let v = def
            .variants
            .iter()
            .find(|v| v.name == variant)
            .ok_or_else(|| RuntimeError(format!(
                "unknown variant `{}` for enum `{}`",
                variant, enum_name
            )))?;
        Ok(Some(v.data.is_some()))
    }

    fn eval_binop(&mut self, op: BinOp, l: &Value, r: &Value) -> EvalResult {
        use crate::ast::BinOp::*;
        match (op, l, r) {
            (Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Add, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            (Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Sub, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
            (Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
            (Mul, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
            (Div, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
            (Div, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
            (Rem, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a % b)),
            (Rem, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a % b)),
            (Eq, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a == b)),
            (Eq, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a == b)),
            (Eq, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
            (Eq, Value::Char(a), Value::Char(b)) => Ok(Value::Bool(a == b)),
            (Ne, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a != b)),
            (Ne, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a != b)),
            (Ne, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a != b)),
            (Lt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
            (Lt, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
            (Le, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
            (Le, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
            (Gt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
            (Gt, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
            (Ge, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
            (Ge, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
            (And, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a && *b)),
            (Or, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a || *b)),
            _ => Err(RuntimeError(format!("type error: {:?} {:?} {:?}", op, l, r))),
        }
    }

    fn eval_unop(&mut self, op: UnaryOp, v: &Value) -> EvalResult {
        use crate::ast::UnaryOp::*;
        match (op, v) {
            (Neg, Value::Int(i)) => Ok(Value::Int(-i)),
            (Neg, Value::Float(f)) => Ok(Value::Float(-f)),
            (Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
            _ => Err(RuntimeError(format!("type error: unary {:?} {:?}", op, v))),
        }
    }

    fn call(&mut self, f: &Value, args: &[Value]) -> EvalResult {
        match f {
            Value::NativeFn(name, _) => {
                let ptr = self.native.get(name).ok_or_else(|| RuntimeError(format!("native `{}` not found", name)))?;
                ptr(args)
            }
            Value::Lambda(cl) => {
                if cl.params.len() != args.len() {
                    return Err(RuntimeError("arity mismatch".into()));
                }
                let child = Rc::new(RefCell::new(Environment::with_parent(cl.env.clone())));
                for (p, a) in cl.params.iter().zip(args) {
                    child.borrow_mut().define(p.clone(), a.clone(), false);
                }
                let mut interp = Interpreter {
                    env: child,
                    native: self.native.clone(),
                    struct_defs: self.struct_defs.clone(),
                    enum_defs: self.enum_defs.clone(),
                };
                match &cl.body {
                    Expr::Block(stmts) => {
                        let mut last = Value::Unit;
                        for s in stmts {
                            match s {
                                Stmt::Expr(e) => last = interp.eval(e)?,
                                _ => match interp.run_stmt(s)? {
                                    Flow::Next => {}
                                    Flow::Return(v) => return Ok(v),
                                    Flow::Break => return Err(RuntimeError("break outside loop".into())),
                                    Flow::Continue => return Err(RuntimeError("continue outside loop".into())),
                                },
                            }
                        }
                        Ok(last)
                    }
                    _ => interp.eval(&cl.body),
                }
            }
            _ => Err(RuntimeError("calling non-function".into())),
        }
    }
}
