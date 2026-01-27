//! AST-walking interpreter.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;
use crate::environment::Environment;
use crate::native::NativeRegistry;
use crate::value::{Value, EvalResult, RuntimeError, LambdaClosure};

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
            Stmt::Break => Ok(Flow::Break),
            Stmt::Continue => Ok(Flow::Continue),
        }
    }

    fn match_pattern(
        &mut self,
        p: &Pattern,
        v: &Value,
    ) -> Result<Option<Rc<RefCell<Environment>>>, RuntimeError> {
        match (p, v) {
            (Pattern::Wildcard, _) => Ok(Some(self.env.clone())),
            (Pattern::Ident(name), _) => {
                let ext = Rc::new(RefCell::new(Environment::with_parent(self.env.clone())));
                ext.borrow_mut().define(name.clone(), v.clone(), false);
                Ok(Some(ext))
            }
            (Pattern::Literal(Literal::Int(i)), Value::Int(j)) if *i == *j => Ok(Some(self.env.clone())),
            (Pattern::Literal(Literal::Bool(a)), Value::Bool(b)) if *a == *b => Ok(Some(self.env.clone())),
            (Pattern::Literal(Literal::None), Value::Option(None)) => Ok(Some(self.env.clone())),
            (Pattern::Variant { enum_name, variant, inner }, _) if enum_name == "Option" && variant == "Some" => {
                let Value::Option(Some(ref d)) = v else { return Ok(None) };
                let Some(pat) = inner else { return Ok(Some(self.env.clone())) };
                self.match_pattern(pat, d)
            }
            (Pattern::Variant { enum_name, variant, inner }, Value::Variant { enum_name: en, variant: vn, data }) if enum_name == en && variant == vn => {
                let ext = Rc::new(RefCell::new(Environment::with_parent(self.env.clone())));
                match (inner, data) {
                    (Some(pat), Some(d)) => self.match_pattern(pat, d),
                    (None, None) => Ok(Some(ext)),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
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
                let prev = self.env.clone();
                self.env = Rc::new(RefCell::new(Environment::with_parent(prev.clone())));
                let mut last = Value::Unit;
                for s in stmts {
                    match s {
                        Stmt::Expr(e) => last = self.eval(e)?,
                        _ => { self.run_stmt(s)?; }
                    }
                }
                self.env = prev;
                Ok(last)
            }
            Expr::StructLiteral { name, fields } => {
                let mut map = HashMap::new();
                for (f, ex) in fields {
                    map.insert(f.clone(), self.eval(ex)?);
                }
                Ok(Value::Struct { name: name.clone(), fields: map })
            }
            Expr::VariantLiteral { enum_name, variant, data } => {
                let d = data.as_ref().map(|e| Box::new(self.eval(e).unwrap()));
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
                let v: Vec<(Value, Value)> = pairs
                    .iter()
                    .map(|(k, v)| Ok((self.eval(k)?, self.eval(v)?)))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Map(Rc::new(RefCell::new(v))))
            }
            Expr::If { .. } | Expr::Match { .. } => Err(RuntimeError("if/match as expression not implemented".into())),
        }
    }

    fn eval_literal(&mut self, l: &Literal) -> EvalResult {
        match l {
            Literal::Int(i) => Ok(Value::Int(*i)),
            Literal::Float(f) => Ok(Value::Float(*f)),
            Literal::Bool(b) => Ok(Value::Bool(*b)),
            Literal::Char(c) => Ok(Value::Char(*c)),
            Literal::String(s) => Ok(Value::String((*s).clone().into())),
            Literal::Unit => Ok(Value::Unit),
            Literal::None => Ok(Value::Option(None)),
            Literal::Some(e) => Ok(Value::Option(Some(Box::new(self.eval(e)?)))),
            Literal::Ok(e) => Ok(Value::Result(Ok(Box::new(self.eval(e)?)))),
            Literal::Err(e) => Ok(Value::Result(Err(Box::new(self.eval(e)?)))),
        }
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
                                _ => { interp.run_stmt(s)?; }
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
