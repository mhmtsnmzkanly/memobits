//! AST-walking interpreter.

use alloc::{format, vec};
use alloc::rc::Rc;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cell::RefCell;
use crate::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::environment::Environment;
use crate::native::{NativeRegistry, value_to_string};
use crate::types::Type;
use crate::value::{EvalResult, FunctionId, HeapObject, RuntimeError, Value, value_type_name};

#[derive(Clone)]
pub struct Interpreter {
    pub env: Rc<RefCell<Environment>>,
    pub native: NativeRegistry,
    struct_defs: HashMap<String, StructDef>,
    enum_defs: HashMap<String, EnumDef>,
    functions: Rc<RefCell<Vec<FunctionDef>>>,
    source: Option<String>,
}

#[derive(Clone, Debug)]
pub enum Flow {
    Next,
    Break,
    Continue,
    Return(Value),
}

#[derive(Clone)]
struct FunctionDef {
    name: Option<String>,
    params: Vec<String>,
    param_types: Vec<Option<Type>>,
    body: Expr,
}

impl Interpreter {
    pub fn new(native: NativeRegistry) -> Self {
        Self {
            env: Rc::new(RefCell::new(Environment::new())),
            native,
            struct_defs: HashMap::new(),
            enum_defs: HashMap::new(),
            functions: Rc::new(RefCell::new(Vec::new())),
            source: None,
        }
    }

    pub fn set_source(&mut self, src: &str) {
        self.source = Some(src.to_string());
    }

    pub fn run(&mut self, program: &Program) -> EvalResult {
        for item in &program.items {
            self.run_item(item)?;
        }
        Ok(Value::Unit)
    }

    fn with_span(&self, span: &Span, err: RuntimeError) -> RuntimeError {
        let suffix = if let Some(src) = &self.source {
            let (line, col) = line_col(src, span.lo);
            format!(" (at {}:{})", line, col)
        } else {
            format!(" (at {}..{})", span.lo, span.hi)
        };
        if err.0.contains("(at ") {
            err
        } else {
            RuntimeError(format!("{}{}", err.0, suffix))
        }
    }

    fn block_span(stmts: &[Stmt]) -> Span {
        if let Some(first) = stmts.first() {
            let last = stmts.last().unwrap();
            Span {
                lo: first.span.lo,
                hi: last.span.hi,
            }
        } else {
            Span { lo: 0, hi: 0 }
        }
    }

    fn register_function(
        &mut self,
        name: Option<String>,
        params: Vec<String>,
        param_types: Vec<Option<Type>>,
        body: Expr,
    ) -> FunctionId {
        let mut funcs = self.functions.borrow_mut();
        let id = funcs.len();
        funcs.push(FunctionDef { name, params, param_types, body });
        id
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
            Item::TypeAlias(_) => Ok(Value::Unit),
            Item::ModuleDecl(_) => Ok(Value::Unit),
            Item::FnDef(d) => {
                let name = d.name.clone();
                let params: Vec<String> = d.params.iter().map(|(p, _)| p.clone()).collect();
                let param_types: Vec<Option<Type>> = d.params.iter().map(|(_, t)| Some(t.clone())).collect();
                let body_span = Interpreter::block_span(&d.body);
                let body_expr = Expr {
                    node: ExprKind::Block(d.body.clone()),
                    span: body_span,
                };
                let fn_id = self.register_function(Some(name.clone()), params, param_types, body_expr);
                let captured = self.env.borrow().snapshot();
                let f = Value::heap(HeapObject::Closure { fn_id, env: captured });
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
        let res = match &s.node {
            StmtKind::Let(b) => {
                let typ = b.typ.clone();
                let v = self.eval(&b.init)?;
                let v = self.apply_tuple_labels(typ.as_ref(), v);
                self.env.borrow_mut().define(b.name.clone(), v, false);
                Ok(Flow::Next)
            }
            StmtKind::Var(b) => {
                let typ = b.typ.clone();
                let v = self.eval(&b.init)?;
                let v = self.apply_tuple_labels(typ.as_ref(), v);
                self.env.borrow_mut().define(b.name.clone(), v, true);
                Ok(Flow::Next)
            }
            StmtKind::Assign { name, value } => {
                let v = self.eval(value)?;
                if !self.env.borrow_mut().set(name, v) {
                    return Err(RuntimeError(format!("cannot assign to immutable binding `{}`", name)));
                }
                Ok(Flow::Next)
            }
            StmtKind::AssignIndex { base, index, value } => {
                let b = self.eval(base)?;
                let i = self.eval(index)?;
                let v = self.eval(value)?;
                match (b, i) {
                    (Value::HeapRef(h), Value::Int(idx)) => match h.as_ref() {
                        HeapObject::List(vec) => {
                            let idx = idx as usize;
                            let mut guard = vec.borrow_mut();
                            if idx >= guard.len() {
                                return Err(RuntimeError(format!(
                                    "list index out of bounds: {} (len {})",
                                    idx,
                                    guard.len()
                                )));
                            }
                            guard[idx] = v;
                            Ok(Flow::Next)
                        }
                        HeapObject::Array(_) => Err(RuntimeError("cannot assign to array index (arrays are immutable at runtime)".into())),
                        _ => Err(RuntimeError(format!(
                            "index assignment on non-list/map (got {})",
                            value_type_name(&b)
                        ))),
                    },
                    (Value::HeapRef(h), key_val) => match h.as_ref() {
                        HeapObject::Map(map) => {
                            self.ensure_map_key(&key_val)?;
                            map.borrow_mut().insert(key_val, v);
                            Ok(Flow::Next)
                        }
                        _ => Err(RuntimeError(format!(
                            "index assignment on non-list/map (got {})",
                            value_type_name(&b)
                        ))),
                    },
                    _ => Err(RuntimeError(format!(
                        "index assignment on non-list/map (got {})",
                        value_type_name(&b)
                    ))),
                }
            }
            StmtKind::Expr(e) => {
                self.eval(e)?;
                Ok(Flow::Next)
            }
            StmtKind::If { cond, then_b, else_b } => {
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
            StmtKind::Loop(body) => loop {
                match self.run_stmts(body) {
                    Ok(Flow::Break) => return Ok(Flow::Next),
                    Ok(Flow::Continue) | Ok(Flow::Next) => {}
                    Ok(Flow::Return(v)) => return Ok(Flow::Return(v)),
                    Err(e) => {
                        if e.0.starts_with("exit:") {
                            let code = e.0.strip_prefix("exit:").and_then(|s| s.parse().ok()).unwrap_or(0);
                            #[cfg(feature = "std")]
                            {
                                std::process::exit(code);
                            }
                            #[cfg(not(feature = "std"))]
                            {
                                let _code = code;
                            }
                        }
                        return Err(e);
                    }
                }
            },
            StmtKind::Match { scrutinee, arms } => {
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
            StmtKind::Return(expr) => {
                let v = match expr {
                    Some(e) => self.eval(e)?,
                    None => Value::Unit,
                };
                Ok(Flow::Return(v))
            }
            StmtKind::Break => Ok(Flow::Break),
            StmtKind::Continue => Ok(Flow::Continue),
        };
        res.map_err(|e| self.with_span(&s.span, e))
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
            (Pattern::Literal(Literal::String(a)), Value::HeapRef(h)) => match h.as_ref() {
                HeapObject::String(b) => Ok(a.as_str() == b.as_str()),
                _ => Ok(false),
            },
            (Pattern::Literal(Literal::None), Value::HeapRef(h)) => match h.as_ref() {
                HeapObject::Enum { type_id, variant_id, payload } => {
                    Ok(type_id == "Option" && *variant_id == 0 && payload.is_empty())
                }
                _ => Ok(false),
            },
            (Pattern::StructLiteral { name, fields }, Value::HeapRef(h)) => match h.as_ref() {
                HeapObject::Struct { type_id, fields: vals } => {
                    if name != type_id {
                        return Ok(false);
                    }
                    self.validate_struct_pattern(name, fields)?;
                    for (fname, pat) in fields {
                        let idx = self.struct_field_index(type_id, fname)?;
                        let Some(fv) = vals.get(idx) else { return Ok(false) };
                        if !self.match_pattern_into(pat, fv, env.clone())? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ => Ok(false),
            },
            (Pattern::Variant { enum_name, variant, inner }, Value::HeapRef(h)) => match h.as_ref() {
                HeapObject::Enum { type_id, variant_id, payload } if enum_name == type_id => {
                    let (vid, expects_data) = self.enum_variant_id(enum_name, variant)?;
                    if *variant_id != vid {
                        return Ok(false);
                    }
                    match (expects_data, inner, payload.as_slice()) {
                        (true, Some(pat), [d]) => self.match_pattern_into(pat, d, env),
                        (true, None, [_]) => Ok(true),
                        (true, _, []) => Ok(false),
                        (false, None, []) => Ok(true),
                        (false, Some(_), _) => Err(RuntimeError(format!(
                            "pattern has data but variant `{}`::`{}` has no data",
                            enum_name, variant
                        ))),
                        _ => Ok(false),
                    }
                }
                _ => Ok(false),
            },
            _ => Ok(false),
        }
    }

    pub fn eval(&mut self, e: &Expr) -> EvalResult {
        let res = match &e.node {
            ExprKind::Literal(l) => self.eval_literal(l),
            ExprKind::Ident(name) => self.env
                .borrow()
                .get(name)
                .ok_or_else(|| RuntimeError(format!("undefined variable `{}`", name))),
            ExprKind::NativeCall(name, args) => {
                let f = self.native.get(name).ok_or_else(|| RuntimeError(format!("unknown native `{}`", name)))?;
                let vals: Vec<Value> = args.iter().map(|a| self.eval(a)).collect::<Result<Vec<_>, _>>()?;
                let r = f(&vals);
                if let Err(ref e) = r {
                    if e.0.starts_with("exit:") {
                        let code = e.0.strip_prefix("exit:").and_then(|s| s.parse().ok()).unwrap_or(0);
                        #[cfg(feature = "std")]
                        {
                            std::process::exit(code);
                        }
                        #[cfg(not(feature = "std"))]
                        {
                            let _code = code;
                        }
                    }
                }
                r
            }
            ExprKind::Binary { op, left, right } => {
                match op {
                    BinOp::And => {
                        let l = self.eval(left)?;
                        match l {
                            Value::Bool(false) => Ok(Value::Bool(false)),
                            Value::Bool(true) => {
                                let r = self.eval(right)?;
                                self.eval_binop(*op, &l, &r)
                            }
                            _ => Err(RuntimeError("&& expects Bool operands".into())),
                        }
                    }
                    BinOp::Or => {
                        let l = self.eval(left)?;
                        match l {
                            Value::Bool(true) => Ok(Value::Bool(true)),
                            Value::Bool(false) => {
                                let r = self.eval(right)?;
                                self.eval_binop(*op, &l, &r)
                            }
                            _ => Err(RuntimeError("|| expects Bool operands".into())),
                        }
                    }
                    _ => {
                        let l = self.eval(left)?;
                        let r = self.eval(right)?;
                        self.eval_binop(*op, &l, &r)
                    }
                }
            }
            ExprKind::Unary { op, inner } => {
                let v = self.eval(inner)?;
                self.eval_unop(*op, &v)
            }
            ExprKind::Call { callee, args } => {
                let f = self.eval(callee)?;
                let arg_vals: Vec<Value> = args.iter().map(|a| self.eval(a)).collect::<Result<Vec<_>, _>>()?;
                self.call(&f, &arg_vals)
            }
            ExprKind::Block(stmts) => {
                self.eval_block_value(stmts)
            }
            ExprKind::StructLiteral { name, fields } => {
                let vals = self.build_struct_fields(name, fields)?;
                Ok(Value::heap(HeapObject::Struct {
                    type_id: name.clone(),
                    fields: vals,
                }))
            }
            ExprKind::VariantLiteral { enum_name, variant, data } => {
                let (variant_id, expects_data) = self.enum_variant_id(enum_name, variant)?;
                match (expects_data, data) {
                    (true, Some(expr)) => {
                        let v = self.eval(expr)?;
                        Ok(Value::heap(HeapObject::Enum {
                            type_id: enum_name.clone(),
                            variant_id,
                            payload: vec![v],
                        }))
                    }
                    (true, None) => Err(RuntimeError(format!(
                        "variant `{}`::`{}` expects data",
                        enum_name, variant
                    ))),
                    (false, Some(_)) => Err(RuntimeError(format!(
                        "variant `{}`::`{}` does not take data",
                        enum_name, variant
                    ))),
                    (false, None) => Ok(Value::heap(HeapObject::Enum {
                        type_id: enum_name.clone(),
                        variant_id,
                        payload: Vec::new(),
                    })),
                }
            }
            ExprKind::FieldAccess { base, field } => {
                let b = self.eval(base)?;
                match &b {
                    Value::HeapRef(h) => match h.as_ref() {
                        HeapObject::Struct { type_id, fields } => {
                            let idx = self.struct_field_index(type_id, field)?;
                            fields
                                .get(idx)
                                .cloned()
                                .ok_or_else(|| RuntimeError(format!("no field `{}`", field)))
                        }
                        HeapObject::Tuple { labels, values } => {
                            if let Ok(idx) = field.parse::<usize>() {
                                return values
                                    .get(idx)
                                    .cloned()
                                    .ok_or_else(|| RuntimeError(format!(
                                        "tuple index out of bounds: {} (len {})",
                                        idx,
                                        values.len()
                                    )));
                            }
                            let pos = labels
                                .iter()
                                .position(|l| l.as_deref() == Some(field.as_str()));
                            if let Some(idx) = pos {
                                values
                                    .get(idx)
                                    .cloned()
                                    .ok_or_else(|| RuntimeError(format!(
                                        "tuple index out of bounds: {} (len {})",
                                        idx,
                                        values.len()
                                    )))
                            } else {
                                Err(RuntimeError(format!("unknown tuple label `{}`", field)))
                            }
                        }
                        _ => Err(RuntimeError(format!(
                            "field access on non-struct/tuple (got {})",
                            value_type_name(&b)
                        ))),
                    },
                    _ => Err(RuntimeError(format!(
                        "field access on non-struct/tuple (got {})",
                        value_type_name(&b)
                    ))),
                }
            }
            ExprKind::ListLiteral(elems) => {
                let v: Vec<Value> = elems.iter().map(|e| self.eval(e)).collect::<Result<Vec<_>, _>>()?;
                Ok(Value::heap(HeapObject::List(RefCell::new(v))))
            }
            ExprKind::ArrayLiteral(elems) => {
                let v: Vec<Value> = elems.iter().map(|e| self.eval(e)).collect::<Result<Vec<_>, _>>()?;
                Ok(Value::heap(HeapObject::Array(v)))
            }
            ExprKind::Template { parts } => {
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
                Ok(Value::string(s))
            }
            ExprKind::Index { base, index } => {
                let b = self.eval(base)?;
                let i = self.eval(index)?;
                match (&b, &i) {
                    (Value::HeapRef(h), Value::Int(idx)) => match h.as_ref() {
                        HeapObject::List(vec) => {
                            let idx = *idx as usize;
                            let guard = vec.borrow();
                            guard
                                .get(idx)
                                .cloned()
                                .ok_or_else(|| RuntimeError(format!("list index out of bounds: {} (len {})", idx, guard.len())))
                        }
                        HeapObject::Array(arr) => {
                            let idx = *idx as usize;
                            arr.get(idx)
                                .cloned()
                                .ok_or_else(|| RuntimeError(format!("array index out of bounds: {} (len {})", idx, arr.len())))
                        }
                        _ => Err(RuntimeError(format!(
                            "index on non-list/array/map (got {})",
                            value_type_name(&b)
                        ))),
                    },
                    (Value::HeapRef(h), key_val) => match h.as_ref() {
                        HeapObject::Map(map) => {
                            self.ensure_map_key(key_val)?;
                            map.borrow()
                                .get(key_val)
                                .cloned()
                                .ok_or_else(|| RuntimeError(format!(
                                    "map key not found: {}",
                                    value_to_string(key_val)
                                )))
                        }
                        _ => Err(RuntimeError(format!(
                            "index on non-list/array/map (got {})",
                            value_type_name(&b)
                        ))),
                    },
                    _ => Err(RuntimeError(format!(
                        "index on non-list/array/map (got {})",
                        value_type_name(&b)
                    ))),
                }
            }
            ExprKind::Lambda { params, body } => {
                let ps: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
                let param_types: Vec<Option<Type>> = params.iter().map(|(_, t)| t.clone()).collect();
                let fn_id = self.register_function(None, ps, param_types, body.as_ref().clone());
                let captured = self.env.borrow().snapshot();
                Ok(Value::heap(HeapObject::Closure { fn_id, env: captured }))
            }
            ExprKind::MapLiteral(pairs) => {
                let mut m = HashMap::new();
                for (k, v) in pairs {
                    let key_val = self.eval(k)?;
                    self.ensure_map_key(&key_val)?;
                    let val = self.eval(v)?;
                    m.insert(key_val, val);
                }
                Ok(Value::heap(HeapObject::Map(RefCell::new(m))))
            }
            ExprKind::TupleLiteral(elems) => {
                let vals = elems
                    .iter()
                    .map(|e| self.eval(e))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::heap(HeapObject::Tuple {
                    labels: vec![None; vals.len()],
                    values: vals,
                }))
            }
            ExprKind::If { cond, then_b, else_b } => {
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
            ExprKind::Match { scrutinee, arms } => {
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
        };
        res.map_err(|err| self.with_span(&e.span, err))
    }

    fn eval_block_value(&mut self, stmts: &[Stmt]) -> EvalResult {
        // NOTE: Block expression icin yeni scope olusturulur.
        let prev = self.env.clone();
        self.env = Rc::new(RefCell::new(Environment::with_parent(prev.clone())));
        let mut last = Value::Unit;
        for s in stmts {
            match &s.node {
                StmtKind::Expr(e) => last = self.eval(e)?,
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
            Literal::String(s) => Ok(Value::string((*s).clone())),
            Literal::Unit => Ok(Value::Unit),
            // NOTE: Option/Result literal'leri de Variant olarak temsili ediliyor.
            Literal::None => Ok(Value::heap(HeapObject::Enum {
                type_id: "Option".to_string(),
                variant_id: 0,
                payload: Vec::new(),
            })),
            Literal::Some(e) => Ok(Value::heap(HeapObject::Enum {
                type_id: "Option".to_string(),
                variant_id: 1,
                payload: vec![self.eval(e)?],
            })),
            Literal::Ok(e) => Ok(Value::heap(HeapObject::Enum {
                type_id: "Result".to_string(),
                variant_id: 0,
                payload: vec![self.eval(e)?],
            })),
            Literal::Err(e) => Ok(Value::heap(HeapObject::Enum {
                type_id: "Result".to_string(),
                variant_id: 1,
                payload: vec![self.eval(e)?],
            })),
        }
    }

    fn build_struct_fields(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
    ) -> Result<Vec<Value>, RuntimeError> {
        let (field_names, field_count) = {
            let def = self
                .struct_defs
                .get(name)
                .ok_or_else(|| RuntimeError(format!("unknown struct `{}`", name)))?;
            let names = def.fields.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>();
            (names, def.fields.len())
        };
        let mut out: Vec<Option<Value>> = vec![None; field_count];
        let mut seen = HashSet::new();
        for (f, ex) in fields {
            if !seen.insert(f.as_str()) {
                return Err(RuntimeError(format!(
                    "duplicate field `{}` for struct `{}`",
                    f, name
                )));
            }
            let idx = self.struct_field_index(name, f)?;
            out[idx] = Some(self.eval(ex)?);
        }
        let mut missing = Vec::new();
        for (i, val) in out.iter().enumerate() {
            if val.is_none() {
                missing.push(field_names[i].clone());
            }
        }
        if !missing.is_empty() {
            return Err(RuntimeError(format!(
                "missing field(s) for struct `{}`: {}",
                name,
                missing.join(", ")
            )));
        }
        Ok(out.into_iter().map(|v| v.unwrap()).collect())
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
        let def_fields: HashSet<&str> =
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

    fn struct_field_index(&self, name: &str, field: &str) -> Result<usize, RuntimeError> {
        let def = self
            .struct_defs
            .get(name)
            .ok_or_else(|| RuntimeError(format!("unknown struct `{}`", name)))?;
        def.fields
            .iter()
            .position(|(n, _)| n == field)
            .ok_or_else(|| RuntimeError(format!("unknown field `{}` for struct `{}`", field, name)))
    }

    fn ensure_map_key(&self, v: &Value) -> Result<(), RuntimeError> {
        match v {
            Value::Int(_) | Value::Bool(_) | Value::Char(_) => Ok(()),
            Value::HeapRef(h) => match h.as_ref() {
                HeapObject::String(_) => Ok(()),
                _ => Err(RuntimeError(format!(
                    "map key must be Int/Bool/Char/String (got {})",
                    value_type_name(v)
                ))),
            },
            _ => Err(RuntimeError(format!(
                "map key must be Int/Bool/Char/String (got {})",
                value_type_name(v)
            ))),
        }
    }

    fn apply_tuple_labels(&self, typ: Option<&Type>, v: Value) -> Value {
        let Some(Type::Tuple(fields)) = typ else {
            return v;
        };
        let Value::HeapRef(h) = v else {
            return v;
        };
        match h.as_ref() {
            HeapObject::Tuple { labels, values } => {
                let has_any_label = labels.iter().any(|l| l.is_some());
                if has_any_label {
                    return Value::HeapRef(h);
                }
                if values.len() != fields.len() {
                    return Value::HeapRef(h);
                }
                let new_labels = fields.iter().map(|f| f.label.clone()).collect::<Vec<_>>();
                Value::heap(HeapObject::Tuple {
                    labels: new_labels,
                    values: values.clone(),
                })
            }
            _ => Value::HeapRef(h),
        }
    }

    fn enum_variant_id(
        &self,
        enum_name: &str,
        variant: &str,
    ) -> Result<(usize, bool), RuntimeError> {
        if enum_name == "Option" {
            return match variant {
                "None" => Ok((0, false)),
                "Some" => Ok((1, true)),
                _ => Err(RuntimeError(format!(
                    "unknown variant `{}` for enum `Option`",
                    variant
                ))),
            };
        }
        if enum_name == "Result" {
            return match variant {
                "Ok" => Ok((0, true)),
                "Err" => Ok((1, true)),
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
        let (idx, v) = def
            .variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.name == variant)
            .ok_or_else(|| RuntimeError(format!(
                "unknown variant `{}` for enum `{}`",
                variant, enum_name
            )))?;
        Ok((idx, v.data.is_some()))
    }

    fn eval_binop(&mut self, op: BinOp, l: &Value, r: &Value) -> EvalResult {
        use crate::ast::BinOp::*;
        match (op, l, r) {
            (Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Add, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            (Add, Value::HeapRef(a), Value::HeapRef(b)) => match (a.as_ref(), b.as_ref()) {
                (HeapObject::String(sa), HeapObject::String(sb)) => {
                    Ok(Value::string(format!("{}{}", sa, sb)))
                }
                _ => Err(RuntimeError(format!("type error: {:?} {:?} {:?}", op, l, r))),
            },
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
            (Eq, Value::HeapRef(a), Value::HeapRef(b)) => match (a.as_ref(), b.as_ref()) {
                (HeapObject::String(sa), HeapObject::String(sb)) => Ok(Value::Bool(sa == sb)),
                _ => Ok(Value::Bool(false)),
            },
            (Ne, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a != b)),
            (Ne, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a != b)),
            (Ne, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a != b)),
            (Ne, Value::HeapRef(a), Value::HeapRef(b)) => match (a.as_ref(), b.as_ref()) {
                (HeapObject::String(sa), HeapObject::String(sb)) => Ok(Value::Bool(sa != sb)),
                _ => Ok(Value::Bool(true)),
            },
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
            Value::HeapRef(h) => match h.as_ref() {
                HeapObject::Closure { fn_id, env } => {
                    let def = {
                        let funcs = self.functions.borrow();
                        funcs
                            .get(*fn_id)
                            .cloned()
                            .ok_or_else(|| RuntimeError("unknown function id".into()))?
                    };
                    if def.params.len() != args.len() {
                        return Err(RuntimeError("arity mismatch".into()));
                    }
                    let captured_env = Environment::with_captured(env.clone());
                    let child = Rc::new(RefCell::new(captured_env));
                    for ((p, ty), a) in def.params.iter().zip(def.param_types.iter()).zip(args) {
                        let v = self.apply_tuple_labels(ty.as_ref(), a.clone());
                        child.borrow_mut().define(p.clone(), v, false);
                    }
                    if let Some(ref name) = def.name {
                        if child.borrow().get(name).is_none() {
                            child.borrow_mut().define(name.clone(), f.clone(), false);
                        }
                    }
                    let mut interp = Interpreter {
                        env: child,
                        native: self.native.clone(),
                        struct_defs: self.struct_defs.clone(),
                        enum_defs: self.enum_defs.clone(),
                        functions: self.functions.clone(),
                        source: self.source.clone(),
                    };
                    match &def.body.node {
                        ExprKind::Block(stmts) => {
                            let mut last = Value::Unit;
                            for s in stmts {
                                match &s.node {
                                    StmtKind::Expr(e) => last = interp.eval(e)?,
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
                        _ => interp.eval(&def.body),
                    }
                }
                _ => Err(RuntimeError("calling non-function".into())),
            },
            _ => Err(RuntimeError("calling non-function".into())),
        }
    }
}

fn line_col(src: &str, idx: usize) -> (usize, usize) {
    let mut line = 1usize;
    let mut col = 1usize;
    for (i, ch) in src.char_indices() {
        if i >= idx {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}
