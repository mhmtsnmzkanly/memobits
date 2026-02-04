//! Basit TypeChecker (taslak): AST uzerinde tip denetimi ve kismi cikarim.
//! Not: Burasi bilerek "minimale" tutuldu; sonraki kisiler icin genisletilebilir.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;
use crate::types::{EnumVariant, Type};

#[derive(Clone, Debug)]
enum ConstVal {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
}

#[derive(Debug, Clone)]
pub struct TypeError(pub String);

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct TypeWarning {
    pub message: String,
    pub pos: Option<(usize, usize)>,
}

impl std::fmt::Display for TypeWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some((line, col)) = self.pos {
            write!(f, "({}, {}): {}", line, col, self.message)
        } else {
            write!(f, "{}", self.message)
        }
    }
}
#[derive(Clone)]
struct TypeBinding {
    typ: Type,
    mutable: bool,
}

#[derive(Clone, Default)]
struct TypeEnv {
    bindings: HashMap<String, TypeBinding>,
    parent: Option<Rc<RefCell<TypeEnv>>>,
}

impl TypeEnv {
    fn new() -> Self {
        Self::default()
    }

    fn with_parent(parent: Rc<RefCell<TypeEnv>>) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(parent),
        }
    }

    fn define(&mut self, name: impl Into<String>, typ: Type, mutable: bool) {
        self.bindings.insert(name.into(), TypeBinding { typ, mutable });
    }

    fn set(&mut self, name: &str, typ: Type) -> Result<(), TypeError> {
        if let Some(b) = self.bindings.get_mut(name) {
            if b.mutable {
                b.typ = typ;
                return Ok(());
            }
            return Err(TypeError(format!(
                "cannot assign to immutable binding `{}`",
                name
            )));
        }
        if let Some(ref p) = self.parent {
            return p.borrow_mut().set(name, typ);
        }
        Err(TypeError(format!("undefined binding `{}`", name)))
    }

    fn get(&self, name: &str) -> Option<TypeBinding> {
        self.bindings.get(name).cloned().or_else(|| {
            self.parent
                .as_ref()
                .and_then(|p| p.borrow().get(name))
        })
    }
}

pub struct TypeChecker {
    structs: HashMap<String, Type>,
    enums: HashMap<String, Type>,
    return_stack: Vec<Type>,
    errors: Vec<TypeError>,
    warnings: Vec<TypeWarning>,
    source: Option<String>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            structs: HashMap::new(),
            enums: HashMap::new(),
            return_stack: Vec::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
            source: None,
        }
    }

    pub fn set_source(&mut self, src: &str) {
        self.source = Some(src.to_string());
    }

    pub fn check_program(&mut self, program: &Program) -> Result<(), Vec<TypeError>> {
        self.collect_defs(program);
        let env = Rc::new(RefCell::new(TypeEnv::new()));

        // 1) Fn signature'larini onceden tanimla (recursive call'lar icin).
        for item in &program.items {
            if let Item::FnDef(def) = item {
                let params = def.params.iter().map(|(_, t)| t.clone()).collect();
                let fn_ty = Type::Fn(params, Box::new(def.ret.clone()));
                env.borrow_mut().define(def.name.clone(), fn_ty, false);
            }
        }

        // 2) Tum item'lari tip kontrol et.
        for item in &program.items {
            if let Err(e) = self.check_item(env.clone(), item) {
                self.errors.push(e);
            }
        }

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors.clone())
        }
    }

    pub fn warnings(&self) -> &[TypeWarning] {
        &self.warnings
    }

    fn collect_defs(&mut self, program: &Program) {
        for item in &program.items {
            match item {
                Item::StructDef(def) => {
                    let mut fields = HashMap::new();
                    for (n, t) in &def.fields {
                        fields.insert(n.clone(), t.clone());
                    }
                    self.structs.insert(
                        def.name.clone(),
                        Type::Struct {
                            name: def.name.clone(),
                            fields,
                        },
                    );
                }
                Item::EnumDef(def) => {
                    let variants = def
                        .variants
                        .iter()
                        .map(|v| EnumVariant {
                            name: v.name.clone(),
                            data: v.data.clone(),
                        })
                        .collect::<Vec<_>>();
                    self.enums.insert(
                        def.name.clone(),
                        Type::Enum {
                            name: def.name.clone(),
                            variants,
                        },
                    );
                }
                _ => {}
            }
        }
    }

    fn check_item(&mut self, env: Rc<RefCell<TypeEnv>>, item: &Item) -> Result<(), TypeError> {
        match item {
            Item::StructDef(_) | Item::EnumDef(_) => Ok(()),
            Item::FnDef(def) => self.check_fn_def(env, def),
            Item::GlobalLet(b) => {
                let t = self.check_expr(env.clone(), &b.init)?;
                let typ = self.apply_annotation(t, b.typ.as_ref())?;
                env.borrow_mut().define(b.name.clone(), typ, false);
                Ok(())
            }
            Item::GlobalVar(b) => {
                let t = self.check_expr(env.clone(), &b.init)?;
                let typ = self.apply_annotation(t, b.typ.as_ref())?;
                env.borrow_mut().define(b.name.clone(), typ, true);
                Ok(())
            }
            Item::TopLevelStmt(s) => {
                self.check_stmt(env, s)?;
                Ok(())
            }
        }
    }

    fn check_fn_def(&mut self, env: Rc<RefCell<TypeEnv>>, def: &FnDef) -> Result<(), TypeError> {
        let child = Rc::new(RefCell::new(TypeEnv::with_parent(env)));
        for (name, ty) in &def.params {
            child.borrow_mut().define(name.clone(), ty.clone(), false);
        }
        self.return_stack.push(def.ret.clone());
        let body_ty = self.check_block(child, &def.body)?;
        self.return_stack.pop();
        let expected = def.ret.clone();
        self.unify(body_ty, expected)
            .map(|_| ())
            .map_err(|e| TypeError(format!("fn `{}`: {}", def.name, e)))
    }

    fn check_block(&mut self, env: Rc<RefCell<TypeEnv>>, stmts: &[Stmt]) -> Result<Type, TypeError> {
        let mut last = Type::Unit;
        if let Some(pos) = stmts.iter().position(|s| matches!(s.node, StmtKind::Return(_))) {
            if pos + 1 < stmts.len() {
                let span = &stmts[pos + 1].span;
                self.warn(span, "unreachable statement after return");
            }
        }
        for s in stmts {
            match &s.node {
                StmtKind::Return(_) => {
                    let _ = self.check_stmt(env.clone(), s)?;
                    // NOTE: return sonrasinda block tipi, fonksiyon return tipi kabul edilir.
                    if let Some(ret) = self.return_stack.last() {
                        return Ok(ret.clone());
                    }
                    return Ok(Type::Unit);
                }
                _ => {
                    last = self.check_stmt(env.clone(), s)?;
                }
            }
        }
        Ok(last)
    }

    fn check_stmt(&mut self, env: Rc<RefCell<TypeEnv>>, s: &Stmt) -> Result<Type, TypeError> {
        match &s.node {
            StmtKind::Let(b) => {
                let t = self.check_expr(env.clone(), &b.init)?;
                let typ = self.apply_annotation(t, b.typ.as_ref())?;
                env.borrow_mut().define(b.name.clone(), typ, false);
                Ok(Type::Unit)
            }
            StmtKind::Var(b) => {
                let t = self.check_expr(env.clone(), &b.init)?;
                let typ = self.apply_annotation(t, b.typ.as_ref())?;
                env.borrow_mut().define(b.name.clone(), typ, true);
                Ok(Type::Unit)
            }
            StmtKind::Assign { name, value } => {
                let rhs = self.check_expr(env.clone(), value)?;
                let b = env
                    .borrow()
                    .get(name)
                    .ok_or_else(|| TypeError(format!("undefined binding `{}`", name)))?;
                let b_typ = b.typ.clone();
                let _ = self.unify(b_typ.clone(), rhs)?;
                env.borrow_mut().set(name, b_typ)?;
                Ok(Type::Unit)
            }
            StmtKind::AssignIndex { base, index, value } => {
                let bt = self.check_expr(env.clone(), base)?;
                let it = self.check_expr(env.clone(), index)?;
                let vt = self.check_expr(env, value)?;
                match bt {
                    Type::List(inner) => {
                        let _ = self.unify(Type::Int, it)?;
                        let _ = self.unify(*inner, vt)?;
                        Ok(Type::Unit)
                    }
                    Type::Array(inner, _) => {
                        let _ = self.unify(Type::Int, it)?;
                        let _ = self.unify(*inner, vt)?;
                        Ok(Type::Unit)
                    }
                    Type::Map(k, v) => {
                        let _ = self.unify(*k, it)?;
                        let _ = self.unify(*v, vt)?;
                        Ok(Type::Unit)
                    }
                    _ => Err(TypeError("index assignment on non-list/array/map".into())),
                }
            }
            StmtKind::Expr(e) => self.check_expr(env, e),
            StmtKind::If { cond, then_b, else_b } => {
                let ct = self.check_expr(env.clone(), cond)?;
                self.expect_bool(ct)?;
                if let Some(b) = self.const_bool(cond) {
                    if b {
                        if let Some(eb) = else_b.as_ref() {
                            if let Some(first) = eb.first() {
                                self.warn(&first.span, "unreachable else branch (condition is always true)");
                            }
                        }
                    } else if let Some(first) = then_b.first() {
                        self.warn(&first.span, "unreachable then branch (condition is always false)");
                    }
                }
                let t1 = self.check_block(env.clone(), then_b)?;
                let t2 = if let Some(eb) = else_b {
                    self.check_block(env.clone(), eb)?
                } else {
                    Type::Unit
                };
                self.unify(t1, t2)
            }
            StmtKind::Loop(body) => {
                let _ = self.check_block(env, body)?;
                Ok(Type::Unit)
            }
            StmtKind::Match { scrutinee, arms } => {
                let st = self.check_expr(env.clone(), scrutinee)?;
                let mut acc = Type::Unknown;
                for arm in arms {
                    let t = self.check_match_arm(env.clone(), &st, arm)?;
                    acc = self.unify(acc, t)?;
                }
                self.check_match_exhaustive(&st, arms)?;
                Ok(acc)
            }
            StmtKind::Return(expr) => {
                let expected = self
                    .return_stack
                    .last()
                    .cloned()
                    .ok_or_else(|| TypeError("return outside function".into()))?;
                let actual = match expr {
                    Some(e) => self.check_expr(env, e)?,
                    None => Type::Unit,
                };
                let _ = self.unify(expected, actual)?;
                Ok(Type::Unit)
            }
            StmtKind::Break | StmtKind::Continue => Ok(Type::Unit),
        }
    }

    fn check_expr(&mut self, env: Rc<RefCell<TypeEnv>>, e: &Expr) -> Result<Type, TypeError> {
        match &e.node {
            ExprKind::Literal(l) => match l {
                Literal::Some(inner) => {
                    let t = self.check_expr(env, inner)?;
                    Ok(Type::Option(Box::new(t)))
                }
                Literal::Ok(inner) => {
                    let t = self.check_expr(env, inner)?;
                    Ok(Type::Result(Box::new(t), Box::new(Type::Unknown)))
                }
                Literal::Err(inner) => {
                    let t = self.check_expr(env, inner)?;
                    Ok(Type::Result(Box::new(Type::Unknown), Box::new(t)))
                }
                _ => self.type_of_literal(l),
            },
            ExprKind::Ident(name) => env
                .borrow()
                .get(name)
                .map(|b| b.typ)
                .ok_or_else(|| TypeError(format!("undefined variable `{}`", name))),
            ExprKind::NativeCall(name, _args) => Ok(self.native_return_type(name)),
            ExprKind::Binary { op, left, right } => {
                let l = self.check_expr(env.clone(), left)?;
                let r = self.check_expr(env, right)?;
                if matches!(op, BinOp::Div | BinOp::Rem) {
                    if let Some(0) = self.const_int(right) {
                        return Err(TypeError("division by zero (const)".into()));
                    }
                }
                self.type_of_binop(*op, l, r)
            }
            ExprKind::Unary { op, inner } => {
                let t = self.check_expr(env, inner)?;
                self.type_of_unop(*op, t)
            }
            ExprKind::Call { callee, args } => {
                let callee_t = self.check_expr(env.clone(), callee)?;
                let Type::Fn(params, ret) = callee_t else {
                    return Err(TypeError("calling non-function".into()));
                };
                if params.len() != args.len() {
                    return Err(TypeError("arity mismatch".into()));
                }
                for (p, a) in params.iter().zip(args.iter()) {
                    let at = self.check_expr(env.clone(), a)?;
                    let _ = self.unify(p.clone(), at)?;
                }
                Ok(*ret)
            }
            ExprKind::Block(stmts) => self.check_block(env, stmts),
            ExprKind::If { cond, then_b, else_b } => {
                let ct = self.check_expr(env.clone(), cond)?;
                self.expect_bool(ct)?;
                if let Some(b) = self.const_bool(cond) {
                    if b {
                        if let Some(eb) = else_b.as_ref() {
                            if let Some(first) = eb.first() {
                                self.warn(&first.span, "unreachable else branch (condition is always true)");
                            }
                        }
                    } else if let Some(first) = then_b.first() {
                        self.warn(&first.span, "unreachable then branch (condition is always false)");
                    }
                }
                let t1 = self.check_block(env.clone(), then_b)?;
                let t2 = if let Some(eb) = else_b {
                    self.check_block(env.clone(), eb)?
                } else {
                    Type::Unit
                };
                self.unify(t1, t2)
            }
            ExprKind::Match { scrutinee, arms } => {
                let st = self.check_expr(env.clone(), scrutinee)?;
                let mut acc = Type::Unknown;
                for arm in arms {
                    let t = self.check_match_arm(env.clone(), &st, arm)?;
                    acc = self.unify(acc, t)?;
                }
                self.check_match_exhaustive(&st, arms)?;
                Ok(acc)
            }
            ExprKind::Lambda { params, body } => {
                let child = Rc::new(RefCell::new(TypeEnv::with_parent(env)));
                let mut param_types = Vec::new();
                for (name, ty) in params {
                    let t = ty.clone().unwrap_or(Type::Unknown);
                    child.borrow_mut().define(name.clone(), t.clone(), false);
                    param_types.push(t);
                }
                let ret = self.check_expr(child, body)?;
                Ok(Type::Fn(param_types, Box::new(ret)))
            }
            ExprKind::StructLiteral { name, fields } => {
                let st = self
                    .structs
                    .get(name)
                    .ok_or_else(|| TypeError(format!("unknown struct `{}`", name)))?
                    .clone();
                let Type::Struct { fields: def_fields, .. } = &st else {
                    return Err(TypeError("internal struct type error".into()));
                };
                let mut remaining = std::collections::HashSet::new();
                for f in def_fields.keys() {
                    remaining.insert(f.as_str());
                }
                for (f, v) in fields {
                    let dt = def_fields
                        .get(f)
                        .ok_or_else(|| TypeError(format!("unknown field `{}` for `{}`", f, name)))?
                        .clone();
                    let vt = self.check_expr(env.clone(), v)?;
                    let _ = self.unify(dt, vt)?;
                    remaining.remove(f.as_str());
                }
                if !remaining.is_empty() {
                    let missing: Vec<&str> = remaining.into_iter().collect();
                    return Err(TypeError(format!(
                        "missing field(s) for struct `{}`: {}",
                        name,
                        missing.join(", ")
                    )));
                }
                Ok(st)
            }
            ExprKind::VariantLiteral { enum_name, variant, data } => {
                let et = self
                    .enums
                    .get(enum_name)
                    .ok_or_else(|| TypeError(format!("unknown enum `{}`", enum_name)))?
                    .clone();
                let Type::Enum { variants, .. } = &et else {
                    return Err(TypeError("internal enum type error".into()));
                };
                let v = variants
                    .iter()
                    .find(|v| v.name == *variant)
                    .ok_or_else(|| TypeError(format!(
                        "unknown variant `{}` for enum `{}`",
                        variant, enum_name
                    )))?;
                match (&v.data, data) {
                    (Some(dt), Some(expr)) => {
                        let vt = self.check_expr(env, expr)?;
                        let _ = self.unify(dt.clone(), vt)?;
                    }
                    (None, None) => {}
                    (Some(_), None) => {
                        return Err(TypeError(format!(
                            "variant `{}`::`{}` expects data",
                            enum_name, variant
                        )))
                    }
                    (None, Some(_)) => {
                        return Err(TypeError(format!(
                            "variant `{}`::`{}` does not take data",
                            enum_name, variant
                        )))
                    }
                }
                Ok(et)
            }
            ExprKind::FieldAccess { base, field } => {
                let bt = self.check_expr(env, base)?;
                let bt = self.resolve_type(&bt);
                let Type::Struct { fields, .. } = bt else {
                    return Err(TypeError("field access on non-struct".into()));
                };
                fields
                    .get(field)
                    .cloned()
                    .ok_or_else(|| TypeError(format!("unknown field `{}`", field)))
            }
            ExprKind::Index { base, index } => {
                let bt = self.check_expr(env.clone(), base)?;
                let it = self.check_expr(env, index)?;
                match bt {
                    Type::List(inner) => {
                        let _ = self.unify(Type::Int, it)?;
                        Ok(*inner)
                    }
                    Type::Array(inner, n) => {
                        let _ = self.unify(Type::Int, it)?;
                        if let Some(idx) = self.const_int(index) {
                            if idx < 0 || (idx as usize) >= n {
                                return Err(TypeError("array index out of bounds (const)".into()));
                            }
                        }
                        Ok(*inner)
                    }
                    Type::Map(k, v) => {
                        let _ = self.unify(*k, it)?;
                        Ok(*v)
                    }
                    _ => Err(TypeError("index on non-list/array/map".into())),
                }
            }
            ExprKind::ListLiteral(elems) => {
                let mut acc = Type::Unknown;
                for e in elems {
                    let t = self.check_expr(env.clone(), e)?;
                    acc = self.unify(acc, t)?;
                }
                Ok(Type::List(Box::new(acc)))
            }
            ExprKind::ArrayLiteral(elems) => {
                let mut acc = Type::Unknown;
                for e in elems {
                    let t = self.check_expr(env.clone(), e)?;
                    acc = self.unify(acc, t)?;
                }
                Ok(Type::Array(Box::new(acc), elems.len()))
            }
            ExprKind::MapLiteral(pairs) => {
                let mut k = Type::Unknown;
                let mut v = Type::Unknown;
                for (ke, ve) in pairs {
                    let kt = self.check_expr(env.clone(), ke)?;
                    k = self.unify(k, kt)?;
                    let vt = self.check_expr(env.clone(), ve)?;
                    v = self.unify(v, vt)?;
                }
                Ok(Type::Map(Box::new(k), Box::new(v)))
            }
            ExprKind::Template { .. } => Ok(Type::String),
        }
    }

    fn check_match_arm(
        &mut self,
        env: Rc<RefCell<TypeEnv>>,
        scrutinee: &Type,
        arm: &MatchArm,
    ) -> Result<Type, TypeError> {
        let bindings = self.check_pattern_bindings(scrutinee, &arm.pattern)?;
        let child = Rc::new(RefCell::new(TypeEnv::with_parent(env)));
        for (name, ty) in bindings {
            child.borrow_mut().define(name, ty, false);
        }
        self.check_block(child, &arm.body)
    }

    fn check_pattern_bindings(
        &self,
        scrutinee: &Type,
        p: &Pattern,
    ) -> Result<Vec<(String, Type)>, TypeError> {
        let st = self.resolve_type(scrutinee);
        match p {
            Pattern::Wildcard => Ok(Vec::new()),
            Pattern::Ident(name) => Ok(vec![(name.clone(), st)]),
            Pattern::Literal(l) => {
                let pt = self.type_of_literal(l)?;
                let _ = self.unify(st, pt)?;
                Ok(Vec::new())
            }
            Pattern::StructLiteral { name, fields: pat_fields } => {
                let Some(Type::Struct { name: sn, fields: def_fields }) = self.structs.get(name) else {
                    return Err(TypeError(format!("unknown struct `{}`", name)));
                };
                let _ = self.unify(
                    st,
                    Type::Struct {
                        name: sn.clone(),
                        fields: def_fields.clone(),
                    },
                )?;
                let mut out = Vec::new();
                for (fname, pat) in pat_fields {
                    let ft = def_fields
                        .get(fname)
                        .ok_or_else(|| TypeError(format!("unknown field `{}` in pattern", fname)))?
                        .clone();
                    out.extend(self.check_pattern_bindings(&ft, pat)?);
                }
                Ok(out)
            }
            Pattern::Variant { enum_name, variant, inner } => {
                if enum_name == "Option" {
                    let inner_ty = match st {
                        Type::Option(t) => *t,
                        Type::Unknown => Type::Unknown,
                        _ => {
                            return Err(TypeError("pattern expects Option".into()));
                        }
                    };
                    let _ = self.unify(
                        scrutinee.clone(),
                        Type::Option(Box::new(inner_ty.clone())),
                    )?;
                    if variant == "Some" {
                        if let Some(pat) = inner {
                            return Ok(self.check_pattern_bindings(&inner_ty, pat)?);
                        }
                        return Ok(Vec::new());
                    }
                    if variant == "None" {
                        return Ok(Vec::new());
                    }
                    return Err(TypeError(format!(
                        "unknown variant `{}` for enum `Option`",
                        variant
                    )));
                }
                if enum_name == "Result" {
                    let (ok_ty, err_ty) = match st {
                        Type::Result(ok, err) => (*ok, *err),
                        Type::Unknown => (Type::Unknown, Type::Unknown),
                        _ => {
                            return Err(TypeError("pattern expects Result".into()));
                        }
                    };
                    let _ = self.unify(
                        scrutinee.clone(),
                        Type::Result(Box::new(ok_ty.clone()), Box::new(err_ty.clone())),
                    )?;
                    if variant == "Ok" {
                        if let Some(pat) = inner {
                            return Ok(self.check_pattern_bindings(&ok_ty, pat)?);
                        }
                        return Ok(Vec::new());
                    }
                    if variant == "Err" {
                        if let Some(pat) = inner {
                            return Ok(self.check_pattern_bindings(&err_ty, pat)?);
                        }
                        return Ok(Vec::new());
                    }
                    return Err(TypeError(format!(
                        "unknown variant `{}` for enum `Result`",
                        variant
                    )));
                }

                let Some(Type::Enum { variants, name }) = self.enums.get(enum_name) else {
                    return Err(TypeError(format!("unknown enum `{}`", enum_name)));
                };
                let v = variants
                    .iter()
                    .find(|v| v.name == *variant)
                    .ok_or_else(|| {
                        TypeError(format!(
                            "unknown variant `{}` for enum `{}`",
                            variant, enum_name
                        ))
                    })?;
                let _ = self.unify(
                    st,
                    Type::Enum {
                        name: name.clone(),
                        variants: variants.clone(),
                    },
                )?;
                match (&v.data, inner) {
                    (Some(dt), Some(pat)) => Ok(self.check_pattern_bindings(dt, pat)?),
                    (None, None) => Ok(Vec::new()),
                    (Some(_), None) => Ok(Vec::new()),
                    (None, Some(_)) => Err(TypeError(format!(
                        "variant `{}`::`{}` has no data",
                        enum_name, variant
                    ))),
                }
            }
        }
    }

    fn type_of_literal(&self, l: &Literal) -> Result<Type, TypeError> {
        Ok(match l {
            Literal::Int(_) => Type::Int,
            Literal::Float(_) => Type::Float,
            Literal::Bool(_) => Type::Bool,
            Literal::Char(_) => Type::Char,
            Literal::String(_) => Type::String,
            Literal::Unit => Type::Unit,
            Literal::None => Type::Option(Box::new(Type::Unknown)),
            Literal::Some(_) => Type::Option(Box::new(Type::Unknown)),
            Literal::Ok(_) => Type::Result(Box::new(Type::Unknown), Box::new(Type::Unknown)),
            Literal::Err(_) => Type::Result(Box::new(Type::Unknown), Box::new(Type::Unknown)),
        })
    }

    fn check_match_exhaustive(&self, scrutinee: &Type, arms: &[MatchArm]) -> Result<(), TypeError> {
        // NOTE: Basit exhaustiveness kontrolu. Wildcard/ident varsa yeterli sayilir.
        for arm in arms {
            match arm.pattern {
                Pattern::Wildcard | Pattern::Ident(_) => return Ok(()),
                _ => {}
            }
        }

        let st = self.resolve_type(scrutinee);
        match st {
            Type::Option(_) => {
                let mut has_some = false;
                let mut has_none = false;
                for arm in arms {
                    match &arm.pattern {
                        Pattern::Literal(Literal::None) => has_none = true,
                        Pattern::Variant { enum_name, variant, .. }
                            if enum_name == "Option" && variant == "Some" =>
                        {
                            has_some = true
                        }
                        _ => {}
                    }
                }
                if has_some && has_none {
                    Ok(())
                } else {
                    Err(TypeError("non-exhaustive match on Option".into()))
                }
            }
            Type::Result(_, _) => {
                let mut has_ok = false;
                let mut has_err = false;
                for arm in arms {
                    match &arm.pattern {
                        Pattern::Variant { enum_name, variant, .. }
                            if enum_name == "Result" && variant == "Ok" =>
                        {
                            has_ok = true
                        }
                        Pattern::Variant { enum_name, variant, .. }
                            if enum_name == "Result" && variant == "Err" =>
                        {
                            has_err = true
                        }
                        _ => {}
                    }
                }
                if has_ok && has_err {
                    Ok(())
                } else {
                    Err(TypeError("non-exhaustive match on Result".into()))
                }
            }
            Type::Enum { name, variants } => {
                let all_variants: Vec<String> = if variants.is_empty() {
                    self.enums
                        .get(&name)
                        .and_then(|t| match t {
                            Type::Enum { variants, .. } => Some(
                                variants.iter().map(|v| v.name.clone()).collect::<Vec<_>>(),
                            ),
                            _ => None,
                        })
                        .unwrap_or_default()
                } else {
                    variants.iter().map(|v| v.name.clone()).collect()
                };
                if all_variants.is_empty() {
                    return Ok(());
                }
                let mut seen = std::collections::HashSet::new();
                for arm in arms {
                    if let Pattern::Variant { enum_name, variant, .. } = &arm.pattern {
                        if enum_name == &name {
                            seen.insert(variant.clone());
                        }
                    }
                }
                let all: std::collections::HashSet<_> = all_variants.into_iter().collect();
                if seen == all {
                    Ok(())
                } else {
                    Err(TypeError(format!(
                        "non-exhaustive match on enum `{}`",
                        name
                    )))
                }
            }
            _ => Ok(()),
        }
    }

    fn resolve_type(&self, t: &Type) -> Type {
        match t {
            Type::Struct { name, .. } => self
                .structs
                .get(name)
                .cloned()
                .unwrap_or_else(|| t.clone()),
            Type::Enum { name, .. } => self
                .enums
                .get(name)
                .cloned()
                .unwrap_or_else(|| t.clone()),
            _ => t.clone(),
        }
    }

    fn type_of_binop(&self, op: BinOp, l: Type, r: Type) -> Result<Type, TypeError> {
        use crate::ast::BinOp::*;
        match op {
            Add | Sub | Mul | Div | Rem => {
                let t = self.unify(l, r)?;
                match t {
                    Type::Int | Type::Float | Type::Unknown => Ok(t),
                    Type::String if matches!(op, Add) => Ok(Type::String),
                    _ => Err(TypeError("numeric operator on non-number".into())),
                }
            }
            Eq | Ne => {
                let _ = self.unify(l, r)?;
                Ok(Type::Bool)
            }
            Lt | Le | Gt | Ge => {
                let t = self.unify(l, r)?;
                match t {
                    Type::Int | Type::Float | Type::Unknown => Ok(Type::Bool),
                    _ => Err(TypeError("comparison on non-number".into())),
                }
            }
            And | Or => {
                self.expect_bool(l)?;
                self.expect_bool(r)?;
                Ok(Type::Bool)
            }
        }
    }

    fn type_of_unop(&self, op: UnaryOp, v: Type) -> Result<Type, TypeError> {
        use crate::ast::UnaryOp::*;
        match op {
            Neg => match v {
                Type::Int | Type::Float | Type::Unknown => Ok(v),
                _ => Err(TypeError("negation on non-number".into())),
            },
            Not => {
                self.expect_bool(v)?;
                Ok(Type::Bool)
            }
        }
    }

    fn expect_bool(&self, t: Type) -> Result<(), TypeError> {
        match t {
            Type::Bool | Type::Unknown => Ok(()),
            _ => Err(TypeError("expected Bool".into())),
        }
    }

    fn const_int(&self, e: &Expr) -> Option<i64> {
        match self.const_eval(e)? {
            ConstVal::Int(i) => Some(i),
            _ => None,
        }
    }

    fn const_bool(&self, e: &Expr) -> Option<bool> {
        match self.const_eval(e)? {
            ConstVal::Bool(b) => Some(b),
            _ => None,
        }
    }

    fn const_eval(&self, e: &Expr) -> Option<ConstVal> {
        match &e.node {
            ExprKind::Literal(lit) => match lit {
                Literal::Int(i) => Some(ConstVal::Int(*i)),
                Literal::Float(f) => Some(ConstVal::Float(*f)),
                Literal::Bool(b) => Some(ConstVal::Bool(*b)),
                Literal::Char(c) => Some(ConstVal::Char(*c)),
                Literal::String(s) => Some(ConstVal::Str(s.clone())),
                _ => None,
            },
            ExprKind::Unary { op, inner } => {
                let v = self.const_eval(inner)?;
                match (op, v) {
                    (UnaryOp::Neg, ConstVal::Int(i)) => Some(ConstVal::Int(-i)),
                    (UnaryOp::Neg, ConstVal::Float(f)) => Some(ConstVal::Float(-f)),
                    (UnaryOp::Not, ConstVal::Bool(b)) => Some(ConstVal::Bool(!b)),
                    _ => None,
                }
            }
            ExprKind::Binary { op, left, right } => {
                let l = self.const_eval(left)?;
                let r = self.const_eval(right)?;
                match (op, l, r) {
                    (BinOp::Add, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a + b)),
                    (BinOp::Sub, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a - b)),
                    (BinOp::Mul, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a * b)),
                    (BinOp::Div, ConstVal::Int(a), ConstVal::Int(b)) => {
                        if b == 0 { None } else { Some(ConstVal::Int(a / b)) }
                    }
                    (BinOp::Rem, ConstVal::Int(a), ConstVal::Int(b)) => {
                        if b == 0 { None } else { Some(ConstVal::Int(a % b)) }
                    }
                    (BinOp::Add, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a + b)),
                    (BinOp::Sub, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a - b)),
                    (BinOp::Mul, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Float(a * b)),
                    (BinOp::Div, ConstVal::Float(a), ConstVal::Float(b)) => {
                        if b == 0.0 { None } else { Some(ConstVal::Float(a / b)) }
                    }
                    (BinOp::Rem, ConstVal::Float(a), ConstVal::Float(b)) => {
                        if b == 0.0 { None } else { Some(ConstVal::Float(a % b)) }
                    }
                    (BinOp::Add, ConstVal::Str(a), ConstVal::Str(b)) => {
                        Some(ConstVal::Str(format!("{}{}", a, b)))
                    }
                    (BinOp::And, ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a && b)),
                    (BinOp::Or, ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a || b)),
                    (BinOp::Eq, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Char(a), ConstVal::Char(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Str(a), ConstVal::Str(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Ne, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Char(a), ConstVal::Char(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Str(a), ConstVal::Str(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Lt, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a < b)),
                    (BinOp::Le, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a <= b)),
                    (BinOp::Gt, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a > b)),
                    (BinOp::Ge, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a >= b)),
                    (BinOp::Lt, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a < b)),
                    (BinOp::Le, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a <= b)),
                    (BinOp::Gt, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a > b)),
                    (BinOp::Ge, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a >= b)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn warn(&mut self, span: &Span, msg: &str) {
        let pos = self
            .source
            .as_ref()
            .map(|src| line_col(src, span.lo));
        self.warnings.push(TypeWarning {
            message: msg.to_string(),
            pos,
        });
    }

    fn apply_annotation(&self, inferred: Type, ann: Option<&Type>) -> Result<Type, TypeError> {
        if let Some(t) = ann {
            self.unify(inferred, t.clone())
        } else {
            Ok(inferred)
        }
    }

    fn unify(&self, a: Type, b: Type) -> Result<Type, TypeError> {
        if a == b {
            return Ok(a);
        }
        match (a, b) {
            (Type::Unknown, t) | (t, Type::Unknown) => Ok(t),
            (Type::Option(a), Type::Option(b)) => {
                let inner = self.unify(*a, *b)?;
                Ok(Type::Option(Box::new(inner)))
            }
            (Type::Result(a1, a2), Type::Result(b1, b2)) => {
                let ok = self.unify(*a1, *b1)?;
                let err = self.unify(*a2, *b2)?;
                Ok(Type::Result(Box::new(ok), Box::new(err)))
            }
            (Type::List(a), Type::List(b)) => {
                let inner = self.unify(*a, *b)?;
                Ok(Type::List(Box::new(inner)))
            }
            (Type::Array(a, n1), Type::Array(b, n2)) if n1 == n2 => {
                let inner = self.unify(*a, *b)?;
                Ok(Type::Array(Box::new(inner), n1))
            }
            (Type::Map(ka, va), Type::Map(kb, vb)) => {
                let k = self.unify(*ka, *kb)?;
                let v = self.unify(*va, *vb)?;
                Ok(Type::Map(Box::new(k), Box::new(v)))
            }
            (Type::Fn(pa, ra), Type::Fn(pb, rb)) if pa.len() == pb.len() => {
                for (a, b) in pa.iter().cloned().zip(pb.iter().cloned()) {
                    let _ = self.unify(a, b)?;
                }
                let r = self.unify(*ra, *rb)?;
                let params = if pa.is_empty() { pb } else { pa };
                Ok(Type::Fn(params, Box::new(r)))
            }
            (Type::Struct { name: a, fields: fa }, Type::Struct { name: b, fields: fb }) if a == b => {
                let fields = if fa.is_empty() { fb } else { fa };
                Ok(Type::Struct { name: a, fields })
            }
            (Type::Enum { name: a, variants: va }, Type::Enum { name: b, variants: vb }) if a == b => {
                let variants = if va.is_empty() { vb } else { va };
                Ok(Type::Enum { name: a, variants })
            }
            (a, b) => Err(TypeError(format!("type mismatch: {:?} vs {:?}", a, b))),
        }
    }

    fn native_return_type(&self, name: &str) -> Type {
        match name {
            "print" | "debug" | "return" => Type::Unit,
            "input" => Type::String,
            _ => Type::Unknown,
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
