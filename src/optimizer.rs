//! Compile-time optimizer: const propagation, folding, and dead code pruning.

use alloc::string::String;
use alloc::vec::Vec;
use crate::collections::HashMap;

use crate::ast::*;

#[derive(Clone, Debug, PartialEq)]
enum ConstVal {
    Int(i64),
    UInt(u64),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
    Unit,
    Tuple(Vec<ConstVal>),
    List(Vec<ConstVal>),
    Array(Vec<ConstVal>),
    Map(Vec<(ConstVal, ConstVal)>),
}

pub fn optimize_program(program: &mut Program) {
    let mut opt = Optimizer::new();
    for item in &mut program.items {
        opt.optimize_item(item);
    }
}

struct Optimizer {
    scopes: Vec<HashMap<String, ConstVal>>,
}

impl Optimizer {
    fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn set_const(&mut self, name: String, val: ConstVal) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, val);
        }
    }

    fn unset_const(&mut self, name: &str) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.remove(name).is_some() {
                break;
            }
        }
    }

    fn get_const(&self, name: &str) -> Option<ConstVal> {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v.clone());
            }
        }
        None
    }

    fn optimize_item(&mut self, item: &mut Item) {
        match item {
            Item::FnDef(def) => {
                self.push_scope();
                for (name, _) in &def.params {
                    self.unset_const(name);
                }
                for s in &mut def.body {
                    self.optimize_stmt(s);
                }
                self.pop_scope();
            }
            Item::GlobalLet(b) => {
                self.optimize_expr(&mut b.init);
                if let Some(cv) = self.const_eval(&b.init) {
                    self.set_const(b.name.clone(), cv);
                }
            }
            Item::GlobalVar(b) => {
                self.optimize_expr(&mut b.init);
                self.unset_const(&b.name);
            }
            Item::TopLevelStmt(s) => self.optimize_stmt(s),
            Item::StructDef(_) | Item::EnumDef(_) | Item::ModuleDecl(_) | Item::TypeAlias(_) => {}
            Item::PropertyDef(def) => {
                self.optimize_expr(&mut def.default);
                self.push_scope();
                self.unset_const(&def.getter.value_param);
                self.optimize_expr(&mut def.getter.body);
                self.pop_scope();
                if let Some(setter) = def.setter.as_mut() {
                    self.push_scope();
                    self.unset_const(&setter.value_param);
                    self.unset_const(&setter.input_param);
                    self.optimize_expr(&mut setter.body);
                    self.pop_scope();
                }
            }
        }
    }

    fn optimize_stmt(&mut self, stmt: &mut Stmt) {
        match &mut stmt.node {
            StmtKind::Let(b) => {
                self.optimize_expr(&mut b.init);
                if let Some(cv) = self.const_eval(&b.init) {
                    self.set_const(b.name.clone(), cv);
                }
            }
            StmtKind::Var(b) => {
                self.optimize_expr(&mut b.init);
                self.unset_const(&b.name);
            }
            StmtKind::Assign { name, value } => {
                self.optimize_expr(value);
                self.unset_const(name);
            }
            StmtKind::AssignIndex { base, index, value } => {
                self.optimize_expr(base);
                self.optimize_expr(index);
                self.optimize_expr(value);
            }
            StmtKind::Expr(e) => {
                self.optimize_expr(e);
            }
            StmtKind::If { cond, then_b, else_b } => {
                self.optimize_expr(cond);
                if let Some(ConstVal::Bool(b)) = self.const_eval(cond) {
                    let body = if b {
                        then_b.clone()
                    } else {
                        else_b.clone().unwrap_or_default()
                    };
                    stmt.node = StmtKind::Expr(Expr {
                        node: ExprKind::Block(body),
                        span: stmt.span.clone(),
                    });
                    self.optimize_stmt(stmt);
                    return;
                }
                self.push_scope();
                for s in then_b {
                    self.optimize_stmt(s);
                }
                self.pop_scope();
                if let Some(eb) = else_b {
                    self.push_scope();
                    for s in eb {
                        self.optimize_stmt(s);
                    }
                    self.pop_scope();
                }
            }
            StmtKind::Loop(body) => {
                self.push_scope();
                for s in body {
                    self.optimize_stmt(s);
                }
                self.pop_scope();
            }
            StmtKind::Match { scrutinee, arms } => {
                self.optimize_expr(scrutinee);
                for arm in arms.iter_mut() {
                    self.push_scope();
                    for s in &mut arm.body {
                        self.optimize_stmt(s);
                    }
                    self.pop_scope();
                }
                if let Some(cv) = self.const_eval(scrutinee) {
                    if let Some(arm) = find_const_match_arm(arms, &cv) {
                        let body = arm.body.clone();
                        stmt.node = StmtKind::Expr(Expr {
                            node: ExprKind::Block(body),
                            span: stmt.span.clone(),
                        });
                        self.optimize_stmt(stmt);
                    }
                }
            }
            StmtKind::Return(expr) => {
                if let Some(e) = expr {
                    self.optimize_expr(e);
                }
            }
            StmtKind::Break | StmtKind::Continue => {}
        }
    }

    fn optimize_expr(&mut self, expr: &mut Expr) {
        match &mut expr.node {
            ExprKind::Literal(_) => {}
            ExprKind::Ident(name) => {
                if let Some(cv) = self.get_const(name) {
                    *expr = const_to_expr(cv, expr.span.clone());
                }
            }
            ExprKind::NativeCall(_, args) => {
                for a in args {
                    self.optimize_expr(a);
                }
            }
            ExprKind::Binary { left, right, .. } => {
                self.optimize_expr(left);
                self.optimize_expr(right);
            }
            ExprKind::Unary { inner, .. } => self.optimize_expr(inner),
            ExprKind::Call { callee, args } => {
                self.optimize_expr(callee);
                for a in args {
                    self.optimize_expr(a);
                }
            }
            ExprKind::Block(stmts) => {
                self.push_scope();
                for s in stmts {
                    self.optimize_stmt(s);
                }
                self.pop_scope();
            }
            ExprKind::If { cond, then_b, else_b } => {
                self.optimize_expr(cond);
                if let Some(ConstVal::Bool(b)) = self.const_eval(cond) {
                    let body = if b {
                        then_b.clone()
                    } else {
                        else_b.clone().unwrap_or_default()
                    };
                    *expr = Expr {
                        node: ExprKind::Block(body),
                        span: expr.span.clone(),
                    };
                    self.optimize_expr(expr);
                    return;
                }
                self.push_scope();
                for s in then_b {
                    self.optimize_stmt(s);
                }
                self.pop_scope();
                if let Some(eb) = else_b {
                    self.push_scope();
                    for s in eb {
                        self.optimize_stmt(s);
                    }
                    self.pop_scope();
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.optimize_expr(scrutinee);
                for arm in arms.iter_mut() {
                    self.push_scope();
                    for s in &mut arm.body {
                        self.optimize_stmt(s);
                    }
                    self.pop_scope();
                }
                if let Some(cv) = self.const_eval(scrutinee) {
                    if let Some(arm) = find_const_match_arm(arms, &cv) {
                        let mut body = arm.body.clone();
                        *expr = Expr {
                            node: ExprKind::Block(body.drain(..).collect()),
                            span: expr.span.clone(),
                        };
                        self.optimize_expr(expr);
                    }
                }
            }
            ExprKind::Lambda { params, body } => {
                self.push_scope();
                for (name, _) in params {
                    self.unset_const(name);
                }
                self.optimize_expr(body);
                self.pop_scope();
            }
            ExprKind::StructLiteral { fields, .. } => {
                for (_, v) in fields {
                    self.optimize_expr(v);
                }
            }
            ExprKind::VariantLiteral { data, .. } => {
                if let Some(d) = data {
                    self.optimize_expr(d);
                }
            }
            ExprKind::FieldAccess { base, .. } => self.optimize_expr(base),
            ExprKind::Index { base, index } => {
                self.optimize_expr(base);
                self.optimize_expr(index);
            }
            ExprKind::ListLiteral(elems)
            | ExprKind::ArrayLiteral(elems)
            | ExprKind::TupleLiteral(elems) => {
                for e in elems {
                    self.optimize_expr(e);
                }
            }
            ExprKind::MapLiteral(pairs) => {
                for (k, v) in pairs {
                    self.optimize_expr(k);
                    self.optimize_expr(v);
                }
            }
            ExprKind::Template { parts: _ } => {}
        }

        if let Some(cv) = self.const_eval(expr) {
            *expr = const_to_expr(cv, expr.span.clone());
        }
    }

    fn const_eval(&self, e: &Expr) -> Option<ConstVal> {
        match &e.node {
            ExprKind::Literal(lit) => match lit {
                Literal::Int(i) => Some(ConstVal::Int(*i)),
                Literal::UInt(u) => Some(ConstVal::UInt(*u)),
                Literal::Float(f) => Some(ConstVal::Float(*f)),
                Literal::Bool(b) => Some(ConstVal::Bool(*b)),
                Literal::Char(c) => Some(ConstVal::Char(*c)),
                Literal::String(s) => Some(ConstVal::Str(s.clone())),
                Literal::Unit => Some(ConstVal::Unit),
                _ => None,
            },
            ExprKind::Ident(name) => self.get_const(name),
            ExprKind::TupleLiteral(elems) => {
                let mut out = Vec::with_capacity(elems.len());
                for e in elems {
                    out.push(self.const_eval(e)?);
                }
                Some(ConstVal::Tuple(out))
            }
            ExprKind::ListLiteral(elems) => {
                let mut out = Vec::with_capacity(elems.len());
                for e in elems {
                    out.push(self.const_eval(e)?);
                }
                Some(ConstVal::List(out))
            }
            ExprKind::ArrayLiteral(elems) => {
                let mut out = Vec::with_capacity(elems.len());
                for e in elems {
                    out.push(self.const_eval(e)?);
                }
                Some(ConstVal::Array(out))
            }
            ExprKind::MapLiteral(pairs) => {
                let mut out = Vec::with_capacity(pairs.len());
                for (k, v) in pairs {
                    out.push((self.const_eval(k)?, self.const_eval(v)?));
                }
                Some(ConstVal::Map(out))
            }
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
                    (BinOp::Add, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::UInt(a + b)),
                    (BinOp::Sub, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a - b)),
                    (BinOp::Sub, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::UInt(a - b)),
                    (BinOp::Mul, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Int(a * b)),
                    (BinOp::Mul, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::UInt(a * b)),
                    (BinOp::Div, ConstVal::Int(a), ConstVal::Int(b)) => {
                        if b == 0 { None } else { Some(ConstVal::Int(a / b)) }
                    }
                    (BinOp::Rem, ConstVal::Int(a), ConstVal::Int(b)) => {
                        if b == 0 { None } else { Some(ConstVal::Int(a % b)) }
                    }
                    (BinOp::Div, ConstVal::UInt(a), ConstVal::UInt(b)) => {
                        if b == 0 { None } else { Some(ConstVal::UInt(a / b)) }
                    }
                    (BinOp::Rem, ConstVal::UInt(a), ConstVal::UInt(b)) => {
                        if b == 0 { None } else { Some(ConstVal::UInt(a % b)) }
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
                    (BinOp::Eq, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Char(a), ConstVal::Char(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Eq, ConstVal::Str(a), ConstVal::Str(b)) => Some(ConstVal::Bool(a == b)),
                    (BinOp::Ne, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Float(a), ConstVal::Float(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Bool(a), ConstVal::Bool(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Char(a), ConstVal::Char(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Ne, ConstVal::Str(a), ConstVal::Str(b)) => Some(ConstVal::Bool(a != b)),
                    (BinOp::Lt, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a < b)),
                    (BinOp::Lt, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::Bool(a < b)),
                    (BinOp::Le, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a <= b)),
                    (BinOp::Le, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::Bool(a <= b)),
                    (BinOp::Gt, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a > b)),
                    (BinOp::Gt, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::Bool(a > b)),
                    (BinOp::Ge, ConstVal::Int(a), ConstVal::Int(b)) => Some(ConstVal::Bool(a >= b)),
                    (BinOp::Ge, ConstVal::UInt(a), ConstVal::UInt(b)) => Some(ConstVal::Bool(a >= b)),
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
}

fn find_const_match_arm<'a>(arms: &'a [MatchArm], cv: &ConstVal) -> Option<&'a MatchArm> {
    for arm in arms {
        if pattern_matches_const(&arm.pattern, cv) {
            return Some(arm);
        }
    }
    None
}

fn pattern_matches_const(p: &Pattern, cv: &ConstVal) -> bool {
    match p {
        Pattern::Wildcard => true,
        Pattern::Ident(_) => true,
        Pattern::Literal(lit) => match (lit, cv) {
            (Literal::Int(a), ConstVal::Int(b)) => *a == *b,
            (Literal::UInt(a), ConstVal::UInt(b)) => *a == *b,
            (Literal::Float(a), ConstVal::Float(b)) => *a == *b,
            (Literal::Bool(a), ConstVal::Bool(b)) => *a == *b,
            (Literal::Char(a), ConstVal::Char(b)) => *a == *b,
            (Literal::String(a), ConstVal::Str(b)) => a == b,
            (Literal::Unit, ConstVal::Unit) => true,
            _ => false,
        },
        _ => false,
    }
}

fn const_to_expr(cv: ConstVal, span: Span) -> Expr {
    match cv {
        ConstVal::Int(i) => Expr { node: ExprKind::Literal(Literal::Int(i)), span },
        ConstVal::UInt(u) => Expr { node: ExprKind::Literal(Literal::UInt(u)), span },
        ConstVal::Float(f) => Expr { node: ExprKind::Literal(Literal::Float(f)), span },
        ConstVal::Bool(b) => Expr { node: ExprKind::Literal(Literal::Bool(b)), span },
        ConstVal::Char(c) => Expr { node: ExprKind::Literal(Literal::Char(c)), span },
        ConstVal::Str(s) => Expr { node: ExprKind::Literal(Literal::String(s)), span },
        ConstVal::Unit => Expr { node: ExprKind::Literal(Literal::Unit), span },
        ConstVal::Tuple(items) => {
            let elems = items.into_iter().map(|v| const_to_expr(v, span.clone())).collect();
            Expr { node: ExprKind::TupleLiteral(elems), span }
        }
        ConstVal::List(items) => {
            let elems = items.into_iter().map(|v| const_to_expr(v, span.clone())).collect();
            Expr { node: ExprKind::ListLiteral(elems), span }
        }
        ConstVal::Array(items) => {
            let elems = items.into_iter().map(|v| const_to_expr(v, span.clone())).collect();
            Expr { node: ExprKind::ArrayLiteral(elems), span }
        }
        ConstVal::Map(items) => {
            let pairs = items
                .into_iter()
                .map(|(k, v)| (const_to_expr(k, span.clone()), const_to_expr(v, span.clone())))
                .collect();
            Expr { node: ExprKind::MapLiteral(pairs), span }
        }
    }
}
