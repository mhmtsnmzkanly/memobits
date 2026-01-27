//! AST: soyut sözdizim ağacı tanımları.

use crate::types::Type;

#[derive(Clone, Debug)]
pub struct Program {
    pub items: Vec<Item>,
}

#[derive(Clone, Debug)]
pub enum Item {
    StructDef(StructDef),
    EnumDef(EnumDef),
    FnDef(FnDef),
    GlobalLet(LetBinding),
    GlobalVar(VarBinding),
    TopLevelStmt(Stmt),
}

#[derive(Clone, Debug)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<(String, Type)>,
}

#[derive(Clone, Debug)]
pub struct EnumDef {
    pub name: String,
    pub variants: Vec<EnumVariantDef>,
}

#[derive(Clone, Debug)]
pub struct EnumVariantDef {
    pub name: String,
    pub data: Option<Type>,
}

#[derive(Clone, Debug)]
pub struct FnDef {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub struct LetBinding {
    pub name: String,
    pub typ: Option<Type>,
    pub init: Expr,
}

#[derive(Clone, Debug)]
pub struct VarBinding {
    pub name: String,
    pub typ: Option<Type>,
    pub init: Expr,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Let(LetBinding),
    Var(VarBinding),
    Assign { name: String, value: Expr },
    Expr(Expr),
    If { cond: Expr, then_b: Vec<Stmt>, else_b: Option<Vec<Stmt>> },
    Loop(Vec<Stmt>),
    Match { scrutinee: Expr, arms: Vec<MatchArm> },
    Break,
    Continue,
}

#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard,
    Ident(String),
    StructLiteral { name: String, fields: Vec<(String, Pattern)> },
    Variant { enum_name: String, variant: String, inner: Option<Box<Pattern>> },
    Literal(Literal),
}

#[derive(Clone, Debug)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    String(String),
    Unit,
    None,
    Some(Box<Expr>),
    Ok(Box<Expr>),
    Err(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Literal(Literal),
    Ident(String),
    NativeCall(String, Vec<Expr>),
    Binary { op: BinOp, left: Box<Expr>, right: Box<Expr> },
    Unary { op: UnaryOp, inner: Box<Expr> },
    Call { callee: Box<Expr>, args: Vec<Expr> },
    Block(Vec<Stmt>),
    If { cond: Box<Expr>, then_b: Vec<Stmt>, else_b: Option<Vec<Stmt>> },
    Match { scrutinee: Box<Expr>, arms: Vec<MatchArm> },
    Lambda { params: Vec<(String, Option<Type>)>, body: Box<Expr> },
    StructLiteral { name: String, fields: Vec<(String, Expr)> },
    VariantLiteral { enum_name: String, variant: String, data: Option<Box<Expr>> },
    FieldAccess { base: Box<Expr>, field: String },
    Index { base: Box<Expr>, index: Box<Expr> },
    ListLiteral(Vec<Expr>),
    ArrayLiteral(Vec<Expr>),
    MapLiteral(Vec<(Expr, Expr)>),
    Template { parts: Vec<TemplatePart> },
}

#[derive(Clone, Debug)]
pub enum TemplatePart {
    Lit(String),
    Interp(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}
