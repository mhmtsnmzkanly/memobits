//! Parser: token akışı → AST.

use std::iter::Peekable;
use std::vec::IntoIter;

use crate::ast::*;
use crate::lexer::{Span, Token};
use crate::types::Type;

type TokenStream = Peekable<IntoIter<(Token, Span)>>;

#[derive(Debug)]
pub struct ParseError(pub String, pub Option<Span>);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "parse error: {}", self.0)
    }
}

impl std::error::Error for ParseError {}

pub struct Parser {
    tokens: TokenStream,
    last_span: Span,
    errs: Vec<ParseError>,
}

impl Parser {
    pub fn new(tokens: Vec<(Token, Span)>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            last_span: Span { lo: 0, hi: 0 },
            errs: Vec::new(),
        }
    }

    fn peek(&mut self) -> Option<&Token> {
        self.tokens.peek().map(|(t, _)| t)
    }

    fn advance(&mut self) -> Option<(Token, Span)> {
        let next = self.tokens.next()?;
        self.last_span = next.1.clone();
        Some(next)
    }

    fn expect(&mut self, want: Token) -> Result<Span, ()> {
        let (t, span) = self
            .advance()
            .ok_or_else(|| self.err(format!("expected {:?}, got eof", want)))?;
        if std::mem::discriminant(&t) != std::mem::discriminant(&want) {
            self.err(format!("expected {:?}, got {:?}", want, t));
            return Err(());
        }
        Ok(span)
    }

    fn err(&mut self, msg: String) {
        self.errs.push(ParseError(msg, Some(self.last_span.clone())));
    }

    fn is(&mut self, t: &Token) -> bool {
        match (self.peek(), t) {
            (Some(a), b) => std::mem::discriminant(a) == std::mem::discriminant(b),
            _ => false,
        }
    }

    fn eat(&mut self, t: &Token) -> bool {
        if self.is(t) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn peek_ident(&mut self) -> Option<String> {
        match self.peek() {
            Some(Token::Ident(s)) => Some(s.clone()),
            _ => None,
        }
    }

    fn eat_ident_eq(&mut self, s: &str) -> bool {
        if self.peek_ident().as_deref() == Some(s) {
            self.advance();
            true
        } else {
            false
        }
    }

    pub fn parse(mut self) -> Result<Program, Vec<ParseError>> {
        let mut items = Vec::new();
        while !self.is(&Token::Eof) {
            self.bump_while_semi();
            if self.is(&Token::Eof) {
                break;
            }
            match self.parse_item() {
                Some(it) => items.push(it),
                None => break,
            }
        }
        if !self.errs.is_empty() {
            return Err(self.errs);
        }
        Ok(Program { items })
    }

    fn bump_while_semi(&mut self) {
        while self.eat(&Token::Semi) {}
    }

    fn parse_item(&mut self) -> Option<Item> {
        if self.eat(&Token::Struct) {
            return Some(Item::StructDef(self.parse_struct_def()?));
        }
        if self.eat(&Token::Enum) {
            return Some(Item::EnumDef(self.parse_enum_def()?));
        }
        if self.eat(&Token::Fn) {
            return Some(Item::FnDef(self.parse_fn_def()?));
        }
        if self.eat(&Token::Let) {
            return Some(Item::GlobalLet(self.parse_let_binding()?));
        }
        if self.eat(&Token::Var) {
            return Some(Item::GlobalVar(self.parse_var_binding()?));
        }
        if let Some(s) = self.parse_stmt() {
            return Some(Item::TopLevelStmt(s));
        }
        None
    }

    fn parse_struct_def(&mut self) -> Option<StructDef> {
        let name = self.expect_ident()?;
        self.expect(Token::LBrace).ok()?;
        let mut fields = Vec::new();
        loop {
            self.bump_while_semi();
            if self.eat(&Token::RBrace) {
                break;
            }
            let fname = self.expect_ident()?;
            self.expect(Token::Colon).ok()?;
            let ty = self.parse_type()?;
            fields.push((fname, ty));
            self.bump_while_semi();
            if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                self.err("expected , or }".into());
                break;
            }
        }
        Some(StructDef { name, fields })
    }

    fn parse_enum_def(&mut self) -> Option<EnumDef> {
        let name = self.expect_ident()?;
        self.expect(Token::LBrace).ok()?;
        let mut variants = Vec::new();
        loop {
            self.bump_while_semi();
            if self.eat(&Token::RBrace) {
                break;
            }
            let vname = self.expect_ident()?;
            let data = if self.eat(&Token::LParen) {
                let ty = self.parse_type()?;
                self.expect(Token::RParen).ok()?;
                Some(ty)
            } else {
                None
            };
            variants.push(EnumVariantDef { name: vname, data });
            self.bump_while_semi();
            if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                break;
            }
        }
        Some(EnumDef { name, variants })
    }

    fn parse_fn_def(&mut self) -> Option<FnDef> {
        let name = self.expect_ident()?;
        self.expect(Token::LParen).ok()?;
        let mut params = Vec::new();
        loop {
            self.bump_while_semi();
            if self.eat(&Token::RParen) {
                break;
            }
            let pname = self.expect_ident()?;
            self.expect(Token::Colon).ok()?;
            let ty = self.parse_type()?;
            params.push((pname, ty));
            if !self.eat(&Token::Comma) && !self.is(&Token::RParen) {
                break;
            }
        }
        self.expect(Token::Arrow).ok()?;
        let ret = self.parse_type()?;
        self.expect(Token::LBrace).ok()?;
        let body = self.parse_block_stmts()?;
        self.expect(Token::RBrace).ok()?;
        Some(FnDef {
            name,
            params,
            ret,
            body,
        })
    }

    fn parse_let_binding(&mut self) -> Option<LetBinding> {
        let name = self.expect_ident()?;
        let typ = if self.eat(&Token::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect(Token::Eq).ok()?;
        let init = self.parse_expr()?;
        Some(LetBinding { name, typ, init })
    }

    fn parse_var_binding(&mut self) -> Option<VarBinding> {
        let name = self.expect_ident()?;
        let typ = if self.eat(&Token::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect(Token::Eq).ok()?;
        let init = self.parse_expr()?;
        Some(VarBinding { name, typ, init })
    }

    fn parse_block_stmts(&mut self) -> Option<Vec<Stmt>> {
        let mut stmts = Vec::new();
        loop {
            self.bump_while_semi();
            if self.is(&Token::RBrace) {
                break;
            }
            if let Some(s) = self.parse_stmt() {
                stmts.push(s);
            } else {
                break;
            }
        }
        Some(stmts)
    }

    fn parse_stmt(&mut self) -> Option<Stmt> {
        self.bump_while_semi();
        if self.eat(&Token::Let) {
            return Some(Stmt::Let(self.parse_let_binding()?));
        }
        if self.eat(&Token::Var) {
            return Some(Stmt::Var(self.parse_var_binding()?));
        }
        if self.eat(&Token::Break) {
            return Some(Stmt::Break);
        }
        if self.eat(&Token::Continue) {
            return Some(Stmt::Continue);
        }
        if self.eat(&Token::If) {
            let cond = self.parse_expr()?;
            self.expect(Token::LBrace).ok()?;
            let then_b = self.parse_block_stmts()?;
            self.expect(Token::RBrace).ok()?;
            let else_b = if self.eat(&Token::Else) {
                self.expect(Token::LBrace).ok()?;
                let b = self.parse_block_stmts()?;
                self.expect(Token::RBrace).ok()?;
                Some(b)
            } else {
                None
            };
            return Some(Stmt::If {
                cond,
                then_b,
                else_b,
            });
        }
        if self.eat(&Token::Loop) {
            self.expect(Token::LBrace).ok()?;
            let body = self.parse_block_stmts()?;
            self.expect(Token::RBrace).ok()?;
            return Some(Stmt::Loop(body));
        }
        if self.eat(&Token::Match) {
            let scrutinee = self.parse_expr()?;
            self.expect(Token::LBrace).ok()?;
            let mut arms = Vec::new();
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RBrace) {
                    break;
                }
                let pattern = self.parse_pattern()?;
                self.expect(Token::FatArrow).ok()?;
                let body = if self.is(&Token::LBrace) {
                    self.advance();
                    let b = self.parse_block_stmts()?;
                    self.expect(Token::RBrace).ok()?;
                    b
                } else {
                    let e = self.parse_expr()?;
                    vec![Stmt::Expr(e)]
                };
                arms.push(MatchArm { pattern, body });
                self.bump_while_semi();
                if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                    break;
                }
            }
            return Some(Stmt::Match { scrutinee, arms });
        }
        // Assign: ident = expr, or expression statement starting with ident
        if let Some(name) = self.peek_ident() {
            self.advance();
            if self.eat(&Token::Eq) {
                let value = self.parse_expr()?;
                return Some(Stmt::Assign { name, value });
            }
            return Some(Stmt::Expr(self.parse_expr_postfix(Some(Expr::Ident(name)))?));
        }
        // Expression statement
        let e = self.parse_expr()?;
        Some(Stmt::Expr(e))
    }

    fn parse_pattern(&mut self) -> Option<Pattern> {
        self.bump_while_semi();
        if self.eat_ident_eq("_") {
            return Some(Pattern::Wildcard);
        }
        if let Some(Token::IntLit(i)) = self.peek().cloned() {
            self.advance();
            return Some(Pattern::Literal(Literal::Int(i)));
        }
        if let Some(Token::FloatLit(f)) = self.peek().cloned() {
            self.advance();
            return Some(Pattern::Literal(Literal::Float(f)));
        }
        if self.eat(&Token::True) {
            return Some(Pattern::Literal(Literal::Bool(true)));
        }
        if self.eat(&Token::False) {
            return Some(Pattern::Literal(Literal::Bool(false)));
        }
        if self.eat(&Token::None) {
            return Some(Pattern::Literal(Literal::None));
        }
        if let Some(Token::Ident(ref name)) = self.peek() {
            let name = name.clone();
            self.advance();
            if self.eat(&Token::ColonColon) {
                let variant = self.expect_ident()?;
                let inner = if self.eat(&Token::LParen) {
                    let p = self.parse_pattern()?;
                    self.expect(Token::RParen).ok()?;
                    Some(Box::new(p))
                } else {
                    None
                };
                return Some(Pattern::Variant {
                    enum_name: name,
                    variant,
                    inner,
                });
            }
            if self.eat(&Token::LBrace) {
                let mut fields = Vec::new();
                loop {
                    self.bump_while_semi();
                    if self.eat(&Token::RBrace) {
                        break;
                    }
                    let f = self.expect_ident()?;
                    self.expect(Token::Colon).ok()?;
                    let pat = self.parse_pattern()?;
                    fields.push((f, pat));
                    if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                        break;
                    }
                }
                return Some(Pattern::StructLiteral {
                    name,
                    fields,
                });
            }
            return Some(Pattern::Ident(name));
        }
        self.err("expected pattern".into());
        None
    }

    fn expect_ident(&mut self) -> Option<String> {
        let (t, _) = self.advance().ok_or_else(|| { self.err("expected identifier".into()); }).ok()?;
        match t {
            Token::Ident(s) => Some(s),
            _ => {
                self.err("expected identifier".into());
                None
            }
        }
    }

    fn parse_type(&mut self) -> Option<Type> {
        if self.eat(&Token::IntKw) {
            return Some(Type::Int);
        }
        if self.eat(&Token::FloatKw) {
            return Some(Type::Float);
        }
        if self.eat(&Token::BoolKw) {
            return Some(Type::Bool);
        }
        if self.eat(&Token::CharKw) {
            return Some(Type::Char);
        }
        if self.eat(&Token::StringKw) {
            return Some(Type::String);
        }
        if self.eat(&Token::Option) {
            self.expect(Token::Lt).ok()?;
            let inner = self.parse_type()?;
            self.expect(Token::Gt).ok()?;
            return Some(Type::Option(Box::new(inner)));
        }
        if self.eat(&Token::Result) {
            self.expect(Token::Lt).ok()?;
            let ok = self.parse_type()?;
            self.expect(Token::Comma).ok()?;
            let err = self.parse_type()?;
            self.expect(Token::Gt).ok()?;
            return Some(Type::Result(Box::new(ok), Box::new(err)));
        }
        if self.eat(&Token::Array) {
            self.expect(Token::Lt).ok()?;
            let inner = self.parse_type()?;
            self.expect(Token::Comma).ok()?;
            let n = self.expect_int_lit()?;
            self.expect(Token::Gt).ok()?;
            return Some(Type::Array(Box::new(inner), n));
        }
        if self.eat(&Token::List) {
            self.expect(Token::Lt).ok()?;
            let inner = self.parse_type()?;
            self.expect(Token::Gt).ok()?;
            return Some(Type::List(Box::new(inner)));
        }
        if self.eat(&Token::Map) {
            self.expect(Token::Lt).ok()?;
            let k = self.parse_type()?;
            self.expect(Token::Comma).ok()?;
            let v = self.parse_type()?;
            self.expect(Token::Gt).ok()?;
            return Some(Type::Map(Box::new(k), Box::new(v)));
        }
        if self.eat(&Token::Fn) {
            self.expect(Token::LParen).ok()?;
            let mut params = Vec::new();
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RParen) {
                    break;
                }
                params.push(self.parse_type()?);
                if !self.eat(&Token::Comma) && !self.is(&Token::RParen) {
                    break;
                }
            }
            self.expect(Token::Arrow).ok()?;
            let ret = self.parse_type()?;
            return Some(Type::Fn(params, Box::new(ret)));
        }
        if let Some(Token::Ident(ref s)) = self.peek() {
            let name = s.clone();
            self.advance();
            return Some(Type::Struct {
                name,
                fields: std::collections::HashMap::new(),
            });
        }
        self.err("expected type".into());
        None
    }

    fn expect_int_lit(&mut self) -> Option<usize> {
        let (t, _) = self.advance().ok_or_else(|| { self.err("expected integer".into()); }).ok()?;
        match t {
            Token::IntLit(i) if i >= 0 => Some(i as usize),
            _ => {
                self.err("expected non-negative integer".into());
                None
            }
        }
    }

    fn parse_expr(&mut self) -> Option<Expr> {
        self.parse_expr_or()
    }

    fn parse_expr_or(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_expr_and()?;
        while self.eat(&Token::Or) {
            let rhs = self.parse_expr_and()?;
            lhs = Expr::Binary {
                op: BinOp::Or,
                left: Box::new(lhs),
                right: Box::new(rhs),
            };
        }
        Some(lhs)
    }

    fn parse_expr_and(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_expr_cmp()?;
        while self.eat(&Token::And) {
            let rhs = self.parse_expr_cmp()?;
            lhs = Expr::Binary {
                op: BinOp::And,
                left: Box::new(lhs),
                right: Box::new(rhs),
            };
        }
        Some(lhs)
    }

    fn parse_expr_cmp(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_expr_add()?;
        loop {
            let op = if self.eat(&Token::EqEq) {
                BinOp::Eq
            } else if self.eat(&Token::Ne) {
                BinOp::Ne
            } else if self.eat(&Token::Lt) {
                BinOp::Lt
            } else if self.eat(&Token::Le) {
                BinOp::Le
            } else if self.eat(&Token::Gt) {
                BinOp::Gt
            } else if self.eat(&Token::Ge) {
                BinOp::Ge
            } else {
                break;
            };
            let rhs = self.parse_expr_add()?;
            lhs = Expr::Binary {
                op,
                left: Box::new(lhs),
                right: Box::new(rhs),
            };
        }
        Some(lhs)
    }

    fn parse_expr_add(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_expr_mul()?;
        loop {
            let op = if self.eat(&Token::Plus) {
                BinOp::Add
            } else if self.eat(&Token::Minus) {
                BinOp::Sub
            } else {
                break;
            };
            let rhs = self.parse_expr_mul()?;
            lhs = Expr::Binary {
                op,
                left: Box::new(lhs),
                right: Box::new(rhs),
            };
        }
        Some(lhs)
    }

    fn parse_expr_mul(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_expr_unary()?;
        loop {
            let op = if self.eat(&Token::Star) {
                BinOp::Mul
            } else if self.eat(&Token::Slash) {
                BinOp::Div
            } else if self.eat(&Token::Percent) {
                BinOp::Rem
            } else {
                break;
            };
            let rhs = self.parse_expr_unary()?;
            lhs = Expr::Binary {
                op,
                left: Box::new(lhs),
                right: Box::new(rhs),
            };
        }
        Some(lhs)
    }

    fn parse_expr_unary(&mut self) -> Option<Expr> {
        if self.eat(&Token::Minus) {
            let inner = self.parse_expr_unary()?;
            return Some(Expr::Unary {
                op: UnaryOp::Neg,
                inner: Box::new(inner),
            });
        }
        if self.eat(&Token::Not) {
            let inner = self.parse_expr_unary()?;
            return Some(Expr::Unary {
                op: UnaryOp::Not,
                inner: Box::new(inner),
            });
        }
        self.parse_expr_postfix(None)
    }

    fn parse_expr_postfix(&mut self, initial: Option<Expr>) -> Option<Expr> {
        let mut e = match initial {
            Some(x) => x,
            None => self.parse_expr_primary()?,
        };
        loop {
            if self.eat(&Token::LParen) {
                let mut args = Vec::new();
                loop {
                    self.bump_while_semi();
                    if self.eat(&Token::RParen) {
                        break;
                    }
                    args.push(self.parse_expr()?);
                    if !self.eat(&Token::Comma) && !self.is(&Token::RParen) {
                        break;
                    }
                }
                e = Expr::Call {
                    callee: Box::new(e),
                    args,
                };
            } else if self.eat(&Token::Dot) {
                let field = self.expect_ident()?;
                e = Expr::FieldAccess {
                    base: Box::new(e),
                    field,
                };
            } else if self.eat(&Token::LBracket) {
                let index = self.parse_expr()?;
                self.expect(Token::RBracket).ok()?;
                e = Expr::Index {
                    base: Box::new(e),
                    index: Box::new(index),
                };
            } else {
                break;
            }
        }
        Some(e)
    }

    fn parse_expr_primary(&mut self) -> Option<Expr> {
        self.bump_while_semi();

        // Template: TemplatePart | TemplateInterp ... TemplateEnd
        if matches!(self.peek(), Some(Token::TemplatePart(_)) | Some(Token::TemplateInterp(_))) {
            return self.parse_template();
        }

        if self.eat(&Token::LParen) {
            self.bump_while_semi();
            if self.eat(&Token::RParen) {
                return Some(Expr::Literal(Literal::Unit));
            }
            let e = self.parse_expr()?;
            self.bump_while_semi();
            self.expect(Token::RParen).ok()?;
            return Some(e);
        }

        if self.eat(&Token::LBrace) {
            let body = self.parse_block_stmts()?;
            self.expect(Token::RBrace).ok()?;
            return Some(Expr::Block(body));
        }

        if self.eat(&Token::None) {
            return Some(Expr::Literal(Literal::None));
        }
        if self.eat(&Token::True) {
            return Some(Expr::Literal(Literal::Bool(true)));
        }
        if self.eat(&Token::False) {
            return Some(Expr::Literal(Literal::Bool(false)));
        }
        if let Some(Token::IntLit(i)) = self.peek().cloned() {
            self.advance();
            return Some(Expr::Literal(Literal::Int(i)));
        }
        if let Some(Token::FloatLit(f)) = self.peek().cloned() {
            self.advance();
            return Some(Expr::Literal(Literal::Float(f)));
        }
        if let Some(Token::CharLit(c)) = self.peek().cloned() {
            self.advance();
            return Some(Expr::Literal(Literal::Char(c)));
        }
        if let Some(Token::StringLit(s)) = self.peek().cloned() {
            self.advance();
            return Some(Expr::Literal(Literal::String(s)));
        }
        if self.eat(&Token::Some) {
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_expr()?;
            self.expect(Token::RParen).ok()?;
            return Some(Expr::Literal(Literal::Some(Box::new(inner))));
        }
        if self.eat(&Token::Ok) {
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_expr()?;
            self.expect(Token::RParen).ok()?;
            return Some(Expr::Literal(Literal::Ok(Box::new(inner))));
        }
        if self.eat(&Token::Err) {
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_expr()?;
            self.expect(Token::RParen).ok()?;
            return Some(Expr::Literal(Literal::Err(Box::new(inner))));
        }

        if let Some(Token::NativeIdent(ref name)) = self.peek() {
            let name = name.clone();
            self.advance();
            self.expect(Token::LParen).ok()?;
            let mut args = Vec::new();
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RParen) {
                    break;
                }
                args.push(self.parse_expr()?);
                if !self.eat(&Token::Comma) && !self.is(&Token::RParen) {
                    break;
                }
            }
            return Some(Expr::NativeCall(name, args));
        }

        if let Some(Token::Ident(ref name)) = self.peek() {
            let name = name.clone();
            self.advance();
            if self.eat(&Token::FatArrow) {
                let mut params = vec![(name.clone(), None)];
                while self.eat(&Token::Comma) {
                    let n = self.expect_ident()?;
                    params.push((n, None));
                }
                let body = Box::new(self.parse_expr()?);
                return Some(Expr::Lambda { params, body });
            }
            if self.eat(&Token::LBrace) {
                let mut fields = Vec::new();
                loop {
                    self.bump_while_semi();
                    if self.eat(&Token::RBrace) {
                        break;
                    }
                    let f = self.expect_ident()?;
                    self.expect(Token::Colon).ok()?;
                    let val = self.parse_expr()?;
                    fields.push((f, val));
                    if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                        break;
                    }
                }
                return Some(Expr::StructLiteral {
                    name,
                    fields,
                });
            }
            if self.eat(&Token::ColonColon) {
                let variant = self.expect_ident()?;
                let data = if self.eat(&Token::LParen) {
                    let e = self.parse_expr()?;
                    self.expect(Token::RParen).ok()?;
                    Some(Box::new(e))
                } else {
                    None
                };
                return Some(Expr::VariantLiteral {
                    enum_name: name,
                    variant,
                    data,
                });
            }
            return Some(Expr::Ident(name));
        }

        if self.eat(&Token::LBracket) {
            let mut elems = Vec::new();
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RBracket) {
                    break;
                }
                elems.push(self.parse_expr()?);
                if !self.eat(&Token::Comma) && !self.is(&Token::RBracket) {
                    break;
                }
            }
            return Some(Expr::ListLiteral(elems));
        }

        self.err("expected expression".into());
        None
    }

    fn parse_template(&mut self) -> Option<Expr> {
        let mut parts = Vec::new();
        loop {
            if let Some(Token::TemplatePart(s)) = self.peek().cloned() {
                self.advance();
                parts.push(TemplatePart::Lit(s));
            } else if let Some(Token::TemplateInterp(id)) = self.peek().cloned() {
                self.advance();
                parts.push(TemplatePart::Interp(id));
            } else if self.eat(&Token::TemplateEnd) {
                break;
            } else {
                self.err("expected template part or end".into());
                break;
            }
        }
        Some(Expr::Template { parts })
    }
}
