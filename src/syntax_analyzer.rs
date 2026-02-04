//! SyntaxAnalyzer: logos tabanli lexer + parser + hata raporlama.
//! Not: Lexer/Parser artik burada birlesik. Disarida ayri moduller yok.

use logos::Logos;
use crate::collections::HashMap;

use crate::ast::*;
use crate::types::Type;

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    // Keywords
    Let,
    Var,
    Fn,
    Struct,
    Enum,
    Mod,
    From,
    Type,
    Label,
    Property,
    Get,
    Set,
    Match,
    If,
    Else,
    Loop,
    Return,
    Break,
    Continue,
    True,
    False,
    Option,
    Result,
    Ok,
    Err,
    Some,
    None,
    Array,
    List,
    Map,
    IntKw,
    UIntKw,
    FloatKw,
    BoolKw,
    CharKw,
    StringKw,
    Native,

    // Identifiers & names
    Ident(String),
    /// native::ident
    NativeIdent(String),
    /// Enum::Variant
    PathIdent(String, String),

    // Literals
    IntLit(i64),
    UIntLit(u64),
    FloatLit(f64),
    CharLit(char),
    /// "..." — no interpolation
    StringLit(String),
    /// `...` template: (literal, optional interp id) segments
    TemplatePart(String),
    TemplateInterp(String),
    TemplateEnd,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Eq,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Not,
    Arrow,    // ->
    FatArrow, // =>

    // Delimiters
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Semi,
    Dot,
    ColonColon,
    At,

    Eof,
}

impl Token {
    pub fn is_eof(&self) -> bool {
        matches!(self, Token::Eof)
    }
}

#[derive(Logos, Debug, Clone, PartialEq)]
enum SAToken {
    // ===== Keywords =====
    #[token("let")]
    Let,
    #[token("var")]
    Var,
    #[token("fn")]
    Fn,
    #[token("struct")]
    Struct,
    #[token("enum")]
    Enum,
    #[token("mod")]
    Mod,
    #[token("from")]
    From,
    #[token("type")]
    Type,
    #[token("label")]
    Label,
    #[token("property")]
    Property,
    #[token("Get")]
    Get,
    #[token("Set")]
    Set,
    #[token("match")]
    Match,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("loop")]
    Loop,
    #[token("return")]
    Return,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,

    #[token("true")]
    True,
    #[token("false")]
    False,

    #[token("Option")]
    Option,
    #[token("Result")]
    Result,
    #[token("Ok")]
    Ok,
    #[token("Err")]
    Err,
    #[token("Some")]
    Some,
    #[token("None")]
    None,

    #[token("Array")]
    Array,
    #[token("List")]
    List,
    #[token("Map")]
    Map,

    #[token("Int")]
    IntKw,
    #[token("UInt")]
    UIntKw,
    #[token("Float")]
    FloatKw,
    #[token("Bool")]
    BoolKw,
    #[token("Char")]
    CharKw,
    #[token("String")]
    StringKw,
    #[token("native")]
    Native,

    // ===== Operators (ORDER MATTERS) =====
    #[token("&&")]
    And,
    #[token("||")]
    Or,
    #[token("==")]
    EqEq,
    #[token("!=")]
    Ne,
    #[token("<=")]
    Le,
    #[token(">=")]
    Ge,
    #[token("=>")]
    FatArrow,
    #[token("->")]
    Arrow,

    #[token("=")]
    Eq,

    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("!")]
    Not,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,

    // ===== Delimiters =====
    #[token("::")]
    ColonColon,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(";")]
    Semi,
    #[token(".")]
    Dot,
    #[token("@")]
    At,

    // ===== Literals =====
    #[regex(r"(?:\d+\.\d+(?:[eE][+-]?\d+)?|\d+[eE][+-]?\d+)", |lex| lex.slice().parse::<f64>().ok())]
    FloatLit(f64),

    #[regex(r"\d+[uU]", |lex| parse_uint_literal(lex.slice()))]
    UIntLit(u64),

    #[regex(r"\d+", |lex| lex.slice().parse::<i64>().ok())]
    IntLit(i64),

    #[regex(r"'([^'\\]|\\.)'", |lex| parse_char_literal(lex.slice()))]
    CharLit(char),

    #[regex(r#""([^"\\\x00-\x1F]|\\(["\\bnfrt/]|u[a-fA-F0-9]{4}))*""#, |lex| parse_string_literal(lex.slice()))]
    StringLit(String),

    // Backtick template raw: iceri parse edilecek.
    #[regex(r"`([^`\\]|\\.)*`", |lex| parse_template_literal(lex.slice()))]
    TemplateRaw(String),

    // ===== Native Identifier =====
    #[regex(r"native::[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice()[8..].to_string())]
    NativeIdent(String),
    // ===== Path Identifier (Enum::Variant) =====
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*::[a-zA-Z_][a-zA-Z0-9_]*", |lex| parse_path_ident(lex.slice()))]
    PathIdent((String, String)),

    // ===== Identifier =====
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),

    // ===== Skip =====
    #[regex(r"[ \t\r\n]+", logos::skip)]
    #[regex(r"//[^\n\r]*", logos::skip, allow_greedy = true)]
    // ===== Error =====
    Error,
}

#[derive(Debug, Clone)]
pub struct SyntaxError {
    pub pos: (usize, usize), // line-column (1-based)
    pub detail: String,
}

impl SyntaxError {
    pub fn new(pos: (usize, usize), detail: String) -> Self {
        Self { pos, detail }
    }
}

impl std::fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error on ({}:{}): {}", self.pos.0, self.pos.1, self.detail)
    }
}

#[derive(Debug)]
pub struct SyntaxAnalyzer {
    source: String,
    tokens: Vec<(Token, Span)>,
    errors: Vec<SyntaxError>,
}

impl SyntaxAnalyzer {
    pub fn new(source: &str) -> Self {
        let mut sa = Self {
            source: source.to_string(),
            tokens: Vec::new(),
            errors: Vec::new(),
        };
        sa.lex();
        sa
    }

    /// Tum analiz akisi: lex + parse, sonuc olarak AST ya da hatalar.
    pub fn analyz(&mut self) -> Result<Program, Vec<SyntaxError>> {
        if !self.errors.is_empty() {
            return Err(self.errors.clone());
        }

        let parse = Parser::new(self.tokens.clone()).parse();
        match parse {
            Ok(program) => Ok(program),
            Err(errs) => {
                let mut out = Vec::new();
                for e in errs {
                    let pos = match e.1 {
                        Some(span) => line_col(&self.source, span.lo),
                        None => (1, 1),
                    };
                    out.push(SyntaxError::new(pos, e.0));
                }
                Err(out)
            }
        }
    }


    fn lex(&mut self) {
        let src = self.source.clone();
        let mut lexer = SAToken::lexer(&src);
        let mut tokens: Vec<(Token, Span)> = Vec::new();
        let mut errors: Vec<SyntaxError> = Vec::new();

        while let Some(result) = lexer.next() {
            let span = lexer.span();
            match result {
                Ok(SAToken::Error) | Err(_) => {
                    errors.push(SyntaxError::new(
                        line_col(&src, span.start),
                        format!("Lexical error: `{}`", &src[span.start..span.end]),
                    ));
                }
                Ok(tok) => {
                    if let Err(e) = push_token(&src, &mut tokens, tok, span.start, span.end) {
                        errors.push(e);
                    }
                }
            }
        }

        tokens.push((
            Token::Eof,
            Span {
                lo: src.len(),
                hi: src.len(),
            },
        ));

        self.tokens = tokens;
        self.errors = errors;
    }
}

fn push_token(
    src: &str,
    tokens: &mut Vec<(Token, Span)>,
    tok: SAToken,
    lo: usize,
    hi: usize,
) -> Result<(), SyntaxError> {
    let span = Span { lo, hi };
    match tok {
        SAToken::Let => tokens.push((Token::Let, span)),
        SAToken::Var => tokens.push((Token::Var, span)),
        SAToken::Fn => tokens.push((Token::Fn, span)),
        SAToken::Struct => tokens.push((Token::Struct, span)),
        SAToken::Enum => tokens.push((Token::Enum, span)),
        SAToken::Mod => tokens.push((Token::Mod, span)),
        SAToken::From => tokens.push((Token::From, span)),
        SAToken::Type => tokens.push((Token::Type, span)),
        SAToken::Label => tokens.push((Token::Label, span)),
        SAToken::Property => tokens.push((Token::Property, span)),
        SAToken::Get => tokens.push((Token::Get, span)),
        SAToken::Set => tokens.push((Token::Set, span)),
        SAToken::Match => tokens.push((Token::Match, span)),
        SAToken::If => tokens.push((Token::If, span)),
        SAToken::Else => tokens.push((Token::Else, span)),
        SAToken::Loop => tokens.push((Token::Loop, span)),
        SAToken::Return => tokens.push((Token::Return, span)),
        SAToken::Break => tokens.push((Token::Break, span)),
        SAToken::Continue => tokens.push((Token::Continue, span)),

        SAToken::True => tokens.push((Token::True, span)),
        SAToken::False => tokens.push((Token::False, span)),

        SAToken::Option => tokens.push((Token::Option, span)),
        SAToken::Result => tokens.push((Token::Result, span)),
        SAToken::Ok => tokens.push((Token::Ok, span)),
        SAToken::Err => tokens.push((Token::Err, span)),
        SAToken::Some => tokens.push((Token::Some, span)),
        SAToken::None => tokens.push((Token::None, span)),

        SAToken::Array => tokens.push((Token::Array, span)),
        SAToken::List => tokens.push((Token::List, span)),
        SAToken::Map => tokens.push((Token::Map, span)),

        SAToken::IntKw => tokens.push((Token::IntKw, span)),
        SAToken::UIntKw => tokens.push((Token::UIntKw, span)),
        SAToken::FloatKw => tokens.push((Token::FloatKw, span)),
        SAToken::BoolKw => tokens.push((Token::BoolKw, span)),
        SAToken::CharKw => tokens.push((Token::CharKw, span)),
        SAToken::StringKw => tokens.push((Token::StringKw, span)),
        SAToken::Native => tokens.push((Token::Native, span)),

        SAToken::And => tokens.push((Token::And, span)),
        SAToken::Or => tokens.push((Token::Or, span)),
        SAToken::EqEq => tokens.push((Token::EqEq, span)),
        SAToken::Ne => tokens.push((Token::Ne, span)),
        SAToken::Le => tokens.push((Token::Le, span)),
        SAToken::Ge => tokens.push((Token::Ge, span)),
        SAToken::FatArrow => tokens.push((Token::FatArrow, span)),
        SAToken::Arrow => tokens.push((Token::Arrow, span)),

        SAToken::Eq => tokens.push((Token::Eq, span)),
        SAToken::Plus => tokens.push((Token::Plus, span)),
        SAToken::Minus => tokens.push((Token::Minus, span)),
        SAToken::Star => tokens.push((Token::Star, span)),
        SAToken::Slash => tokens.push((Token::Slash, span)),
        SAToken::Percent => tokens.push((Token::Percent, span)),
        SAToken::Not => tokens.push((Token::Not, span)),
        SAToken::Lt => tokens.push((Token::Lt, span)),
        SAToken::Gt => tokens.push((Token::Gt, span)),

        SAToken::ColonColon => tokens.push((Token::ColonColon, span)),
        SAToken::LParen => tokens.push((Token::LParen, span)),
        SAToken::RParen => tokens.push((Token::RParen, span)),
        SAToken::LBrace => tokens.push((Token::LBrace, span)),
        SAToken::RBrace => tokens.push((Token::RBrace, span)),
        SAToken::LBracket => tokens.push((Token::LBracket, span)),
        SAToken::RBracket => tokens.push((Token::RBracket, span)),
        SAToken::Comma => tokens.push((Token::Comma, span)),
        SAToken::Colon => tokens.push((Token::Colon, span)),
        SAToken::Semi => tokens.push((Token::Semi, span)),
        SAToken::Dot => tokens.push((Token::Dot, span)),
        SAToken::At => tokens.push((Token::At, span)),

        SAToken::NativeIdent(name) => tokens.push((Token::NativeIdent(name), span)),
        SAToken::PathIdent((a, b)) => tokens.push((Token::PathIdent(a, b), span)),
        SAToken::Ident(name) => tokens.push((Token::Ident(name), span)),
        SAToken::IntLit(i) => tokens.push((Token::IntLit(i), span)),
        SAToken::UIntLit(u) => tokens.push((Token::UIntLit(u), span)),
        SAToken::FloatLit(f) => tokens.push((Token::FloatLit(f), span)),
        SAToken::CharLit(c) => tokens.push((Token::CharLit(c), span)),
        SAToken::StringLit(s) => tokens.push((Token::StringLit(s), span)),
        SAToken::TemplateRaw(raw) => {
            // NOTE: Template string, ici parser'a uygun sekilde parcalaniyor.
            push_template_tokens(src, tokens, &raw, lo, hi)?;
        }
        SAToken::Error => {
            return Err(SyntaxError::new(
                line_col(src, lo),
                format!("Lexical error: `{}`", &src[lo..hi]),
            ));
        }
    }
    Ok(())
}

fn push_template_tokens(
    src: &str,
    tokens: &mut Vec<(Token, Span)>,
    raw: &str,
    lo: usize,
    _hi: usize,
) -> Result<(), SyntaxError> {
    // NOTE: raw icerigi backtick'ler olmadan gelir. Span hesaplari icin
    // baslangic offset'i `lo + 1` olarak alinmistir.
    let base = lo + 1;
    let bytes = raw.as_bytes();
    let mut lit = String::new();
    let mut lit_start = 0usize;
    let mut i = 0usize;

    while i < bytes.len() {
        let b = bytes[i];
        match b {
            b'\\' => {
                i += 1;
                if i >= bytes.len() {
                    return Err(SyntaxError::new(
                        line_col(src, lo),
                        "unexpected eof after \\\\ in template".into(),
                    ));
                }
                let e = bytes[i] as char;
                match e {
                    'n' => lit.push('\n'),
                    'r' => lit.push('\r'),
                    't' => lit.push('\t'),
                    '0' => lit.push('\0'),
                    '`' => lit.push('`'),
                    '\\' => lit.push('\\'),
                    '{' => lit.push('{'),
                    _ => {
                        return Err(SyntaxError::new(
                            line_col(src, lo),
                            format!("unknown escape \\\\{}", e),
                        ))
                    }
                }
            }
            b'{' => {
                if !lit.is_empty() {
                    let lit_end = i;
                    tokens.push((
                        Token::TemplatePart(std::mem::take(&mut lit)),
                        Span {
                            lo: base + lit_start,
                            hi: base + lit_end,
                        },
                    ));
                }
                let brace_start = i;
                i += 1;
                while i < bytes.len() && (bytes[i] == b' ' || bytes[i] == b'\t') {
                    i += 1;
                }
                let ident_start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                if ident_start == i {
                    return Err(SyntaxError::new(
                        line_col(src, lo),
                        "expected identifier in template interpolation".into(),
                    ));
                }
                let id = std::str::from_utf8(&bytes[ident_start..i])
                    .unwrap_or("")
                    .to_string();
                while i < bytes.len() && (bytes[i] == b' ' || bytes[i] == b'\t') {
                    i += 1;
                }
                if i >= bytes.len() || bytes[i] != b'}' {
                    return Err(SyntaxError::new(
                        line_col(src, lo),
                        "expected } to close template interpolation".into(),
                    ));
                }
                let brace_end = i + 1;
                tokens.push((
                    Token::TemplateInterp(id),
                    Span {
                        lo: base + brace_start,
                        hi: base + brace_end,
                    },
                ));
                lit_start = brace_end;
            }
            _ => {
                lit.push(b as char);
            }
        }
        i += 1;
    }

    if !lit.is_empty() {
        let lit_end = bytes.len();
        tokens.push((
            Token::TemplatePart(std::mem::take(&mut lit)),
            Span {
                lo: base + lit_start,
                hi: base + lit_end,
            },
        ));
    }
    tokens.push((
        Token::TemplateEnd,
        Span {
            lo: base + bytes.len(),
            hi: base + bytes.len(),
        },
    ));
    Ok(())
}

fn parse_string_literal(slice: &str) -> Option<String> {
    if slice.len() < 2 {
        return None;
    }
    let inner = &slice[1..slice.len() - 1];
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        let esc = chars.next()?;
        match esc {
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            '0' => out.push('\0'),
            '"' => out.push('"'),
            '\\' => out.push('\\'),
            _ => return None,
        }
    }
    Some(out)
}

fn parse_uint_literal(slice: &str) -> Option<u64> {
    let s = slice.trim_end_matches(|c: char| c == 'u' || c == 'U');
    s.parse::<u64>().ok()
}

fn parse_char_literal(slice: &str) -> Option<char> {
    if slice.len() < 3 {
        return None;
    }
    let inner = &slice[1..slice.len() - 1];
    let mut chars = inner.chars();
    let c = chars.next()?;
    let out = if c == '\\' {
        let esc = chars.next()?;
        match esc {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '0' => '\0',
            '\'' => '\'',
            '\\' => '\\',
            _ => return None,
        }
    } else {
        c
    };
    if chars.next().is_some() {
        return None;
    }
    Some(out)
}

fn parse_template_literal(slice: &str) -> Option<String> {
    if slice.len() < 2 {
        return None;
    }
    Some(slice[1..slice.len() - 1].to_string())
}

fn parse_path_ident(slice: &str) -> Option<(String, String)> {
    let mut parts = slice.split("::");
    let a = parts.next()?.to_string();
    let b = parts.next()?.to_string();
    if parts.next().is_some() {
        return None;
    }
    Some((a, b))
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

// ===== Parser (SyntaxAnalyzer icinde) =====

type TokenStream = std::iter::Peekable<std::vec::IntoIter<(Token, Span)>>;

#[derive(Debug)]
struct ParseError(pub String, pub Option<Span>);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "parse error: {}", self.0)
    }
}

impl std::error::Error for ParseError {}

struct Parser {
    tokens: TokenStream,
    last_span: Span,
    errs: Vec<ParseError>,
    allow_struct_literal: bool,
}

impl Parser {
    fn new(tokens: Vec<(Token, Span)>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            last_span: Span { lo: 0, hi: 0 },
            errs: Vec::new(),
            allow_struct_literal: true,
        }
    }

    fn peek(&mut self) -> Option<&Token> {
        self.tokens.peek().map(|(t, _)| t)
    }

    fn peek_span(&mut self) -> Option<Span> {
        self.tokens.peek().map(|(_, s)| s.clone())
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
        self.errs
            .push(ParseError(msg, Some(self.last_span.clone())));
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

    fn span_join(a: &Span, b: &Span) -> Span {
        Span { lo: a.lo, hi: b.hi }
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

    fn make_expr(&self, span: Span, node: ExprKind) -> Expr {
        Expr { node, span }
    }

    fn make_stmt(&self, span: Span, node: StmtKind) -> Stmt {
        Stmt { node, span }
    }

    fn parse(mut self) -> Result<Program, Vec<ParseError>> {
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
        if self.eat(&Token::Type) {
            let name = self.expect_ident()?;
            self.expect(Token::Eq).ok()?;
            let target = self.parse_type()?;
            if !self.eat(&Token::Semi) && !self.is(&Token::Eof) {
                self.err("expected ; after type alias".into());
            }
            return Some(Item::TypeAlias(TypeAlias { name, target }));
        }
        if self.eat(&Token::Property) {
            return Some(Item::PropertyDef(self.parse_property_def()?));
        }
        if self.eat(&Token::Mod) {
            let name = self.expect_ident()?;
            let mut path = None;
            if self.eat(&Token::From) {
                match self.advance() {
                    Some((Token::StringLit(s), _)) => {
                        path = Some(s);
                    }
                    _ => {
                        self.err("expected string literal after from".into());
                    }
                }
            }
            if !self.eat(&Token::Semi) && !self.is(&Token::Eof) {
                self.err("expected ; after mod declaration".into());
            }
            return Some(Item::ModuleDecl(ModuleDecl { name, path }));
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

    fn parse_property_def(&mut self) -> Option<PropertyDef> {
        self.expect(Token::Lt).ok()?;
        let typ = self.parse_type()?;
        self.expect(Token::Gt).ok()?;
        let name = self.expect_ident()?;
        self.expect(Token::LBrace).ok()?;

        let mut getter: Option<PropertyGetter> = None;
        let mut setter: Option<PropertySetter> = None;

        loop {
            self.bump_while_semi();
            if self.eat(&Token::RBrace) {
                break;
            }
            if self.eat(&Token::Get) {
                if getter.is_some() {
                    self.err("duplicate Get in property".into());
                }
                if self.eat(&Token::Semi) {
                    getter = Some(PropertyGetter {
                        value_param: "value".into(),
                        body: Expr {
                            node: ExprKind::Ident("value".into()),
                            span: self.last_span.clone(),
                        },
                    });
                    continue;
                }
                self.expect(Token::Colon).ok()?;
                let value_param = self.expect_ident()?;
                let body = if self.eat(&Token::FatArrow) {
                    self.parse_expr()?
                } else if self.eat(&Token::LBrace) {
                    let b = self.parse_block_stmts()?;
                    self.expect(Token::RBrace).ok()?;
                    let span = Parser::block_span(&b);
                    Expr { node: ExprKind::Block(b), span }
                } else {
                    self.err("expected => or { after Get:".into());
                    return None;
                };
                getter = Some(PropertyGetter { value_param, body });
                if self.eat(&Token::Semi) {
                    continue;
                }
                continue;
            }
            if self.eat(&Token::Set) {
                if self.eat(&Token::Semi) {
                    setter = None;
                    continue;
                }
                self.expect(Token::Colon).ok()?;
                let value_param = self.expect_ident()?;
                self.expect(Token::Comma).ok()?;
                let input_param = self.expect_ident()?;
                let body = if self.eat(&Token::FatArrow) {
                    self.parse_expr()?
                } else if self.eat(&Token::LBrace) {
                    let b = self.parse_block_stmts()?;
                    self.expect(Token::RBrace).ok()?;
                    let span = Parser::block_span(&b);
                    Expr { node: ExprKind::Block(b), span }
                } else {
                    self.err("expected => or { after Set:".into());
                    return None;
                };
                setter = Some(PropertySetter {
                    value_param,
                    input_param,
                    body,
                });
                if self.eat(&Token::Semi) {
                    continue;
                }
                continue;
            }
            self.err("expected Get or Set in property".into());
            break;
        }

        let getter = getter.unwrap_or(PropertyGetter {
            value_param: "value".into(),
            body: Expr {
                node: ExprKind::Ident("value".into()),
                span: self.last_span.clone(),
            },
        });

        self.expect(Token::Eq).ok()?;
        let default = self.parse_expr()?;
        if !self.eat(&Token::Semi) && !self.is(&Token::Eof) {
            self.err("expected ; after property".into());
        }

        Some(PropertyDef {
            name,
            typ,
            default,
            getter,
            setter,
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
            let start = self.last_span.clone();
            let b = self.parse_let_binding()?;
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_stmt(span, StmtKind::Let(b)));
        }
        if self.eat(&Token::Var) {
            let start = self.last_span.clone();
            let b = self.parse_var_binding()?;
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_stmt(span, StmtKind::Var(b)));
        }
        if self.eat(&Token::Break) {
            let span = self.last_span.clone();
            return Some(self.make_stmt(span, StmtKind::Break));
        }
        if self.eat(&Token::Continue) {
            let span = self.last_span.clone();
            return Some(self.make_stmt(span, StmtKind::Continue));
        }
        if self.eat(&Token::If) {
            let start = self.last_span.clone();
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
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_stmt(span, StmtKind::If {
                cond,
                then_b,
                else_b,
            }));
        }
        if self.eat(&Token::Loop) {
            let start = self.last_span.clone();
            self.expect(Token::LBrace).ok()?;
            let body = self.parse_block_stmts()?;
            self.expect(Token::RBrace).ok()?;
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_stmt(span, StmtKind::Loop(body)));
        }
        if self.eat(&Token::Return) {
            let start = self.last_span.clone();
            // NOTE: return ifadesi opsiyonel olabilir.
            if self.is(&Token::Semi) || self.is(&Token::RBrace) {
                let span = Span { lo: start.lo, hi: self.last_span.hi };
                return Some(self.make_stmt(span, StmtKind::Return(None)));
            }
            let val = self.parse_expr()?;
            let span = Span { lo: start.lo, hi: val.span.hi };
            return Some(self.make_stmt(span, StmtKind::Return(Some(val))));
        }
        if self.eat(&Token::Match) {
            let start = self.last_span.clone();
            let prev = self.allow_struct_literal;
            self.allow_struct_literal = false;
            let scrutinee = self.parse_expr()?;
            self.allow_struct_literal = prev;
            self.expect(Token::LBrace).ok()?;
            let mut arms = Vec::new();
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RBrace) {
                    break;
                }
                let pattern = if let Some(Token::PathIdent(ref a, ref b)) = self.peek() {
                    let (enum_name, variant) = (a.clone(), b.clone());
                    self.advance();
                    let inner = if self.eat(&Token::LParen) {
                        let p = self.parse_match_pattern()?;
                        self.expect(Token::RParen).ok()?;
                        Some(Box::new(p))
                    } else {
                        None
                    };
                    Pattern::Variant {
                        enum_name,
                        variant,
                        inner,
                    }
                } else {
                    self.parse_match_pattern()?
                };
                self.expect(Token::FatArrow).ok()?;
                let body = if self.is(&Token::LBrace) {
                    self.advance();
                    let b = self.parse_block_stmts()?;
                    self.expect(Token::RBrace).ok()?;
                    b
                } else {
                    let e = self.parse_expr()?;
                    vec![self.make_stmt(e.span.clone(), StmtKind::Expr(e))]
                };
                arms.push(MatchArm { pattern, body });
                self.bump_while_semi();
                if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                    break;
                }
            }
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_stmt(span, StmtKind::Match { scrutinee, arms }));
        }
        // Assign: ident = expr, or expression statement starting with ident
        if let Some(name) = self.peek_ident() {
            self.advance();
            let start = self.last_span.clone();
            let head = self.make_expr(start.clone(), ExprKind::Ident(name));
            let lhs = self.parse_expr_postfix(Some(head))?;
            if self.eat(&Token::Eq) {
                let value = self.parse_expr()?;
                let span = Span { lo: lhs.span.lo, hi: value.span.hi };
                return match lhs.node {
                    ExprKind::Ident(name) => {
                        Some(self.make_stmt(span, StmtKind::Assign { name, value }))
                    }
                    ExprKind::Index { base, index } => Some(self.make_stmt(
                        span,
                        StmtKind::AssignIndex {
                            base: *base,
                            index: *index,
                            value,
                        },
                    )),
                    _ => {
                        self.err("invalid assignment target".into());
                        None
                    }
                };
            }
            return Some(self.make_stmt(lhs.span.clone(), StmtKind::Expr(lhs)));
        }
        // Expression statement
        let e = self.parse_expr()?;
        Some(self.make_stmt(e.span.clone(), StmtKind::Expr(e)))
    }

    fn parse_match_pattern(&mut self) -> Option<Pattern> {
        self.bump_while_semi();
        if self.eat_ident_eq("_") {
            return Some(Pattern::Wildcard);
        }
        if let Some(Token::IntLit(i)) = self.peek().cloned() {
            self.advance();
            return Some(Pattern::Literal(Literal::Int(i)));
        }
        if let Some(Token::UIntLit(u)) = self.peek().cloned() {
            self.advance();
            return Some(Pattern::Literal(Literal::UInt(u)));
        }
        if let Some(Token::FloatLit(f)) = self.peek().cloned() {
            self.advance();
            return Some(Pattern::Literal(Literal::Float(f)));
        }
        if let Some(Token::CharLit(c)) = self.peek().cloned() {
            self.advance();
            return Some(Pattern::Literal(Literal::Char(c)));
        }
        if let Some(Token::StringLit(s)) = self.peek().cloned() {
            self.advance();
            return Some(Pattern::Literal(Literal::String(s)));
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
        if self.eat(&Token::Some) {
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_match_pattern()?;
            self.expect(Token::RParen).ok()?;
            return Some(Pattern::Variant {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                inner: Some(Box::new(inner)),
            });
        }
        if self.eat(&Token::Ok) {
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_match_pattern()?;
            self.expect(Token::RParen).ok()?;
            return Some(Pattern::Variant {
                enum_name: "Result".to_string(),
                variant: "Ok".to_string(),
                inner: Some(Box::new(inner)),
            });
        }
        if self.eat(&Token::Err) {
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_match_pattern()?;
            self.expect(Token::RParen).ok()?;
            return Some(Pattern::Variant {
                enum_name: "Result".to_string(),
                variant: "Err".to_string(),
                inner: Some(Box::new(inner)),
            });
        }
        if let Some(Token::PathIdent(ref a, ref b)) = self.peek() {
            let (enum_name, variant) = (a.clone(), b.clone());
            self.advance();
            let inner = if self.eat(&Token::LParen) {
                let p = self.parse_match_pattern()?;
                self.expect(Token::RParen).ok()?;
                Some(Box::new(p))
            } else {
                None
            };
            return Some(Pattern::Variant {
                enum_name,
                variant,
                inner,
            });
        }
        if let Some(Token::Ident(ref name)) = self.peek() {
            let name = name.clone();
            self.advance();
            if self.eat(&Token::ColonColon) {
                let variant = self.expect_ident()?;
                let inner = if self.eat(&Token::LParen) {
                    let p = self.parse_match_pattern()?;
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
                    let pat = self.parse_match_pattern()?;
                    fields.push((f, pat));
                    if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                        break;
                    }
                }
                return Some(Pattern::StructLiteral { name, fields });
            }
            return Some(Pattern::Ident(name));
        }
        self.err("expected pattern".into());
        None
    }

    fn expect_ident(&mut self) -> Option<String> {
        let (t, _) = self
            .advance()
            .ok_or_else(|| {
                self.err("expected identifier".into());
            })
            .ok()?;
        match t {
            Token::Ident(s) => Some(s),
            Token::PathIdent(_, b) => Some(b),
            _ => {
                self.err("expected identifier".into());
                None
            }
        }
    }

    fn parse_type(&mut self) -> Option<Type> {
        if self.eat(&Token::LParen) {
            let mut fields = Vec::new();
            let first = self.parse_type()?;
            let label = if self.eat(&Token::Label) {
                Some(self.expect_ident()?)
            } else {
                None
            };
            fields.push(crate::types::TupleField { typ: first, label });
            if self.eat(&Token::Comma) {
                loop {
                    if self.eat(&Token::RParen) {
                        break;
                    }
                    let t = self.parse_type()?;
                    let label = if self.eat(&Token::Label) {
                        Some(self.expect_ident()?)
                    } else {
                        None
                    };
                    fields.push(crate::types::TupleField { typ: t, label });
                    if !self.eat(&Token::Comma) && !self.is(&Token::RParen) {
                        break;
                    }
                }
                self.expect(Token::RParen).ok()?;
                return Some(Type::Tuple(fields));
            }
            self.expect(Token::RParen).ok()?;
            return Some(fields.remove(0).typ);
        }
        if self.eat(&Token::IntKw) {
            return Some(Type::Int);
        }
        if self.eat(&Token::UIntKw) {
            return Some(Type::UInt);
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
                fields: HashMap::new(),
            });
        }
        self.err("expected type".into());
        None
    }

    fn expect_int_lit(&mut self) -> Option<usize> {
        let (t, _) = self
            .advance()
            .ok_or_else(|| {
                self.err("expected integer".into());
            })
            .ok()?;
        match t {
            Token::IntLit(i) if i >= 0 => Some(i as usize),
            Token::UIntLit(u) => Some(u as usize),
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
            let span = Parser::span_join(&lhs.span, &rhs.span);
            lhs = self.make_expr(
                span,
                ExprKind::Binary {
                    op: BinOp::Or,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                },
            );
        }
        Some(lhs)
    }

    fn parse_expr_and(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_expr_cmp()?;
        while self.eat(&Token::And) {
            let rhs = self.parse_expr_cmp()?;
            let span = Parser::span_join(&lhs.span, &rhs.span);
            lhs = self.make_expr(
                span,
                ExprKind::Binary {
                    op: BinOp::And,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                },
            );
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
            let span = Parser::span_join(&lhs.span, &rhs.span);
            lhs = self.make_expr(
                span,
                ExprKind::Binary {
                    op,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                },
            );
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
            let span = Parser::span_join(&lhs.span, &rhs.span);
            lhs = self.make_expr(
                span,
                ExprKind::Binary {
                    op,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                },
            );
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
            let span = Parser::span_join(&lhs.span, &rhs.span);
            lhs = self.make_expr(
                span,
                ExprKind::Binary {
                    op,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                },
            );
        }
        Some(lhs)
    }

    fn parse_expr_unary(&mut self) -> Option<Expr> {
        if self.eat(&Token::Minus) {
            let start = self.last_span.clone();
            let inner = self.parse_expr_unary()?;
            let span = Span { lo: start.lo, hi: inner.span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::Unary {
                    op: UnaryOp::Neg,
                    inner: Box::new(inner),
                },
            ));
        }
        if self.eat(&Token::Not) {
            let start = self.last_span.clone();
            let inner = self.parse_expr_unary()?;
            let span = Span { lo: start.lo, hi: inner.span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::Unary {
                    op: UnaryOp::Not,
                    inner: Box::new(inner),
                },
            ));
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
                let span = Span { lo: e.span.lo, hi: self.last_span.hi };
                e = self.make_expr(
                    span,
                    ExprKind::Call {
                        callee: Box::new(e),
                        args,
                    },
                );
            } else if self.eat(&Token::Dot) {
                let name = match self.peek().cloned() {
                    Some(Token::IntLit(i)) => {
                        self.advance();
                        i.to_string()
                    }
                    _ => self.expect_ident()?,
                };
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
                    let mut full_args = Vec::with_capacity(args.len() + 1);
                    full_args.push(e);
                    full_args.extend(args);
                    let span = Span { lo: full_args[0].span.lo, hi: self.last_span.hi };
                    let callee_span = Span { lo: span.lo, hi: span.lo };
                    e = self.make_expr(
                        span,
                        ExprKind::Call {
                            callee: Box::new(self.make_expr(
                                callee_span,
                                ExprKind::Ident(name),
                            )),
                            args: full_args,
                        },
                    );
                } else {
                    let span = Span { lo: e.span.lo, hi: self.last_span.hi };
                    e = self.make_expr(
                        span,
                        ExprKind::FieldAccess {
                            base: Box::new(e),
                            field: name,
                        },
                    );
                }
            } else if self.eat(&Token::LBracket) {
                let index = self.parse_expr()?;
                self.expect(Token::RBracket).ok()?;
                let span = Span { lo: e.span.lo, hi: self.last_span.hi };
                e = self.make_expr(
                    span,
                    ExprKind::Index {
                        base: Box::new(e),
                        index: Box::new(index),
                    },
                );
            } else {
                break;
            }
        }
        Some(e)
    }

    fn parse_expr_primary(&mut self) -> Option<Expr> {
        self.bump_while_semi();

        // Template: TemplatePart | TemplateInterp ... TemplateEnd
        if matches!(
            self.peek(),
            Some(Token::TemplatePart(_)) | Some(Token::TemplateInterp(_))
        ) {
            return self.parse_template();
        }

        if self.eat(&Token::LParen) {
            let _start = self.last_span.clone();
            self.bump_while_semi();
            if self.eat(&Token::RParen) {
                let span = self.last_span.clone();
                return Some(self.make_expr(span, ExprKind::Literal(Literal::Unit)));
            }
            let prev = self.allow_struct_literal;
            self.allow_struct_literal = true;
            let first = self.parse_expr()?;
            self.allow_struct_literal = prev;
            self.bump_while_semi();
            if self.eat(&Token::Comma) {
                let mut elems = vec![first];
                loop {
                    self.bump_while_semi();
                    if self.eat(&Token::RParen) {
                        break;
                    }
                    elems.push(self.parse_expr()?);
                    self.bump_while_semi();
                    if !self.eat(&Token::Comma) && !self.is(&Token::RParen) {
                        break;
                    }
                }
                let span = Span { lo: _start.lo, hi: self.last_span.hi };
                return Some(self.make_expr(span, ExprKind::TupleLiteral(elems)));
            }
            self.expect(Token::RParen).ok()?;
            return Some(first);
        }

        if self.eat(&Token::At) {
            let start = self.last_span.clone();
            self.expect(Token::LBracket).ok()?;
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
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(span, ExprKind::ArrayLiteral(elems)));
        }

        if self.eat(&Token::Array) {
            let start = self.last_span.clone();
            self.expect(Token::LParen).ok()?;
            let mut elems = Vec::new();
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RParen) {
                    break;
                }
                elems.push(self.parse_expr()?);
                if !self.eat(&Token::Comma) && !self.is(&Token::RParen) {
                    break;
                }
            }
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(span, ExprKind::ArrayLiteral(elems)));
        }

        if self.eat(&Token::LBrace) {
            let start = self.last_span.clone();
            self.bump_while_semi();
            if self.eat(&Token::RBrace) {
                let span = Span { lo: start.lo, hi: self.last_span.hi };
                return Some(self.make_expr(span, ExprKind::Block(Vec::new())));
            }

            let first_expr = self.parse_expr()?;
            if self.eat(&Token::FatArrow) {
                // Map literal: { key => value, ... }
                let mut pairs = Vec::new();
                let value = self.parse_expr()?;
                pairs.push((first_expr, value));
                loop {
                    self.bump_while_semi();
                    if self.eat(&Token::RBrace) {
                        break;
                    }
                    if self.eat(&Token::Comma) {
                        self.bump_while_semi();
                        if self.eat(&Token::RBrace) {
                            break;
                        }
                    }
                    let k = self.parse_expr()?;
                    self.expect(Token::FatArrow).ok()?;
                    let v = self.parse_expr()?;
                    pairs.push((k, v));
                }
                let span = Span { lo: start.lo, hi: self.last_span.hi };
                return Some(self.make_expr(span, ExprKind::MapLiteral(pairs)));
            }

            // Block expression: first expr + rest statements
            let mut body = Vec::new();
            body.push(self.make_stmt(first_expr.span.clone(), StmtKind::Expr(first_expr)));
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RBrace) {
                    break;
                }
                if let Some(s) = self.parse_stmt() {
                    body.push(s);
                } else {
                    break;
                }
            }
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(span, ExprKind::Block(body)));
        }

        if self.eat(&Token::If) {
            let start = self.last_span.clone();
            let cond = Box::new(self.parse_expr()?);
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
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::If {
                    cond,
                    then_b,
                    else_b,
                },
            ));
        }

        if self.eat(&Token::Match) {
            let start = self.last_span.clone();
            let prev = self.allow_struct_literal;
            self.allow_struct_literal = false;
            let scrutinee = Box::new(self.parse_expr()?);
            self.allow_struct_literal = prev;
            self.expect(Token::LBrace).ok()?;
            let mut arms = Vec::new();
            loop {
                self.bump_while_semi();
                if self.eat(&Token::RBrace) {
                    break;
                }
                let pattern = if let Some(Token::PathIdent(ref a, ref b)) = self.peek() {
                    let (enum_name, variant) = (a.clone(), b.clone());
                    self.advance();
                    let inner = if self.eat(&Token::LParen) {
                        let p = self.parse_match_pattern()?;
                        self.expect(Token::RParen).ok()?;
                        Some(Box::new(p))
                    } else {
                        None
                    };
                    Pattern::Variant {
                        enum_name,
                        variant,
                        inner,
                    }
                } else {
                    self.parse_match_pattern()?
                };
                self.expect(Token::FatArrow).ok()?;
                let body = if self.is(&Token::LBrace) {
                    self.advance();
                    let b = self.parse_block_stmts()?;
                    self.expect(Token::RBrace).ok()?;
                    b
                } else {
                    let e = self.parse_expr()?;
                    vec![self.make_stmt(e.span.clone(), StmtKind::Expr(e))]
                };
                arms.push(MatchArm { pattern, body });
                self.bump_while_semi();
                if !self.eat(&Token::Comma) && !self.is(&Token::RBrace) {
                    break;
                }
            }
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::Match { scrutinee, arms },
            ));
        }

        if self.eat(&Token::None) {
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::None)));
        }
        if self.eat(&Token::True) {
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::Bool(true))));
        }
        if self.eat(&Token::False) {
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::Bool(false))));
        }
        if let Some(Token::IntLit(i)) = self.peek().cloned() {
            self.advance();
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::Int(i))));
        }
        if let Some(Token::UIntLit(u)) = self.peek().cloned() {
            self.advance();
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::UInt(u))));
        }
        if let Some(Token::FloatLit(f)) = self.peek().cloned() {
            self.advance();
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::Float(f))));
        }
        if let Some(Token::CharLit(c)) = self.peek().cloned() {
            self.advance();
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::Char(c))));
        }
        if let Some(Token::StringLit(s)) = self.peek().cloned() {
            self.advance();
            let span = self.last_span.clone();
            return Some(self.make_expr(span, ExprKind::Literal(Literal::String(s))));
        }
        if self.eat(&Token::Some) {
            let start = self.last_span.clone();
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_expr()?;
            self.expect(Token::RParen).ok()?;
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::Literal(Literal::Some(Box::new(inner))),
            ));
        }
        if self.eat(&Token::Ok) {
            let start = self.last_span.clone();
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_expr()?;
            self.expect(Token::RParen).ok()?;
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::Literal(Literal::Ok(Box::new(inner))),
            ));
        }
        if self.eat(&Token::Err) {
            let start = self.last_span.clone();
            self.expect(Token::LParen).ok()?;
            let inner = self.parse_expr()?;
            self.expect(Token::RParen).ok()?;
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::Literal(Literal::Err(Box::new(inner))),
            ));
        }

        if let Some(Token::NativeIdent(ref name)) = self.peek() {
            let name = name.clone();
            self.advance();
            let start = self.last_span.clone();
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
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(span, ExprKind::NativeCall(name, args)));
        }

        if let Some(Token::PathIdent(ref a, ref b)) = self.peek() {
            let (enum_name, variant) = (a.clone(), b.clone());
            let start = self.peek_span().unwrap_or(self.last_span.clone());
            self.advance();
            let data = if self.eat(&Token::LParen) {
                let e = self.parse_expr()?;
                self.expect(Token::RParen).ok()?;
                Some(Box::new(e))
            } else {
                None
            };
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(
                span,
                ExprKind::VariantLiteral {
                    enum_name,
                    variant,
                    data,
                },
            ));
        }
        if let Some(Token::Ident(ref name)) = self.peek() {
            let name = name.clone();
            self.advance();
            let start = self.last_span.clone();
            if name == "array" && self.eat(&Token::LBracket) {
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
                let span = Span { lo: start.lo, hi: self.last_span.hi };
                return Some(self.make_expr(span, ExprKind::ArrayLiteral(elems)));
            }
            if self.eat(&Token::FatArrow) {
                let mut params = vec![(name.clone(), None)];
                while self.eat(&Token::Comma) {
                    let n = self.expect_ident()?;
                    params.push((n, None));
                }
                let body = Box::new(self.parse_expr()?);
                let span = Span { lo: start.lo, hi: body.span.hi };
                return Some(self.make_expr(
                    span,
                    ExprKind::Lambda { params, body },
                ));
            }
            if self.allow_struct_literal && self.eat(&Token::LBrace) {
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
                let span = Span { lo: start.lo, hi: self.last_span.hi };
                return Some(self.make_expr(
                    span,
                    ExprKind::StructLiteral { name, fields },
                ));
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
                let span = Span { lo: start.lo, hi: self.last_span.hi };
                return Some(self.make_expr(
                    span,
                    ExprKind::VariantLiteral {
                        enum_name: name,
                        variant,
                        data,
                    },
                ));
            }
            let span = Span { lo: start.lo, hi: start.hi };
            return Some(self.make_expr(span, ExprKind::Ident(name)));
        }

        if self.eat(&Token::LBracket) {
            let start = self.last_span.clone();
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
            let span = Span { lo: start.lo, hi: self.last_span.hi };
            return Some(self.make_expr(span, ExprKind::ListLiteral(elems)));
        }

        self.err("expected expression".into());
        None
    }

    fn parse_template(&mut self) -> Option<Expr> {
        let start = self.peek_span().unwrap_or(self.last_span.clone());
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
        let span = Span { lo: start.lo, hi: self.last_span.hi };
        Some(self.make_expr(span, ExprKind::Template { parts }))
    }
}
