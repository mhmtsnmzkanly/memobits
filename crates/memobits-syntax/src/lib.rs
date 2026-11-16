//! Source-spanned syntax for the initial Memobits language subset.
//! Parsing does not perform name, type, ownership, or control-flow checks.
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, SourceId, Span};

#[derive(Clone, Debug, PartialEq)]
pub struct Node<T> {
    pub span: Span,
    pub kind: T,
}
pub type Expr = Node<ExprKind>;
pub type Statement = Node<StatementKind>;
pub type Item = Node<ItemKind>;
#[derive(Clone, Debug, PartialEq)]
pub struct Module {
    pub items: Vec<Item>,
}
#[derive(Clone, Debug, PartialEq)]
pub enum ItemKind {
    Function {
        public: bool,
        name: String,
        parameters: Vec<Parameter>,
        result: Option<Type>,
        body: Block,
    },
    Use {
        public: bool,
        path: Vec<String>,
        alias: Option<String>,
    },
    Type {
        public: bool,
        name: String,
        definition: TypeDefinition,
    },
}
#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    pub span: Span,
    pub path: Vec<String>,
    pub arguments: Vec<TypeArgument>,
}
#[derive(Clone, Debug, PartialEq)]
pub enum TypeArgument {
    Type(Type),
    Integer(IntegerLiteral),
}
#[derive(Clone, Debug, PartialEq)]
pub struct IntegerLiteral {
    pub span: Span,
    pub raw: String,
}
#[derive(Clone, Debug, PartialEq)]
pub enum TypeDefinition {
    Alias(Type),
    Struct(Vec<Field>),
    Enum(Vec<Variant>),
}
#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub span: Span,
    pub public: bool,
    pub name: String,
    pub ty: Type,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Variant {
    pub span: Span,
    pub name: String,
    pub payload: Vec<Type>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Access {
    Owned,
    Borrow,
    Share,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Parameter {
    pub span: Span,
    pub mutable: bool,
    pub name: String,
    pub access: Access,
    pub ty: Type,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub span: Span,
    pub statements: Vec<Statement>,
    pub tail: Option<Box<Expr>>,
}
#[derive(Clone, Debug, PartialEq)]
pub enum StatementKind {
    Binding {
        mutable: bool,
        name: String,
        annotation: Option<Type>,
        value: Expr,
    },
    Assign {
        target: Expr,
        operator: String,
        value: Expr,
    },
    Expression(Expr),
    Return(Option<Expr>),
    Loop(Block),
    Break,
    Continue,
}
#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Array(Vec<Expr>),
    RepeatArray {
        value: Box<Expr>,
        count: IntegerLiteral,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    Number(String),
    Bool(bool),
    Path(Vec<String>),
    Unary {
        operator: String,
        operand: Box<Expr>,
    },
    Binary {
        operator: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
    },
    Field {
        base: Box<Expr>,
        name: String,
    },
    Block(Block),
    If {
        condition: Box<Expr>,
        then_branch: Block,
        else_branch: Option<Box<Expr>>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Word(String),
    Number(String),
    Symbol(String),
    Eof,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}
pub struct LexResult {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
}
pub struct ParseResult {
    pub module: Module,
    pub diagnostics: Vec<Diagnostic>,
}
fn diagnostic(number: u16, span: Span, message: impl Into<String>) -> Diagnostic {
    let mut d = Diagnostic::new(
        DiagnosticCode::new(Category::Syntax, number).unwrap(),
        Severity::Error,
        message,
    );
    d.span = Some(span);
    d
}
/// Lex UTF-8 text; all locations are byte offsets on scalar boundaries.
/// SE001 denotes an unrecognized character or unterminated block comment.
pub fn lex(source: SourceId, text: &str) -> LexResult {
    let mut tokens = Vec::new();
    let mut diagnostics = Vec::new();
    let mut i = 0;
    while i < text.len() {
        let start = i;
        let c = text[i..].chars().next().unwrap();
        if c.is_whitespace() {
            i += c.len_utf8();
            continue;
        }
        if text[i..].starts_with("//") {
            i = text[i..].find('\n').map_or(text.len(), |n| i + n);
            continue;
        }
        if text[i..].starts_with("/*") {
            i += 2;
            let mut depth = 1;
            while i < text.len() && depth > 0 {
                if text[i..].starts_with("/*") {
                    depth += 1;
                    i += 2;
                } else if text[i..].starts_with("*/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += text[i..].chars().next().unwrap().len_utf8();
                }
            }
            if depth > 0 {
                diagnostics.push(diagnostic(
                    1,
                    Span {
                        source,
                        start,
                        end: i,
                    },
                    "unterminated block comment",
                ));
            }
            continue;
        }
        let kind = if c == '_' || c.is_alphabetic() {
            i += c.len_utf8();
            while let Some(c) = text[i..].chars().next() {
                if c == '_' || c.is_alphanumeric() {
                    i += c.len_utf8();
                } else {
                    break;
                }
            }
            TokenKind::Word(text[start..i].into())
        } else if c.is_ascii_digit() {
            i += 1;
            while i < text.len()
                && (text.as_bytes()[i].is_ascii_digit() || text.as_bytes()[i] == b'_')
            {
                i += 1;
            }
            if text.as_bytes().get(i) == Some(&b'.')
                && text.as_bytes().get(i + 1).is_some_and(u8::is_ascii_digit)
            {
                i += 1;
                while i < text.len()
                    && (text.as_bytes()[i].is_ascii_digit() || text.as_bytes()[i] == b'_')
                {
                    i += 1;
                }
            }
            if matches!(text.as_bytes().get(i), Some(b'e' | b'E')) {
                i += 1;
                if matches!(text.as_bytes().get(i), Some(b'+' | b'-')) {
                    i += 1;
                }
                let digits = i;
                while i < text.len() && text.as_bytes()[i].is_ascii_digit() {
                    i += 1;
                }
                if digits == i {
                    diagnostics.push(diagnostic(
                        1,
                        Span {
                            source,
                            start,
                            end: i,
                        },
                        "expected exponent digits",
                    ));
                }
            }
            TokenKind::Number(text[start..i].into())
        } else if let Some(op) = [
            "::", ":=", "->", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=",
        ]
        .into_iter()
        .find(|op| text[i..].starts_with(op))
        {
            i += op.len();
            TokenKind::Symbol(op.into())
        } else if "(){}[],:;=+-*/%!<>.".contains(c) {
            i += 1;
            TokenKind::Symbol(c.to_string())
        } else {
            i += c.len_utf8();
            diagnostics.push(diagnostic(
                1,
                Span {
                    source,
                    start,
                    end: i,
                },
                format!("unrecognized character {c:?}"),
            ));
            continue;
        };
        tokens.push(Token {
            span: Span {
                source,
                start,
                end: i,
            },
            kind,
        });
    }
    tokens.push(Token {
        span: Span {
            source,
            start: i,
            end: i,
        },
        kind: TokenKind::Eof,
    });
    LexResult {
        tokens,
        diagnostics,
    }
}
/// Parse declarations, recovering at declaration and statement boundaries.
/// SE002 denotes an unexpected token or a missing required token.
pub fn parse(source: SourceId, text: &str) -> ParseResult {
    let lexed = lex(source, text);
    let mut p = Parser {
        tokens: lexed.tokens,
        pos: 0,
        diagnostics: lexed.diagnostics,
    };
    let mut items = Vec::new();
    while !p.eof() {
        let before = p.pos;
        match p.item() {
            Ok(item) => items.push(item),
            Err(()) => {
                if p.pos == before {
                    p.bump();
                }
                while !p.eof() && !["pub", "fn", "use", "type"].iter().any(|s| p.at(s)) {
                    p.bump();
                }
            }
        }
    }
    ParseResult {
        module: Module { items },
        diagnostics: p.diagnostics,
    }
}
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    diagnostics: Vec<Diagnostic>,
}
type PResult<T> = Result<T, ()>;
impl Parser {
    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }
    fn eof(&self) -> bool {
        self.current().kind == TokenKind::Eof
    }
    fn at(&self, value: &str) -> bool {
        match &self.current().kind {
            TokenKind::Word(s) | TokenKind::Symbol(s) => s == value,
            _ => false,
        }
    }
    fn bump(&mut self) -> Token {
        let t = self.current().clone();
        if !self.eof() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, s: &str) -> bool {
        if self.at(s) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn fail<T>(&mut self, message: impl Into<String>) -> PResult<T> {
        self.diagnostics
            .push(diagnostic(2, self.current().span, message));
        Err(())
    }
    fn expect(&mut self, s: &str) -> PResult<()> {
        if self.eat(s) {
            Ok(())
        } else {
            self.fail(format!("expected '{s}'"))
        }
    }
    fn span(&self, start: usize) -> Span {
        Span {
            source: self.current().span.source,
            start,
            end: self.tokens[self.pos.saturating_sub(1)].span.end.max(start),
        }
    }
    fn name(&mut self) -> PResult<String> {
        match &self.current().kind {
            TokenKind::Word(s)
                if ![
                    "pub", "fn", "use", "as", "type", "let", "var", "borrow", "share", "return",
                    "loop", "break", "continue", "if", "else", "true", "false", "while", "struct",
                    "enum", "import", "export",
                ]
                .contains(&s.as_str()) =>
            {
                let s = s.clone();
                self.bump();
                Ok(s)
            }
            _ => self.fail("expected identifier"),
        }
    }
    fn member_name(&mut self) -> PResult<String> {
        if self.at("borrow") || self.at("share") {
            let name = match &self.current().kind {
                TokenKind::Word(name) => name.clone(),
                _ => unreachable!("keyword token must be a word"),
            };
            self.bump();
            Ok(name)
        } else {
            self.name()
        }
    }
    fn path(&mut self) -> PResult<Vec<String>> {
        let mut p = vec![self.name()?];
        while self.eat("::") {
            p.push(self.name()?);
        }
        Ok(p)
    }
    fn ty(&mut self) -> PResult<Type> {
        let start = self.current().span.start;
        let path = self.path()?;
        let mut arguments = Vec::new();
        if self.eat("<") {
            if path != ["Array"] {
                return self.fail("only Array supports type arguments");
            }
            arguments.push(TypeArgument::Type(self.ty()?));
            self.expect(",")?;
            arguments.push(TypeArgument::Integer(self.integer_literal()?));
            self.expect(">")?;
        } else if path == ["Array"] {
            return self.fail("expected Array<element type, length>");
        }
        Ok(Type {
            span: self.span(start),
            path,
            arguments,
        })
    }
    fn integer_literal(&mut self) -> PResult<IntegerLiteral> {
        match self.current().kind.clone() {
            TokenKind::Number(raw) if raw.bytes().all(|b| b.is_ascii_digit() || b == b'_') => {
                let span = self.bump().span;
                Ok(IntegerLiteral { span, raw })
            }
            _ => self.fail("expected nonnegative integer literal"),
        }
    }
    fn item(&mut self) -> PResult<Item> {
        let start = self.current().span.start;
        let public = self.eat("pub");
        let kind = if self.eat("fn") {
            let name = self.name()?;
            self.expect("(")?;
            let mut parameters = Vec::new();
            while !self.at(")") && !self.eof() {
                let start = self.current().span.start;
                let mutable = self.eat("var");
                let name = self.name()?;
                self.expect(":")?;
                let access = if self.eat("borrow") {
                    Access::Borrow
                } else if self.eat("share") {
                    Access::Share
                } else {
                    Access::Owned
                };
                let ty = self.ty()?;
                parameters.push(Parameter {
                    span: self.span(start),
                    mutable,
                    name,
                    access,
                    ty,
                });
                if !self.eat(",") {
                    break;
                }
            }
            self.expect(")")?;
            let result = if self.eat("->") {
                Some(self.ty()?)
            } else {
                None
            };
            let body = self.block()?;
            ItemKind::Function {
                public,
                name,
                parameters,
                result,
                body,
            }
        } else if self.eat("use") {
            let path = self.path()?;
            let alias = if self.eat("as") {
                Some(self.name()?)
            } else {
                None
            };
            self.expect(";")?;
            ItemKind::Use {
                public,
                path,
                alias,
            }
        } else if self.eat("type") {
            let name = self.name()?;
            let definition = if self.eat("=") {
                let ty = self.ty()?;
                self.expect(";")?;
                TypeDefinition::Alias(ty)
            } else if self.eat("{") {
                let mut fields = Vec::new();
                while !self.at("}") && !self.eof() {
                    let start = self.current().span.start;
                    let public = self.eat("pub");
                    let name = self.name()?;
                    self.expect(":")?;
                    let ty = self.ty()?;
                    fields.push(Field {
                        span: self.span(start),
                        public,
                        name,
                        ty,
                    });
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("}")?;
                TypeDefinition::Struct(fields)
            } else if self.eat("[") {
                let mut variants = Vec::new();
                while !self.at("]") && !self.eof() {
                    let start = self.current().span.start;
                    let name = self.name()?;
                    let mut payload = Vec::new();
                    if self.eat("(") {
                        while !self.at(")") && !self.eof() {
                            payload.push(self.ty()?);
                            if !self.eat(",") {
                                break;
                            }
                        }
                        self.expect(")")?;
                    }
                    variants.push(Variant {
                        span: self.span(start),
                        name,
                        payload,
                    });
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("]")?;
                TypeDefinition::Enum(variants)
            } else {
                return self.fail("expected '=', '{', or '[' after type name");
            };
            ItemKind::Type {
                public,
                name,
                definition,
            }
        } else {
            return self.fail("expected function, type, or use declaration");
        };
        Ok(Node {
            span: self.span(start),
            kind,
        })
    }
    fn block(&mut self) -> PResult<Block> {
        let start = self.current().span.start;
        self.expect("{")?;
        let mut statements = Vec::new();
        let mut tail = None;
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            match self.statement() {
                Ok((Some(s), _)) => statements.push(s),
                Ok((None, Some(e))) => {
                    tail = Some(Box::new(e));
                    break;
                }
                Ok(_) => {}
                Err(()) => {
                    if self.pos == before {
                        self.bump();
                    }
                    let mut depth = 0;
                    while !self.eof() {
                        if self.at("}") && depth == 0 {
                            break;
                        }
                        if self.at("{") {
                            depth += 1;
                        }
                        if self.at("}") {
                            depth -= 1;
                        }
                        if self.eat(";") && depth == 0 {
                            break;
                        }
                        self.bump();
                    }
                }
            }
        }
        self.expect("}")?;
        Ok(Block {
            span: self.span(start),
            statements,
            tail,
        })
    }
    fn statement(&mut self) -> PResult<(Option<Statement>, Option<Expr>)> {
        let start = self.current().span.start;
        let kind = if self.at("let") || self.at("var") {
            let mutable = self.eat("var");
            if !mutable {
                self.expect("let")?;
            }
            let name = self.name()?;
            let annotation = if self.eat(":=") {
                None
            } else {
                self.expect(":")?;
                let ty = self.ty()?;
                self.expect("=")?;
                Some(ty)
            };
            let value = self.expr(0)?;
            self.expect(";")?;
            StatementKind::Binding {
                mutable,
                name,
                annotation,
                value,
            }
        } else if self.eat("return") {
            let value = if self.at(";") {
                None
            } else {
                Some(self.expr(0)?)
            };
            self.expect(";")?;
            StatementKind::Return(value)
        } else if self.eat("loop") {
            StatementKind::Loop(self.block()?)
        } else if self.eat("break") {
            self.expect(";")?;
            StatementKind::Break
        } else if self.eat("continue") {
            self.expect(";")?;
            StatementKind::Continue
        } else {
            let e = self.expr(0)?;
            if ["=", "+=", "-=", "*=", "/=", "%="]
                .iter()
                .any(|s| self.at(s))
            {
                let operator = match self.bump().kind {
                    TokenKind::Symbol(s) => s,
                    _ => unreachable!(),
                };
                let value = self.expr(0)?;
                self.expect(";")?;
                StatementKind::Assign {
                    target: e,
                    operator,
                    value,
                }
            } else if self.eat(";") {
                StatementKind::Expression(e)
            } else if self.at("}") {
                return Ok((None, Some(e)));
            } else if matches!(e.kind, ExprKind::If { .. } | ExprKind::Block(_)) {
                StatementKind::Expression(e)
            } else {
                return self.fail("expected ';' or block end after expression");
            }
        };
        Ok((
            Some(Node {
                span: self.span(start),
                kind,
            }),
            None,
        ))
    }
    fn expr(&mut self, minimum: u8) -> PResult<Expr> {
        let start = self.current().span.start;
        let mut left = if self.at("-") || self.at("!") || self.at("+") {
            let operator = match self.bump().kind {
                TokenKind::Symbol(s) => s,
                _ => unreachable!(),
            };
            let operand = Box::new(self.expr(13)?);
            Node {
                span: self.span(start),
                kind: ExprKind::Unary { operator, operand },
            }
        } else if self.eat("[") {
            let kind = if self.eat("]") {
                ExprKind::Array(Vec::new())
            } else {
                let first = self.expr(0)?;
                if self.eat(";") {
                    let count = self.integer_literal()?;
                    self.expect("]")?;
                    ExprKind::RepeatArray {
                        value: Box::new(first),
                        count,
                    }
                } else {
                    let mut elements = vec![first];
                    while self.eat(",") && !self.at("]") {
                        elements.push(self.expr(0)?);
                    }
                    self.expect("]")?;
                    ExprKind::Array(elements)
                }
            };
            Node {
                span: self.span(start),
                kind,
            }
        } else if self.at("{") {
            let b = self.block()?;
            Node {
                span: b.span,
                kind: ExprKind::Block(b),
            }
        } else if self.eat("if") {
            let condition = Box::new(self.expr(0)?);
            let then_branch = self.block()?;
            let else_branch = if self.eat("else") {
                if !self.at("if") && !self.at("{") {
                    return self.fail("expected 'if' or block after 'else'");
                }
                Some(Box::new(self.expr(0)?))
            } else {
                None
            };
            Node {
                span: self.span(start),
                kind: ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                },
            }
        } else if self.eat("(") {
            let e = self.expr(0)?;
            self.expect(")")?;
            Node {
                span: self.span(start),
                kind: e.kind,
            }
        } else {
            let kind = match self.current().kind.clone() {
                TokenKind::Number(n) => {
                    self.bump();
                    ExprKind::Number(n)
                }
                TokenKind::Word(s) if s == "true" || s == "false" => {
                    self.bump();
                    ExprKind::Bool(s == "true")
                }
                TokenKind::Word(_) => ExprKind::Path(self.path()?),
                _ => return self.fail("expected expression"),
            };
            Node {
                span: self.span(start),
                kind,
            }
        };
        loop {
            if minimum <= 15 && self.eat("[") {
                let index = Box::new(self.expr(0)?);
                self.expect("]")?;
                left = Node {
                    span: self.span(start),
                    kind: ExprKind::Index {
                        base: Box::new(left),
                        index,
                    },
                };
                continue;
            }
            if minimum <= 15 && self.eat("(") {
                let mut arguments = Vec::new();
                while !self.at(")") && !self.eof() {
                    arguments.push(self.expr(0)?);
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect(")")?;
                left = Node {
                    span: self.span(start),
                    kind: ExprKind::Call {
                        callee: Box::new(left),
                        arguments,
                    },
                };
                continue;
            }
            if minimum <= 15 && self.eat(".") {
                let name = self.member_name()?;
                left = Node {
                    span: self.span(start),
                    kind: ExprKind::Field {
                        base: Box::new(left),
                        name,
                    },
                };
                continue;
            }
            let (operator, power) = match &self.current().kind {
                TokenKind::Symbol(s) => (
                    s.clone(),
                    match s.as_str() {
                        "||" => 1,
                        "&&" => 3,
                        "==" | "!=" => 5,
                        "<" | "<=" | ">" | ">=" => 7,
                        "+" | "-" => 9,
                        "*" | "/" | "%" => 11,
                        _ => break,
                    },
                ),
                _ => break,
            };
            if power < minimum {
                break;
            }
            self.bump();
            let right = Box::new(self.expr(power + 1)?);
            left = Node {
                span: self.span(start),
                kind: ExprKind::Binary {
                    operator,
                    left: Box::new(left),
                    right,
                },
            };
        }
        Ok(left)
    }
}
