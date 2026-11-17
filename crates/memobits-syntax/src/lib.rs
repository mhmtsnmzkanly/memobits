//! Source-spanned syntax for the initial Memobits language subset.
//! Parsing does not perform name, type, ownership, or control-flow checks.
pub mod templates;

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
        base: Option<Type>,
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
    Reference {
        span: Span,
        access: Access,
        referent: Type,
    },
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
    /// `let Type { field, field: alias } := value;` (or `var`). Every field is
    /// named; the parser does not check them against the declaration.
    Destructure {
        mutable: bool,
        path: Vec<String>,
        fields: Vec<FieldPattern>,
        value: Expr,
    },
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
    StringLiteral(String),
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
    /// `Name { field: value, ... }`. Field initialisers keep source order; the
    /// parser does not check that they match the type's declaration.
    Struct {
        path: Vec<String>,
        fields: Vec<FieldInit>,
    },
    Block(Block),
    If {
        condition: Box<Expr>,
        then_branch: Block,
        else_branch: Option<Box<Expr>>,
    },
    /// `match scrutinee { Pattern => expr, ... }`. Arms keep source order.
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
}
#[derive(Clone, Debug, PartialEq)]
pub struct MatchArm {
    pub span: Span,
    pub pattern: Pattern,
    pub body: Expr,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Pattern {
    pub span: Span,
    pub kind: PatternKind,
}
#[derive(Clone, Debug, PartialEq)]
pub enum PatternKind {
    /// `_`: matches any value.
    Wildcard,
    /// `Type::Variant` or `Type::Variant(a, _)`; a unit variant has no slots.
    /// The parser does not check the path against any declaration.
    Variant {
        path: Vec<String>,
        slots: Vec<PatternSlot>,
    },
}
/// One payload slot of a variant pattern: an identifier, or `_` (`name: None`).
#[derive(Clone, Debug, PartialEq)]
pub struct PatternSlot {
    pub span: Span,
    pub name: Option<String>,
}
/// One `field` or `field: alias` entry of a destructuring pattern.
#[derive(Clone, Debug, PartialEq)]
pub struct FieldPattern {
    pub span: Span,
    pub field: String,
    pub binding: String,
}
#[derive(Clone, Debug, PartialEq)]
pub struct FieldInit {
    pub span: Span,
    pub name: String,
    pub value: Expr,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Word(String),
    Number(String),
    StringLiteral(String),
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
/// SE001 denotes a lexical error.
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
        let kind = if c == '"' {
            let (end, token) = lex_string(source, text, start, &mut diagnostics);
            i = end;
            token
        } else if c == '_' || c.is_alphabetic() {
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
            "::", ":=", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=",
            "%=",
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

fn lex_string(
    source: SourceId,
    text: &str,
    start: usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> (usize, TokenKind) {
    let body = start + 1;
    let mut escaped = false;
    let mut reported_escape = false;
    for (offset, c) in text[body..].char_indices() {
        let end = body + offset;
        if matches!(c, '\n' | '\r') {
            diagnostics.push(diagnostic(
                1,
                Span { source, start, end },
                "newline in string literal",
            ));
            return (end, TokenKind::StringLiteral(text[body..end].into()));
        }
        if escaped {
            // Skip an escaped quote for recovery only. The literal is invalid.
            escaped = false;
        } else if c == '"' {
            return (end + 1, TokenKind::StringLiteral(text[body..end].into()));
        } else if c == '\\' {
            if !reported_escape {
                diagnostics.push(diagnostic(
                    1,
                    Span {
                        source,
                        start: end,
                        end: end + 1,
                    },
                    "escapes in string literals are not supported yet",
                ));
                reported_escape = true;
            }
            escaped = true;
        }
    }
    let end = text.len();
    diagnostics.push(diagnostic(
        1,
        Span { source, start, end },
        "unterminated string literal",
    ));
    (end, TokenKind::StringLiteral(text[body..end].into()))
}

/// Parse declarations, recovering at declaration and statement boundaries.
/// SE002 denotes an unexpected token or a missing required token.
pub fn parse(source: SourceId, text: &str) -> ParseResult {
    let lexed = lex(source, text);
    let mut p = Parser {
        tokens: lexed.tokens,
        pos: 0,
        no_struct: false,
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
    /// True while parsing an `if` condition: there a `{` after an expression
    /// starts the branch block, so a struct literal needs parentheses.
    no_struct: bool,
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
                    "enum", "import", "export", "match",
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
            let Some(template) = templates::lookup_applied(&path) else {
                return self.fail("only compiler-known templates support type arguments");
            };
            if template.parameters.is_empty() {
                return self.fail(template.argument_error);
            }
            for (index, parameter) in template.parameters.iter().enumerate() {
                if index > 0 {
                    self.expect(",")?;
                }
                arguments.push(match parameter {
                    templates::ParameterKind::Type | templates::ParameterKind::ErrorType => {
                        let start = self.current().span.start;
                        let access = self.access();
                        let referent = self.ty()?;
                        match access {
                            Access::Owned => TypeArgument::Type(referent),
                            Access::Borrow | Access::Share => TypeArgument::Reference {
                                span: self.span(start),
                                access,
                                referent,
                            },
                        }
                    }
                    templates::ParameterKind::Integer => {
                        TypeArgument::Integer(self.integer_literal()?)
                    }
                });
            }
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
    fn access(&mut self) -> Access {
        if self.eat("borrow") {
            Access::Borrow
        } else if self.eat("share") {
            Access::Share
        } else {
            Access::Owned
        }
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
                let access = self.access();
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
            let base = if self.eat(":") {
                Some(self.ty()?)
            } else {
                None
            };
            if base.is_some() && !self.at("{") {
                return self.fail("a derived error type requires a field body");
            }
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
                base,
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
        let saved = std::mem::replace(&mut self.no_struct, false);
        let block = self.block_inner();
        self.no_struct = saved;
        block
    }
    fn block_inner(&mut self) -> PResult<Block> {
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
    /// A binding head `Name {` or `a::Name {` marks a destructuring pattern.
    fn at_destructure(&self) -> bool {
        let mut at = self.pos;
        loop {
            if !matches!(
                self.tokens.get(at),
                Some(Token {
                    kind: TokenKind::Word(_),
                    ..
                })
            ) {
                return false;
            }
            match self.tokens.get(at + 1) {
                Some(Token {
                    kind: TokenKind::Symbol(s),
                    ..
                }) if s == "{" => return true,
                Some(Token {
                    kind: TokenKind::Symbol(s),
                    ..
                }) if s == "::" => at += 2,
                _ => return false,
            }
        }
    }
    /// `{ field, field: alias, ... }`. Nested patterns and `..` are gated.
    fn field_patterns(&mut self) -> PResult<Vec<FieldPattern>> {
        self.expect("{")?;
        let mut fields = Vec::new();
        while !self.at("}") && !self.eof() {
            let start = self.current().span.start;
            if self.at(".") {
                return self
                    .fail("`..` in a destructuring pattern is not supported; name every field");
            }
            let field = self.name()?;
            let binding = if self.eat(":") {
                let alias = self.name()?;
                if self.at("{") || self.at("::") {
                    return self.fail(
                        "nested destructuring patterns are not supported yet; bind the field to a name",
                    );
                }
                alias
            } else {
                if self.at("{") {
                    return self.fail(
                        "nested destructuring patterns are not supported yet; bind the field to a name",
                    );
                }
                field.clone()
            };
            fields.push(FieldPattern {
                span: self.span(start),
                field,
                binding,
            });
            if !self.eat(",") {
                break;
            }
        }
        self.expect("}")?;
        Ok(fields)
    }
    fn statement(&mut self) -> PResult<(Option<Statement>, Option<Expr>)> {
        let start = self.current().span.start;
        let kind = if self.at("let") || self.at("var") {
            let mutable = self.eat("var");
            if !mutable {
                self.expect("let")?;
            }
            if self.at_destructure() {
                let path = self.path()?;
                let fields = self.field_patterns()?;
                self.expect(":=")?;
                let value = self.expr(0)?;
                self.expect(";")?;
                return Ok((
                    Some(Statement {
                        span: self.span(start),
                        kind: StatementKind::Destructure {
                            mutable,
                            path,
                            fields,
                            value,
                        },
                    }),
                    None,
                ));
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
            // A block-like expression at the start of a statement ends at its
            // closing brace: no postfix or binary continuation.
            let block_start = self.at("{") || self.at("if") || self.at("match");
            let e = if block_start {
                self.block_like(true)?
            } else {
                self.expr(0)?
            };
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
            } else if block_start {
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
    /// Parses a bare block or an `if`/`else` chain, starting at `{` or `if`.
    /// In statement position (`statement == true`) the `else` chain is also
    /// parsed block-only, so the statement ends at its final `}`. Elsewhere the
    /// `else` operand keeps its original full-expression parsing.
    fn block_like(&mut self, statement: bool) -> PResult<Expr> {
        let start = self.current().span.start;
        if self.at("{") {
            let b = self.block()?;
            return Ok(Node {
                span: b.span,
                kind: ExprKind::Block(b),
            });
        }
        if self.at("match") {
            return self.match_expr();
        }
        self.expect("if")?;
        let saved = std::mem::replace(&mut self.no_struct, true);
        let condition = self.expr(0);
        self.no_struct = saved;
        let condition = Box::new(condition?);
        let then_branch = self.block()?;
        let else_branch = if self.eat("else") {
            if !self.at("if") && !self.at("{") {
                return self.fail("expected 'if' or block after 'else'");
            }
            Some(Box::new(if statement {
                self.block_like(true)?
            } else {
                self.expr(0)?
            }))
        } else {
            None
        };
        Ok(Node {
            span: self.span(start),
            kind: ExprKind::If {
                condition,
                then_branch,
                else_branch,
            },
        })
    }
    /// `match scrutinee { pattern => body, ... }`, starting at `match`. An arm
    /// whose body is block-like (`{`, `if`, `match`) may omit its comma.
    fn match_expr(&mut self) -> PResult<Expr> {
        let start = self.current().span.start;
        self.expect("match")?;
        let saved = std::mem::replace(&mut self.no_struct, true);
        let scrutinee = self.expr(0);
        self.no_struct = saved;
        let scrutinee = Box::new(scrutinee?);
        self.expect("{")?;
        let mut arms = Vec::new();
        self.nested(|p| {
            while !p.at("}") && !p.eof() {
                let arm_start = p.current().span.start;
                let pattern = p.pattern()?;
                if p.at("if") {
                    return p.fail("match guards are not supported yet");
                }
                p.expect("=>")?;
                let block_start = p.at("{") || p.at("if") || p.at("match");
                let body = if block_start {
                    p.block_like(true)?
                } else if p.at("return") || p.at("break") || p.at("continue") {
                    p.divergent_arm()?
                } else {
                    p.expr(0)?
                };
                arms.push(MatchArm {
                    span: p.span(arm_start),
                    pattern,
                    body,
                });
                if !p.eat(",") && !block_start && !p.at("}") {
                    return p.fail("expected ',' or '}' after match arm");
                }
            }
            Ok(())
        })?;
        self.expect("}")?;
        Ok(Node {
            span: self.span(start),
            kind: ExprKind::Match { scrutinee, arms },
        })
    }
    /// `return [expr]`, `break` or `continue` written directly as an arm body.
    /// It is parsed as a one-statement block, which never falls through.
    fn divergent_arm(&mut self) -> PResult<Expr> {
        let start = self.current().span.start;
        let kind = if self.eat("return") {
            let value = if self.at(",") || self.at("}") {
                None
            } else {
                Some(self.expr(0)?)
            };
            StatementKind::Return(value)
        } else if self.eat("break") {
            StatementKind::Break
        } else {
            self.expect("continue")?;
            StatementKind::Continue
        };
        let span = self.span(start);
        Ok(Node {
            span,
            kind: ExprKind::Block(Block {
                span,
                statements: vec![Node { span, kind }],
                tail: None,
            }),
        })
    }
    fn pattern(&mut self) -> PResult<Pattern> {
        let start = self.current().span.start;
        if matches!(self.current().kind, TokenKind::Number(_))
            || self.at("true")
            || self.at("false")
            || self.at("-")
        {
            return self.fail("literal patterns are not supported yet; match on enum variants");
        }
        let path = self.path()?;
        if path == ["_"] {
            return Ok(Pattern {
                span: self.span(start),
                kind: PatternKind::Wildcard,
            });
        }
        if self.at("{") {
            return self.fail("struct patterns are not supported in `match` yet");
        }
        let mut slots = Vec::new();
        if self.eat("(") {
            while !self.at(")") && !self.eof() {
                let slot_start = self.current().span.start;
                if matches!(self.current().kind, TokenKind::Number(_))
                    || self.at("true")
                    || self.at("false")
                    || self.at("-")
                {
                    return self.fail("literal patterns are not supported yet");
                }
                let name = self.name()?;
                if self.at("(") || self.at("::") || self.at("{") {
                    return self.fail(
                        "nested patterns are not supported yet; bind the payload and match it in a second `match`",
                    );
                }
                slots.push(PatternSlot {
                    span: self.span(slot_start),
                    name: (name != "_").then_some(name),
                });
                if !self.eat(",") {
                    break;
                }
            }
            self.expect(")")?;
        }
        Ok(Pattern {
            span: self.span(start),
            kind: PatternKind::Variant { path, slots },
        })
    }
    /// Parse inside delimiters, where a `{` can no longer be mistaken for the
    /// block that follows an `if` condition.
    fn nested<T>(&mut self, parse: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        let saved = std::mem::replace(&mut self.no_struct, false);
        let result = parse(self);
        self.no_struct = saved;
        result
    }
    /// At `{`: whether `word :` follows, which no block statement can start with.
    fn looks_like_struct_fields(&self) -> bool {
        matches!(
            (self.tokens.get(self.pos + 1), self.tokens.get(self.pos + 2)),
            (
                Some(Token { kind: TokenKind::Word(_), .. }),
                Some(Token { kind: TokenKind::Symbol(colon), .. })
            ) if colon == ":"
        )
    }
    fn array_literal_rest(&mut self) -> PResult<ExprKind> {
        if self.eat("]") {
            return Ok(ExprKind::Array(Vec::new()));
        }
        let first = self.expr(0)?;
        if self.eat(";") {
            let count = self.integer_literal()?;
            self.expect("]")?;
            Ok(ExprKind::RepeatArray {
                value: Box::new(first),
                count,
            })
        } else {
            let mut elements = vec![first];
            while self.eat(",") && !self.at("]") {
                elements.push(self.expr(0)?);
            }
            self.expect("]")?;
            Ok(ExprKind::Array(elements))
        }
    }
    /// `{ name: expression, ... }` after a struct literal's path.
    fn struct_fields(&mut self) -> PResult<Vec<FieldInit>> {
        self.expect("{")?;
        let mut fields = Vec::new();
        while !self.at("}") && !self.eof() {
            let start = self.current().span.start;
            let name = self.name()?;
            if self.at(",") || self.at("}") {
                return self.fail(format!(
                    "struct literal field '{name}' needs a value: write '{name}: expression' (shorthand is not supported)"
                ));
            }
            self.expect(":")?;
            let value = self.expr(0)?;
            fields.push(FieldInit {
                span: self.span(start),
                name,
                value,
            });
            if !self.eat(",") {
                break;
            }
        }
        self.expect("}")?;
        Ok(fields)
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
            let kind = self.nested(Self::array_literal_rest)?;
            Node {
                span: self.span(start),
                kind,
            }
        } else if self.at("{") || self.at("if") || self.at("match") {
            self.block_like(false)?
        } else if self.eat("(") {
            let e = self.nested(|p| p.expr(0))?;
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
                TokenKind::StringLiteral(text) => {
                    self.bump();
                    ExprKind::StringLiteral(text)
                }
                TokenKind::Word(s) if s == "true" || s == "false" => {
                    self.bump();
                    ExprKind::Bool(s == "true")
                }
                TokenKind::Word(_) => {
                    let path = self.path()?;
                    if self.at("{") && self.no_struct && self.looks_like_struct_fields() {
                        return self.fail(
                            "a struct literal is not allowed directly in an `if` condition or `match` scrutinee; wrap it in parentheses",
                        );
                    }
                    if self.at("{") && !self.no_struct {
                        let fields = self.nested(Self::struct_fields)?;
                        ExprKind::Struct { path, fields }
                    } else {
                        ExprKind::Path(path)
                    }
                }
                _ => return self.fail("expected expression"),
            };
            Node {
                span: self.span(start),
                kind,
            }
        };
        loop {
            if minimum <= 15 && self.eat("[") {
                let index = Box::new(self.nested(|p| p.expr(0))?);
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
                let arguments = self.nested(|p| {
                    let mut arguments = Vec::new();
                    while !p.at(")") && !p.eof() {
                        arguments.push(p.expr(0)?);
                        if !p.eat(",") {
                            break;
                        }
                    }
                    Ok(arguments)
                })?;
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
