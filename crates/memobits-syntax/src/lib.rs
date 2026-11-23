//! Source-spanned syntax for the initial Memobits language subset.
//! Parsing does not perform name, type, ownership, or control-flow checks.
mod items;
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
        external: bool,
        name: String,
        generic_parameters: Vec<GenericParameter>,
        bounds: Vec<WhereBound>,
        parameters: Vec<Parameter>,
        result: Option<Type>,
        body: Block,
    },
    Use {
        public: bool,
        path: Vec<String>,
        alias: Option<String>,
        group: Vec<UseMember>,
    },
    Type {
        public: bool,
        name: String,
        generic_parameters: Vec<GenericParameter>,
        bounds: Vec<WhereBound>,
        definition: TypeDefinition,
        base: Option<Type>,
    },
    Interface {
        public: bool,
        name: String,
        associated_types: Vec<String>,
        methods: Vec<InterfaceMethod>,
    },
    Extension {
        public: bool,
        target: Type,
        interface: Type,
        associated_types: Vec<AssociatedTypeBinding>,
        methods: Vec<InterfaceMethod>,
    },
    InherentExtension {
        public: bool,
        target: Type,
        generic_parameters: Vec<GenericParameter>,
        methods: Vec<InterfaceMethod>,
    },
}
#[derive(Clone, Debug, PartialEq)]
pub struct UseMember {
    pub name: String,
    pub alias: Option<String>,
}
#[derive(Clone, Debug, PartialEq)]
pub struct GenericParameter {
    pub span: Span,
    pub name: String,
    pub kind: GenericParameterKind,
}
#[derive(Clone, Debug, PartialEq)]
pub enum GenericParameterKind {
    Type,
    Const(Type),
}
#[derive(Clone, Debug, PartialEq)]
pub struct WhereBound {
    pub span: Span,
    pub parameter: String,
    pub interface: Type,
}
#[derive(Clone, Debug, PartialEq)]
pub struct InterfaceMethod {
    pub span: Span,
    pub public: bool,
    pub name: String,
    pub receiver: Access,
    pub parameters: Vec<Parameter>,
    pub result: Option<Type>,
    pub body: Option<Block>,
}
#[derive(Clone, Debug, PartialEq)]
pub struct AssociatedTypeBinding {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
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
    TupleField {
        label: Option<String>,
        ty: Box<Type>,
    },
    Const(String),
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
    Bodyless,
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
    /// `let (first, second) := value;`. Every tuple slot is bound by name.
    TupleDestructure {
        mutable: bool,
        elements: Vec<TupleBinding>,
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
    ForEach {
        binding: String,
        items: Expr,
        body: Block,
    },
    Break,
    Continue,
}
#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Array(Vec<Expr>),
    Tuple(Vec<TupleElement>),
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
    CharLiteral(char),
    Bool(bool),
    Path(Vec<String>),
    Unary {
        operator: String,
        operand: Box<Expr>,
    },
    Cast {
        value: Box<Expr>,
        target: Type,
    },
    Binary {
        operator: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
        interface: Option<Type>,
    },
    Field {
        base: Box<Expr>,
        name: String,
    },
    /// `Name { field: value, ... }`. Field initialisers keep source order; the
    /// parser does not check that they match the type's declaration.
    Struct {
        path: Vec<String>,
        type_arguments: Vec<TypeArgument>,
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
pub struct TupleBinding {
    pub span: Span,
    pub binding: String,
    pub nested: Option<Vec<TupleBinding>>,
}
#[derive(Clone, Debug, PartialEq)]
pub struct FieldInit {
    pub span: Span,
    pub name: String,
    pub value: Expr,
}
#[derive(Clone, Debug, PartialEq)]
pub struct TupleElement {
    pub span: Span,
    pub label: Option<String>,
    pub value: Expr,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Word(String),
    Number(String),
    StringLiteral(String),
    CharLiteral(char),
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
    /// Non-failing migration warnings (`MW` codes); they never make a parse fail.
    pub warnings: Vec<Diagnostic>,
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
        } else if c == '\'' {
            let (end, token) = lex_char(source, text, start, &mut diagnostics);
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
            "%=", "&=", "|=", "^=", "<<=", ">>=",
        ]
        .into_iter()
        .find(|op| text[i..].starts_with(op))
        {
            i += op.len();
            TokenKind::Symbol(op.into())
        } else if "(){}[],:;=+-*/%!<>&|^.?".contains(c) {
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

fn lex_char(
    source: SourceId,
    text: &str,
    start: usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> (usize, TokenKind) {
    let mut cursor = start + 1;
    let mut value = None;
    if cursor < text.len() && text.as_bytes()[cursor] == b'\\' {
        cursor += 1;
        if cursor >= text.len() {
            value = None;
        } else {
            let escaped = text[cursor..].chars().next().unwrap();
            cursor += escaped.len_utf8();
            value = Some(match escaped {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '0' => '\0',
                '\\' => '\\',
                '\'' => '\'',
                _ => '\u{fffd}',
            });
            if !matches!(escaped, 'n' | 'r' | 't' | '0' | '\\' | '\'') {
                diagnostics.push(diagnostic(
                    1,
                    Span {
                        source,
                        start,
                        end: cursor,
                    },
                    "unsupported escape in character literal",
                ));
            }
        }
    } else if cursor < text.len() {
        let scalar = text[cursor..].chars().next().unwrap();
        if !matches!(scalar, '\n' | '\r' | '\'') {
            value = Some(scalar);
            cursor += scalar.len_utf8();
        }
    }
    if cursor < text.len() && text.as_bytes()[cursor] == b'\'' {
        cursor += 1;
        if let Some(value) = value {
            return (cursor, TokenKind::CharLiteral(value));
        }
    }
    while cursor < text.len() && !matches!(text.as_bytes()[cursor], b'\'' | b'\n' | b'\r') {
        cursor += text[cursor..].chars().next().unwrap().len_utf8();
    }
    if cursor < text.len() && text.as_bytes()[cursor] == b'\'' {
        cursor += 1;
    }
    diagnostics.push(diagnostic(
        1,
        Span {
            source,
            start,
            end: cursor,
        },
        "character literal must contain exactly one Unicode scalar value",
    ));
    (cursor, TokenKind::CharLiteral('\u{fffd}'))
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
        warnings: Vec::new(),
        pending: Vec::new(),
    };
    let mut items = Vec::new();
    while !p.eof() {
        let before = p.pos;
        match p.item() {
            Ok(item) => match &item.kind {
                ItemKind::Use {
                    public,
                    path,
                    group,
                    ..
                } if !group.is_empty() => {
                    for member in group {
                        let mut qualified = path.clone();
                        qualified.push(member.name.clone());
                        items.push(Node {
                            span: item.span,
                            kind: ItemKind::Use {
                                public: *public,
                                path: qualified,
                                alias: member.alias.clone(),
                                group: Vec::new(),
                            },
                        });
                    }
                }
                _ => items.push(item),
            },
            Err(()) => {
                if p.pos == before {
                    p.bump();
                }
                while !p.eof()
                    && !["pub", "fn", "use", "type", "interface", "extend"]
                        .iter()
                        .any(|s| p.at(s))
                {
                    p.bump();
                }
            }
        }
        items.append(&mut p.pending);
    }
    ParseResult {
        module: Module { items },
        diagnostics: p.diagnostics,
        warnings: p.warnings,
    }
}
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    /// A following brace starts a control-flow block. Struct literals need parentheses.
    no_struct: bool,
    diagnostics: Vec<Diagnostic>,
    warnings: Vec<Diagnostic>,
    pending: Vec<Item>,
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
    fn next_at(&self, value: &str) -> bool {
        self.tokens
            .get(self.pos + 1)
            .is_some_and(|token| match &token.kind {
                TokenKind::Word(s) | TokenKind::Symbol(s) => s == value,
                _ => false,
            })
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
        if let TokenKind::Number(raw) = &self.current().kind {
            if raw
                .bytes()
                .all(|byte| byte.is_ascii_digit() || byte == b'_')
            {
                let member = raw.replace('_', "");
                self.bump();
                return Ok(member);
            }
        }
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
    fn tuple_label_ahead(&self) -> bool {
        matches!(self.current().kind, TokenKind::Word(_)) && self.next_at(":")
    }
    fn path(&mut self) -> PResult<Vec<String>> {
        let mut p = vec![self.name()?];
        while self.eat("::") {
            p.push(self.name()?);
        }
        Ok(p)
    }
    pub(crate) fn import_path(&mut self) -> PResult<Vec<String>> {
        let mut path = vec![self.name()?];
        while self.at("::") && !self.next_at("{") {
            self.bump();
            path.push(self.name()?);
        }
        Ok(path)
    }
    /// A type including the `T ! E` fallible operator (`Result<T, E>`).
    /// `?` binds tighter than `!`; the error side is a single postfix type.
    fn ty(&mut self) -> PResult<Type> {
        let start = self.current().span.start;
        let value = self.ty_postfix()?;
        if !self.eat("!") {
            return Ok(value);
        }
        let error = self.ty_postfix()?;
        Ok(Type {
            span: self.span(start),
            path: vec!["Result".into()],
            arguments: vec![TypeArgument::Type(value), TypeArgument::Type(error)],
        })
    }
    /// A type without the `!` operator: optional suffixes bind here.
    fn ty_postfix(&mut self) -> PResult<Type> {
        let start = self.current().span.start;
        if self.at("{") {
            self.expect("{")?;
            if self.at("}") {
                return self.fail("an anonymous record type needs at least one named field");
            }
            let mut fields = Vec::new();
            while !self.at("}") && !self.eof() {
                let label = self.name()?;
                self.expect(":")?;
                let ty = self.ty()?;
                fields.push(TypeArgument::TupleField {
                    label: Some(label),
                    ty: Box::new(ty),
                });
                if !self.eat(",") {
                    break;
                }
            }
            self.expect("}")?;
            return Ok(Type {
                span: self.span(start),
                path: vec!["\0record".into()],
                arguments: fields,
            });
        }
        if self.eat("enum") {
            self.expect("[")?;
            let mut path = vec!["\0enum".into()];
            let mut arguments = Vec::new();
            while !self.at("]") && !self.eof() {
                let variant = self.name()?;
                path.push(variant.clone());
                if self.at("(") {
                    self.expect("(")?;
                    let mut payload = Vec::new();
                    while !self.at(")") && !self.eof() {
                        payload.push(TypeArgument::Type(self.ty()?));
                        if !self.eat(",") {
                            break;
                        }
                    }
                    self.expect(")")?;
                    if !payload.is_empty() {
                        arguments.push(TypeArgument::TupleField {
                            label: Some(variant),
                            ty: Box::new(Type {
                                span: self.span(start),
                                path: vec!["\0tuple".into()],
                                arguments: payload,
                            }),
                        });
                    }
                }
                if !self.eat(",") {
                    break;
                }
            }
            self.expect("]")?;
            if path.len() == 1 {
                return self.fail("an anonymous enum type needs at least one variant");
            }
            return Ok(Type {
                span: self.span(start),
                path,
                arguments,
            });
        }
        if self.eat("(") {
            if self.eat(")") {
                return Ok(Type {
                    span: self.span(start),
                    path: vec!["\0tuple".into()],
                    arguments: Vec::new(),
                });
            }
            let first_label = if self.tuple_label_ahead() {
                let name = self.name()?;
                self.expect(":")?;
                Some(name)
            } else {
                None
            };
            let access_start = self.current().span.start;
            let access = self.access();
            let referent = self.ty()?;
            let reference_span = self.span(access_start);
            if access == Access::Owned && self.eat(",") {
                let mut elements = vec![TypeArgument::TupleField {
                    label: first_label,
                    ty: Box::new(referent),
                }];
                while !self.at(")") && !self.eof() {
                    let label = if self.tuple_label_ahead() {
                        let name = self.name()?;
                        self.expect(":")?;
                        Some(name)
                    } else {
                        None
                    };
                    elements.push(TypeArgument::TupleField {
                        label,
                        ty: Box::new(self.ty()?),
                    });
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect(")")?;
                return Ok(Type {
                    span: self.span(start),
                    path: vec!["\0tuple".into()],
                    arguments: elements,
                });
            }
            if first_label.is_some() {
                return self.fail("a labeled tuple type needs tuple delimiters");
            }
            self.expect(")")?;
            if access != Access::Owned {
                if !self.eat("?") {
                    return self.fail("parenthesized reference types require an optional suffix");
                }
                return Ok(Type {
                    span: self.span(start),
                    path: vec!["Option".into()],
                    arguments: vec![TypeArgument::Reference {
                        span: reference_span,
                        access,
                        referent,
                    }],
                });
            }
            let mut ty = referent;
            while self.eat("?") {
                ty = Type {
                    span: self.span(start),
                    path: vec!["Option".into()],
                    arguments: vec![TypeArgument::Type(ty)],
                };
            }
            return Ok(ty);
        }
        let mut path = self.path()?;
        if path.len() == 1 {
            // Lowercase built-in spellings map onto the existing built-in types.
            match path[0].as_str() {
                "bool" => path[0] = "Bool".into(),
                "char" => path[0] = "Char".into(),
                "array" => path[0] = "Array".into(),
                _ => {}
            }
        }
        let mut arguments = Vec::new();
        if self.eat("<") {
            let template = templates::lookup_applied(&path);
            let mut index = 0;
            while !self.at(">") && !self.eof() {
                if index > 0 {
                    self.expect(",")?;
                }
                let parameter = template.and_then(|t| t.parameters.get(index));
                arguments.push(match parameter {
                    Some(templates::ParameterKind::Integer) => {
                        if matches!(self.current().kind, TokenKind::Number(_)) {
                            TypeArgument::Integer(self.integer_literal()?)
                        } else {
                            let name = self.name()?;
                            if !name.as_bytes().first().is_some_and(u8::is_ascii_uppercase) {
                                return self.fail(
                                    "expected nonnegative integer literal or const parameter",
                                );
                            }
                            TypeArgument::Const(name)
                        }
                    }
                    None if matches!(self.current().kind, TokenKind::Number(_)) => {
                        TypeArgument::Integer(self.integer_literal()?)
                    }
                    _ => {
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
                });
                index += 1;
                if !self.at(",") {
                    break;
                }
            }
            self.expect(">")?;
            if let Some(template) = template {
                if arguments.len() != template.parameters.len() {
                    return self.fail(template.argument_error);
                }
            }
            if path.len() == 1
                && matches!(
                    path[0].as_str(),
                    "i8" | "i16"
                        | "i32"
                        | "i64"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "f32"
                        | "f64"
                        | "Bool"
                        | "String"
                        | "Char"
                )
            {
                return self.fail("primitive types do not accept generic arguments");
            }
        } else if path == ["Array"] {
            return self.fail("expected Array<element type, length>");
        }
        if path == ["Bytes"] && !arguments.is_empty() {
            self.warn_migration(
                3,
                start,
                "legacy `Bytes<N>` type spelling; write `Array<u8, N>` instead".into(),
            );
        }
        let mut ty = Type {
            span: self.span(start),
            path,
            arguments,
        };
        while self.eat("?") {
            ty = Type {
                span: self.span(start),
                path: vec!["Option".into()],
                arguments: vec![TypeArgument::Type(ty)],
            };
        }
        Ok(ty)
    }
    /// MW003: the legacy `Bytes<N>` spelling. Meaning is unchanged. MW001 and MW002 are unused.
    fn warn_migration(&mut self, number: u16, start: usize, message: String) {
        let mut warning = Diagnostic::new(
            DiagnosticCode::new(Category::Migration, number).unwrap(),
            Severity::Warning,
            message,
        );
        warning.span = Some(self.span(start));
        self.warnings.push(warning);
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
    /// Positional tuple bindings. Nested patterns and discard bindings retain
    /// their tuple position so lowering can consume every slot exactly once.
    fn tuple_bindings(&mut self) -> PResult<Vec<TupleBinding>> {
        self.expect("(")?;
        let mut elements = Vec::new();
        while !self.at(")") && !self.eof() {
            let start = self.current().span.start;
            let (binding, nested) = if self.at("(") {
                (String::new(), Some(self.tuple_bindings()?))
            } else {
                let binding = self.name()?;
                if self.at("(") || self.at("{") || self.at("::") {
                    return self
                        .fail("expected a tuple binding, wildcard, or nested tuple pattern");
                }
                if self.at(":") {
                    return self.fail(
                        "tuple destructuring aliases are not supported yet; use positional bindings",
                    );
                }
                (binding, None)
            };
            elements.push(TupleBinding {
                span: self.span(start),
                binding,
                nested,
            });
            if !self.eat(",") {
                if !self.at(")") {
                    return self.fail("expected `,` or `)` in tuple destructuring pattern");
                }
                if elements.len() == 1 {
                    return self
                        .fail("a one-element tuple destructuring pattern needs a trailing comma");
                }
                break;
            }
        }
        self.expect(")")?;
        Ok(elements)
    }
    fn statement(&mut self) -> PResult<(Option<Statement>, Option<Expr>)> {
        let start = self.current().span.start;
        let kind = if self.at("let") || self.at("var") {
            let mutable = self.eat("var");
            if !mutable {
                self.expect("let")?;
            }
            if self.at("(") {
                let elements = self.tuple_bindings()?;
                self.expect(":=")?;
                let value = self.expr(0)?;
                self.expect(";")?;
                return Ok((
                    Some(Statement {
                        span: self.span(start),
                        kind: StatementKind::TupleDestructure {
                            mutable,
                            elements,
                            value,
                        },
                    }),
                    None,
                ));
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
            if self.at("{") {
                StatementKind::Loop(self.block()?)
            } else {
                let binding = self.name()?;
                self.expect("in")?;
                let items = self.before_block()?;
                StatementKind::ForEach {
                    binding,
                    items,
                    body: self.block()?,
                }
            }
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
            if [
                "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
            ]
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
        let condition = Box::new(self.before_block()?);
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
        let scrutinee = Box::new(self.before_block()?);
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
    fn before_block(&mut self) -> PResult<Expr> {
        let saved = std::mem::replace(&mut self.no_struct, true);
        let result = self.expr(0);
        self.no_struct = saved;
        result
    }

    /// Parse inside delimiters, where a brace can start a struct literal.
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
    fn generic_struct_literal_ahead(&self) -> bool {
        if !matches!(self.current().kind, TokenKind::Word(_)) || !self.next_at("<") {
            return false;
        }
        let mut depth = 0usize;
        for token in self.tokens.iter().skip(self.pos + 1) {
            match &token.kind {
                TokenKind::Symbol(symbol) if symbol == "<" => depth += 1,
                TokenKind::Symbol(symbol) if symbol == ">" => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return self.tokens.iter().find(|next| next.span.start >= token.span.end)
                            .is_some_and(|next| matches!(&next.kind, TokenKind::Symbol(symbol) if symbol == "{"));
                    }
                }
                TokenKind::Eof => return false,
                _ => {}
            }
        }
        false
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
        } else if self.at("{") && self.looks_like_struct_fields() && self.no_struct {
            return self.fail(
                "an anonymous record literal is not allowed directly in an `if` condition, `match` scrutinee, or loop iterable; wrap it in parentheses",
            );
        } else if self.at("{") && self.looks_like_struct_fields() {
            let fields = self.nested(Self::struct_fields)?;
            Node {
                span: self.span(start),
                kind: ExprKind::Struct {
                    path: Vec::new(),
                    type_arguments: Vec::new(),
                    fields,
                },
            }
        } else if self.at("{") || self.at("if") || self.at("match") {
            self.block_like(false)?
        } else if self.eat("(") {
            if self.eat(")") {
                Node {
                    span: self.span(start),
                    kind: ExprKind::Tuple(Vec::new()),
                }
            } else {
                let first_label = if self.tuple_label_ahead() {
                    let name = self.name()?;
                    self.expect(":")?;
                    Some(name)
                } else {
                    None
                };
                let first = self.nested(|p| p.expr(0))?;
                if self.eat(",") {
                    let mut values = vec![TupleElement {
                        span: first.span,
                        label: first_label,
                        value: first,
                    }];
                    while !self.at(")") && !self.eof() {
                        let label = if self.tuple_label_ahead() {
                            let name = self.name()?;
                            self.expect(":")?;
                            Some(name)
                        } else {
                            None
                        };
                        let value = self.expr(0)?;
                        values.push(TupleElement {
                            span: value.span,
                            label,
                            value,
                        });
                        if !self.eat(",") {
                            break;
                        }
                    }
                    self.expect(")")?;
                    Node {
                        span: self.span(start),
                        kind: ExprKind::Tuple(values),
                    }
                } else {
                    if first_label.is_some() {
                        return self.fail("a labeled tuple value needs tuple delimiters");
                    }
                    self.expect(")")?;
                    Node {
                        span: self.span(start),
                        kind: first.kind,
                    }
                }
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
                TokenKind::CharLiteral(value) => {
                    self.bump();
                    ExprKind::CharLiteral(value)
                }
                TokenKind::Word(s) if s == "true" || s == "false" => {
                    self.bump();
                    ExprKind::Bool(s == "true")
                }
                TokenKind::Word(_) => {
                    let (path, type_arguments) = if self.generic_struct_literal_ahead() {
                        let ty = self.ty()?;
                        (ty.path, ty.arguments)
                    } else {
                        (self.path()?, Vec::new())
                    };
                    if self.at("{") && self.no_struct && self.looks_like_struct_fields() {
                        return self.fail(
                            "a struct literal is not allowed directly in an `if` condition, `match` scrutinee, or loop iterable; wrap it in parentheses",
                        );
                    }
                    if self.at("{") && !self.no_struct {
                        let fields = self.nested(Self::struct_fields)?;
                        ExprKind::Struct {
                            path,
                            type_arguments,
                            fields,
                        }
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
            if minimum <= 12 && self.eat("as") {
                let target = self.ty_postfix()?;
                left = Node {
                    span: self.span(start),
                    kind: ExprKind::Cast {
                        value: Box::new(left),
                        target,
                    },
                };
                continue;
            }
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
                        interface: None,
                    },
                };
                continue;
            }
            if minimum <= 15 && self.eat("of") {
                let interface = self.ty()?;
                let ExprKind::Call {
                    interface: selected,
                    ..
                } = &mut left.kind
                else {
                    return self.fail("interface selection applies to a method call");
                };
                if selected.is_some() {
                    return self.fail("a call can select only one interface");
                }
                *selected = Some(interface);
                left.span = self.span(start);
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
            let shift_right = self.at(">")
                && self.tokens.get(self.pos + 1).is_some_and(
                    |token| matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == ">"),
                );
            let shift_left = self.at("<")
                && self.tokens.get(self.pos + 1).is_some_and(
                    |token| matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "<"),
                );
            let (operator, power) = match &self.current().kind {
                TokenKind::Symbol(s) => {
                    let operator = if shift_right {
                        ">>"
                    } else if shift_left {
                        "<<"
                    } else {
                        s.as_str()
                    };
                    let power = match operator {
                        "||" => 1,
                        "&&" => 2,
                        "==" | "!=" => 3,
                        "<" | "<=" | ">" | ">=" => 4,
                        "|" => 5,
                        "^" => 6,
                        "&" => 7,
                        "<<" | ">>" => 8,
                        "+" | "-" => 9,
                        "*" | "/" | "%" => 11,
                        _ => break,
                    };
                    (operator.to_owned(), power)
                }
                _ => break,
            };
            if power < minimum {
                break;
            }
            self.bump();
            if matches!(operator.as_str(), "<<" | ">>") {
                self.bump();
            }
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
