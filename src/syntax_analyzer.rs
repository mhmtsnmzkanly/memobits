use crate::ast::*;
//use crate::types::Type;
use logos::*;

#[derive(Default, Clone)]
pub struct Helper {
    line: usize,
    column: usize,
}

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(extras = Helper)]
pub enum Token {
    // ===== Keywords =====
    #[token("let")]
    Let,
    #[token("var")]
    Var,
    #[token("fn")]
    Fn,
    #[token("return")]
    Return,
    #[token("struct")]
    Struct,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("loop")]
    Loop,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,

    #[token("true")]
    True,
    #[token("false")]
    False,

    #[token("Int")]
    IntKw,
    #[token("Float")]
    FloatKw,
    #[token("Bool")]
    BoolKw,
    #[token("Char")]
    CharKw,
    #[token("String")]
    StringKw,

    // ===== Operators (ORDER MATTERS) =====
    #[token("==")]
    EqEq,
    #[token("!=")]
    NotEq,
    #[token("<=")]
    LtEq,
    #[token(">=")]
    GtEq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,

    #[token("=>")]
    FatArrow,
    #[token("->")]
    Arrow,

    #[token("=")]
    Assign,

    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,

    // ===== Delimiters =====
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

    // ===== Literals =====
    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().parse::<f64>().ok())]
    FloatLit(f64),

    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    IntLit(i64),

    #[regex(r"'([^'\\]|\\.)'", |lex| {
    lex.slice().chars().nth(1)
    })]
    CharLit(char),

    #[regex(r"`([^`\\]|\\.)*`", |lex| {
    let s = lex.slice();
    Some(s[1..s.len() - 1].to_string())
    })]
    #[regex(r#""([^"\\\x00-\x1F]|\\(["\\bnfrt/]|u[a-fA-F0-9]{4}))*""#, |lex| {
    let s = lex.slice();
    Some(s[1..s.len() - 1].to_string())
    })]
    StringLit(String),

    // ===== Identifier =====
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| {
    Some(lex.slice().to_string())
    })]
    Ident(String),

    // ===== Skip =====
    #[regex(r"[ \t\r\n]+", logos::skip)]
    #[regex(r"//[^\n\r]*", logos::skip, allow_greedy = true)]
    // ===== Error =====
    Error,
}

impl Token {
    // ===== Keywords =====
    pub fn is_let(&self) -> bool {
        matches!(self, Token::Let)
    }
    pub fn is_var(&self) -> bool {
        matches!(self, Token::Var)
    }
    pub fn is_fn(&self) -> bool {
        matches!(self, Token::Fn)
    }
    pub fn is_return(&self) -> bool {
        matches!(self, Token::Return)
    }
    pub fn is_struct(&self) -> bool {
        matches!(self, Token::Struct)
    }
    pub fn is_if(&self) -> bool {
        matches!(self, Token::If)
    }
    pub fn is_else(&self) -> bool {
        matches!(self, Token::Else)
    }
    pub fn is_loop(&self) -> bool {
        matches!(self, Token::Loop)
    }
    pub fn is_break(&self) -> bool {
        matches!(self, Token::Break)
    }
    pub fn is_continue(&self) -> bool {
        matches!(self, Token::Continue)
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Token::True)
    }
    pub fn is_false(&self) -> bool {
        matches!(self, Token::False)
    }

    pub fn is_int_kw(&self) -> bool {
        matches!(self, Token::IntKw)
    }
    pub fn is_float_kw(&self) -> bool {
        matches!(self, Token::FloatKw)
    }
    pub fn is_bool_kw(&self) -> bool {
        matches!(self, Token::BoolKw)
    }
    pub fn is_char_kw(&self) -> bool {
        matches!(self, Token::CharKw)
    }
    pub fn is_string_kw(&self) -> bool {
        matches!(self, Token::StringKw)
    }

    // ===== Operators =====
    pub fn is_eq_eq(&self) -> bool {
        matches!(self, Token::EqEq)
    }
    pub fn is_not_eq(&self) -> bool {
        matches!(self, Token::NotEq)
    }
    pub fn is_lt_eq(&self) -> bool {
        matches!(self, Token::LtEq)
    }
    pub fn is_gt_eq(&self) -> bool {
        matches!(self, Token::GtEq)
    }
    pub fn is_lt(&self) -> bool {
        matches!(self, Token::Lt)
    }
    pub fn is_gt(&self) -> bool {
        matches!(self, Token::Gt)
    }

    pub fn is_fat_arrow(&self) -> bool {
        matches!(self, Token::FatArrow)
    }
    pub fn is_arrow(&self) -> bool {
        matches!(self, Token::Arrow)
    }

    pub fn is_assign(&self) -> bool {
        matches!(self, Token::Assign)
    }

    pub fn is_plus(&self) -> bool {
        matches!(self, Token::Plus)
    }
    pub fn is_minus(&self) -> bool {
        matches!(self, Token::Minus)
    }
    pub fn is_star(&self) -> bool {
        matches!(self, Token::Star)
    }
    pub fn is_slash(&self) -> bool {
        matches!(self, Token::Slash)
    }

    // ===== Delimiters =====
    pub fn is_lparen(&self) -> bool {
        matches!(self, Token::LParen)
    }
    pub fn is_rparen(&self) -> bool {
        matches!(self, Token::RParen)
    }
    pub fn is_lbrace(&self) -> bool {
        matches!(self, Token::LBrace)
    }
    pub fn is_rbrace(&self) -> bool {
        matches!(self, Token::RBrace)
    }
    pub fn is_lbracket(&self) -> bool {
        matches!(self, Token::LBracket)
    }
    pub fn is_rbracket(&self) -> bool {
        matches!(self, Token::RBracket)
    }
    pub fn is_comma(&self) -> bool {
        matches!(self, Token::Comma)
    }
    pub fn is_colon(&self) -> bool {
        matches!(self, Token::Colon)
    }
    pub fn is_semi(&self) -> bool {
        matches!(self, Token::Semi)
    }
    pub fn is_dot(&self) -> bool {
        matches!(self, Token::Dot)
    }

    // ===== Literals =====
    pub fn is_int_lit(&self) -> bool {
        matches!(self, Token::IntLit(_))
    }
    pub fn is_float_lit(&self) -> bool {
        matches!(self, Token::FloatLit(_))
    }
    pub fn is_char_lit(&self) -> bool {
        matches!(self, Token::CharLit(_))
    }
    pub fn is_string_lit(&self) -> bool {
        matches!(self, Token::StringLit(_))
    }

    // ===== Identifier =====
    pub fn is_ident(&self) -> bool {
        matches!(self, Token::Ident(_))
    }

    // ===== Error =====
    pub fn is_error(&self) -> bool {
        matches!(self, Token::Error)
    }

    // ==== Update position ====
    pub fn update_position(lex: &mut logos::Lexer<Token>) {
        let slice = lex.slice();

        for ch in slice.chars() {
            if ch == '\n' {
                lex.extras.line += 1;
                lex.extras.column = 0;
            } else {
                lex.extras.column += 1;
            }
        }
    }
}

#[derive(Debug)]
pub struct SpannedToken {
    pub token: Token,
    pub span: (usize, usize),
}

#[derive(Debug, Clone)]
pub struct SyntaxError {
    pub pos: (usize, usize), // Error row-column
    pub detail: String,      // Error info
}

impl SyntaxError {
    pub fn new(pos: (usize, usize), detail: String) -> Self {
        Self { pos, detail }
    }
}

impl std::fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Error on ({}:{}): {}",
            self.pos.0, self.pos.1, self.detail
        )
    }
}
#[derive(Debug)]
pub struct SyntaxAnalyzer {
    tokens: Vec<SpannedToken>,
    errors: Vec<SyntaxError>, // Errors from lexer or parser
    cursor: usize,            // Position of cursor (max value is lenght of tokens)
}

impl SyntaxAnalyzer {
    pub fn new(source: &str) -> Self {
        let mut tokens: Vec<SpannedToken> = Vec::new();
        let mut errors: Vec<SyntaxError> = Vec::new();

        let mut lexer = Token::lexer(source);

        while let Some(result) = lexer.next() {
            let span = lexer.span();
            let range = (span.start, span.end);

            match result {
                Err(_) | Ok(Token::Error) => {
                    errors.push(SyntaxError::new(
                        range,
                        format!("Lexical error: `{}`", lexer.slice()),
                    ));
                }
                Ok(token) => {
                    tokens.push(SpannedToken { token, span: range });
                }
            }
        }

        Self {
            tokens,
            errors,
            cursor: 0,
        }
    }
    pub fn analyz(&mut self) -> Result<Program, Vec<SyntaxError>> {
        // AST Items for Interpreter
        let mut items: Vec<Item> = Vec::new();

        // AST Items from Tokens
        for token in &self.tokens {}

        if !self.errors.is_empty() {
            return Err(self.errors.clone());
        }

        Ok(Program { items })
    }
}
