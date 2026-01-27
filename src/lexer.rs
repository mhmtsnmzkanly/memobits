//! Lexer: kaynak metni token akışına dönüştürür.

use std::iter::Peekable;
use std::str::Chars;

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    // Keywords
    Let,
    Var,
    Fn,
    Struct,
    Enum,
    Match,
    If,
    Else,
    Loop,
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
    FloatKw,
    BoolKw,
    CharKw,
    StringKw,
    Native,

    // Identifiers & names
    Ident(String),
    /// native::ident
    NativeIdent(String),

    // Literals
    IntLit(i64),
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

    Eof,
}

impl Token {
    pub fn is_eof(&self) -> bool {
        matches!(self, Token::Eof)
    }
}

#[derive(Clone, Debug)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

pub struct Lexer<'a> {
    #[allow(dead_code)]
    src: &'a str,
    chars: Peekable<Chars<'a>>,
    putback: Vec<char>,
    pos: usize,
    tokens: Vec<(Token, Span)>,
    errs: Vec<String>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            chars: src.chars().peekable(),
            putback: Vec::new(),
            pos: 0,
            tokens: Vec::new(),
            errs: Vec::new(),
        }
    }

    fn peek(&mut self) -> Option<char> {
        if let Some(&c) = self.putback.last() {
            return Some(c);
        }
        self.chars.peek().copied()
    }

    fn bump(&mut self) -> Option<char> {
        if let Some(c) = self.putback.pop() {
            return Some(c);
        }
        let c = self.chars.next()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn putback(&mut self, c: char) {
        self.putback.push(c);
        self.pos = self.pos.saturating_sub(c.len_utf8());
    }

    fn bump_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        while self.peek().map_or(false, &mut pred) {
            self.bump();
        }
    }

    fn start_pos(&self) -> usize {
        self.pos
    }

    fn span(&self, lo: usize, hi: usize) -> Span {
        Span { lo, hi }
    }

    fn push(&mut self, t: Token, lo: usize, hi: usize) {
        self.tokens.push((t, self.span(lo, hi)));
    }

    fn error(&mut self, msg: String) {
        self.errs.push(msg);
    }

    fn skip_line_comment(&mut self) {
        self.bump_while(|c| c != '\n');
    }

    fn read_ident_or_keyword(&mut self) -> (String, usize, usize) {
        let lo = self.start_pos();
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == '_' {
                s.push(c);
                self.bump();
            } else {
                break;
            }
        }
        let hi = self.start_pos();
        (s, lo, hi)
    }

    fn keyword_or_ident(&mut self, s: &str, _lo: usize, _hi: usize) -> Token {
        match s {
            "let" => Token::Let,
            "var" => Token::Var,
            "fn" => Token::Fn,
            "struct" => Token::Struct,
            "enum" => Token::Enum,
            "match" => Token::Match,
            "if" => Token::If,
            "else" => Token::Else,
            "loop" => Token::Loop,
            "break" => Token::Break,
            "continue" => Token::Continue,
            "true" => Token::True,
            "false" => Token::False,
            "Option" => Token::Option,
            "Result" => Token::Result,
            "Ok" => Token::Ok,
            "Err" => Token::Err,
            "Some" => Token::Some,
            "None" => Token::None,
            "Array" => Token::Array,
            "List" => Token::List,
            "Map" => Token::Map,
            "Int" => Token::IntKw,
            "Float" => Token::FloatKw,
            "Bool" => Token::BoolKw,
            "Char" => Token::CharKw,
            "String" => Token::StringKw,
            "native" => Token::Native,
            _ => Token::Ident(s.to_string()),
        }
    }

    fn read_number(&mut self) -> Result<(Token, usize, usize), ()> {
        let lo = self.start_pos();
        let mut s = String::new();
        let mut is_float = false;

        if self.peek() == Some('-') {
            s.push(self.bump().unwrap());
        }

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(self.bump().unwrap());
            } else if c == '.' {
                if is_float {
                    self.error("invalid float".into());
                    return Err(());
                }
                is_float = true;
                s.push(self.bump().unwrap());
            } else if c == 'e' || c == 'E' {
                is_float = true;
                s.push(self.bump().unwrap());
                if self.peek() == Some('+') || self.peek() == Some('-') {
                    s.push(self.bump().unwrap());
                }
                while self.peek().map_or(false, |c| c.is_ascii_digit()) {
                    s.push(self.bump().unwrap());
                }
                break;
            } else {
                break;
            }
        }

        let hi = self.start_pos();
        let tok = if is_float {
            let f: f64 = s.parse().map_err(|_| {
                self.error(format!("invalid float literal: {}", s));
            })?;
            Token::FloatLit(f)
        } else {
            let i: i64 = s.parse().map_err(|_| {
                self.error(format!("invalid int literal: {}", s));
            })?;
            Token::IntLit(i)
        };
        Ok((tok, lo, hi))
    }

    fn read_char(&mut self) -> Result<(Token, usize, usize), ()> {
        let lo = self.start_pos();
        self.bump(); // '
        let c = self.bump().ok_or_else(|| {
            self.error("unexpected eof in char".into());
        })?;
        let ch = if c == '\\' {
            let esc = self.bump().ok_or_else(|| {
                self.error("unexpected eof after \\ in char".into());
            })?;
            match esc {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '0' => '\0',
                '\'' => '\'',
                '\\' => '\\',
                _ => {
                    self.error(format!("unknown escape \\{}", esc));
                    return Err(());
                }
            }
        } else {
            c
        };
        if self.bump() != Some('\'') {
            self.error("char literal must end with '".into());
            return Err(());
        }
        let hi = self.start_pos();
        Ok((Token::CharLit(ch), lo, hi))
    }

    fn read_double_quoted_string(&mut self) -> Result<(Token, usize, usize), ()> {
        let lo = self.start_pos();
        self.bump(); // "
        let mut s = String::new();
        loop {
            match self.bump() {
                None => {
                    self.error("unclosed \" string".into());
                    return Err(());
                }
                Some('"') => break,
                Some('\\') => {
                    let e = self.bump().ok_or_else(|| {
                        self.error("unexpected eof after \\ in string".into());
                    })?;
                    match e {
                        'n' => s.push('\n'),
                        'r' => s.push('\r'),
                        't' => s.push('\t'),
                        '0' => s.push('\0'),
                        '"' => s.push('"'),
                        '\\' => s.push('\\'),
                        _ => {
                            self.error(format!("unknown escape \\{}", e));
                            return Err(());
                        }
                    }
                }
                Some(c) => s.push(c),
            }
        }
        let hi = self.start_pos();
        Ok((Token::StringLit(s), lo, hi))
    }

    /// Lex template `...` string. Emits TemplatePart, TemplateInterp, then TemplateEnd.
    fn read_template_string(&mut self) -> Result<(), ()> {
        self.bump(); // `
        let mut lit = String::new();

        loop {
            match self.peek() {
                None => {
                    self.error("unclosed ` template string".into());
                    return Err(());
                }
                Some('`') => {
                    if !lit.is_empty() {
                        let part = std::mem::take(&mut lit);
                        let hi = self.start_pos();
                        let lo = hi.saturating_sub(part.len());
                        self.push(Token::TemplatePart(part), lo, hi);
                    }
                    let end_lo = self.start_pos();
                    self.bump();
                    self.push(Token::TemplateEnd, end_lo, self.start_pos());
                    return Ok(());
                }
                Some('\\') => {
                    self.bump();
                    let e = self.bump().ok_or_else(|| {
                        self.error("unexpected eof after \\ in template".into());
                    })?;
                    match e {
                        'n' => lit.push('\n'),
                        'r' => lit.push('\r'),
                        't' => lit.push('\t'),
                        '0' => lit.push('\0'),
                        '`' => lit.push('`'),
                        '\\' => lit.push('\\'),
                        '{' => lit.push('{'),
                        _ => {
                            self.error(format!("unknown escape \\{}", e));
                            return Err(());
                        }
                    }
                }
                Some('{') => {
                    if !lit.is_empty() {
                        let part = std::mem::take(&mut lit);
                        let hi = self.start_pos();
                        let lo = hi.saturating_sub(part.len());
                        self.push(Token::TemplatePart(part), lo, hi);
                    }
                    let interp_lo = self.start_pos();
                    self.bump(); // {
                    self.bump_while(|c| c == ' ' || c == '\t');
                    let (id, _, _) = self.read_ident_or_keyword();
                    if id.is_empty() {
                        self.error("expected identifier in template interpolation".into());
                        return Err(());
                    }
                    self.bump_while(|c| c == ' ' || c == '\t');
                    if self.bump() != Some('}') {
                        self.error("expected } to close template interpolation".into());
                        return Err(());
                    }
                    self.push(Token::TemplateInterp(id), interp_lo, self.start_pos());
                }
                Some(c) => {
                    lit.push(c);
                    self.bump();
                }
            }
        }
    }

    pub fn lex(mut self) -> Result<Vec<(Token, Span)>, Vec<String>> {
        while self.peek().is_some() {
            self.bump_while(|c| c.is_ascii_whitespace());

            let lo = self.start_pos();
            let Some(c) = self.bump() else { break };

            if c == '/' && self.peek() == Some('/') {
                self.bump();
                self.skip_line_comment();
                continue;
            }

            let (tok, hi) = if c.is_ascii_alphabetic() || c == '_' {
                let mut s = String::from(c);
                while let Some(n) = self.peek() {
                    if n.is_ascii_alphanumeric() || n == '_' {
                        s.push(self.bump().unwrap());
                    } else {
                        break;
                    }
                }
                let hi = self.start_pos();
                if s == "native" && self.peek() == Some(':') {
                    self.bump();
                    if self.peek() != Some(':') {
                        self.error("expected :: after native".into());
                        (Token::Ident(s), hi)
                    } else {
                        self.bump();
                        let (id, _, hi2) = self.read_ident_or_keyword();
                        (Token::NativeIdent(id), hi2)
                    }
                } else {
                    (self.keyword_or_ident(&s, lo, hi), hi)
                }
            } else if c.is_ascii_digit() {
                self.putback(c);
                match self.read_number() {
                    Ok((t, _, hi)) => (t, hi),
                    Err(()) => continue,
                }
            } else {
                let hi = self.start_pos();
                match c {
                    '+' => (Token::Plus, hi),
                    '-' => {
                        if self.peek().map_or(false, |x| x.is_ascii_digit()) {
                            self.putback('-');
                            match self.read_number() {
                                Ok((t, _, hi2)) => (t, hi2),
                                Err(()) => continue,
                            }
                        } else if self.peek() == Some('>') {
                            self.bump();
                            (Token::Arrow, self.start_pos())
                        } else {
                            (Token::Minus, hi)
                        }
                    }
                    '*' => (Token::Star, hi),
                    '/' => (Token::Slash, hi),
                    '%' => (Token::Percent, hi),
                    '=' => {
                        if self.peek() == Some('=') {
                            self.bump();
                            (Token::EqEq, self.start_pos())
                        } else if self.peek() == Some('>') {
                            self.bump();
                            (Token::FatArrow, self.start_pos())
                        } else {
                            (Token::Eq, hi)
                        }
                    }
                    '!' => {
                        if self.peek() == Some('=') {
                            self.bump();
                            (Token::Ne, self.start_pos())
                        } else {
                            (Token::Not, hi)
                        }
                    }
                    '<' => {
                        if self.peek() == Some('=') {
                            self.bump();
                            (Token::Le, self.start_pos())
                        } else {
                            (Token::Lt, hi)
                        }
                    }
                    '>' => {
                        if self.peek() == Some('=') {
                            self.bump();
                            (Token::Ge, self.start_pos())
                        } else {
                            (Token::Gt, hi)
                        }
                    }
                    '&' => {
                        if self.peek() == Some('&') {
                            self.bump();
                            (Token::And, self.start_pos())
                        } else {
                            self.error("expected &&".into());
                            continue;
                        }
                    }
                    '|' => {
                        if self.peek() == Some('|') {
                            self.bump();
                            (Token::Or, self.start_pos())
                        } else {
                            self.error("expected ||".into());
                            continue;
                        }
                    }
                    '(' => (Token::LParen, hi),
                    ')' => (Token::RParen, hi),
                    '{' => (Token::LBrace, hi),
                    '}' => (Token::RBrace, hi),
                    '[' => (Token::LBracket, hi),
                    ']' => (Token::RBracket, hi),
                    ',' => (Token::Comma, hi),
                    ':' => {
                        if self.peek() == Some(':') {
                            self.bump();
                            (Token::ColonColon, self.start_pos())
                        } else {
                            (Token::Colon, hi)
                        }
                    }
                    ';' => (Token::Semi, hi),
                    '.' => (Token::Dot, hi),
                    '"' => {
                        self.putback('"');
                        match self.read_double_quoted_string() {
                            Ok((t, _, hi2)) => (t, hi2),
                            Err(()) => continue,
                        }
                    }
                    '\'' => {
                        self.putback('\'');
                        match self.read_char() {
                            Ok((t, _, hi2)) => (t, hi2),
                            Err(()) => continue,
                        }
                    }
                    '`' => {
                        self.putback('`');
                        if let Err(()) = self.read_template_string() {
                            continue;
                        }
                        continue; // read_template_string already pushed tokens
                    }
                    _ => {
                        self.error(format!("unexpected character: {:?}", c));
                        continue;
                    }
                }
            };

            self.push(tok, lo, hi);
        }

        self.tokens.push((Token::Eof, self.span(self.start_pos(), self.start_pos())));

        if !self.errs.is_empty() {
            return Err(self.errs);
        }
        Ok(self.tokens)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_ints() {
        let l = Lexer::new("0 42 -7");
        let r = l.lex().unwrap();
        let toks: Vec<_> = r.iter().map(|(t, _)| t).collect();
        assert!(matches!(toks[0], Token::IntLit(0)));
        assert!(matches!(toks[1], Token::IntLit(42)));
        assert!(matches!(toks[2], Token::IntLit(-7)));
    }
}
