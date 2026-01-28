//! Memobits — Lexer, Parser, AST, AST-walking Interpreter.
//!
//! Bkz. `docs/LANGUAGE_SPEC.md` için teknik spesifikasyon.

pub mod ast;
pub mod environment;
pub mod interpreter;
pub mod lexer;
pub mod native;
pub mod parser;
pub mod syntax_analyzer;
pub mod types;
pub mod value;

pub use ast::{Expr, Program, Stmt};
pub use interpreter::Interpreter;
pub use lexer::{Lexer, Span, Token};
pub use native::NativeRegistry;
pub use parser::Parser;
pub use syntax_analyzer::*;
pub use types::Type;
pub use value::Value;
