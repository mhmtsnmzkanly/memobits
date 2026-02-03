//! Memobits — SyntaxAnalyzer (lexer+parser), AST, AST-walking Interpreter.
//!
//! Bkz. `docs/LANGUAGE_SPEC.md` için teknik spesifikasyon.

pub mod ast;
pub mod environment;
pub mod interpreter;
pub mod native;
pub mod syntax_analyzer;
pub mod type_checker;
pub mod types;
pub mod value;

pub use ast::{Expr, Program, Stmt};
pub use interpreter::Interpreter;
pub use native::NativeRegistry;
pub use syntax_analyzer::*;
pub use type_checker::TypeChecker;
pub use types::Type;
pub use value::Value;
