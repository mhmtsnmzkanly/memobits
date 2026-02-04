#![cfg_attr(not(feature = "std"), no_std)]
//! Memobits — SyntaxAnalyzer (lexer+parser), AST, AST-walking Interpreter.
//!
//! Bkz. `DOCS.md` için teknik spesifikasyon.

extern crate alloc;

pub mod ast;
pub mod collections;
pub mod environment;
pub mod interpreter;
pub mod native;
pub mod optimizer;
pub mod primitive;
#[cfg(feature = "std")]
pub mod module_loader;
#[cfg(feature = "std")]
pub mod syntax_analyzer;
pub mod type_checker;
pub mod types;
pub mod value;

pub use ast::{Expr, Program, Stmt};
pub use interpreter::Interpreter;
#[cfg(feature = "std")]
pub use module_loader::{load_with_modules, LoadedProgram, ModuleError};
pub use native::NativeRegistry;
#[cfg(feature = "std")]
pub use syntax_analyzer::*;
pub use type_checker::TypeChecker;
pub use types::Type;
pub use value::Value;
