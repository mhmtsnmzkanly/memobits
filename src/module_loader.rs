//! Basit modül yükleyici: `mod foo;` -> foo.mb (göreli).

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use crate::ast::{Expr, ExprKind, Item, Literal, MatchArm, ModuleDecl, Program, Stmt, StmtKind};
use crate::syntax_analyzer::SyntaxAnalyzer;

#[derive(Debug, Clone)]
pub struct ModuleError(pub String);

impl std::fmt::Display for ModuleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for ModuleError {}

pub struct LoadedProgram {
    pub program: Program,
    pub source: String,
}

pub fn load_with_modules(entry_source: &str, entry_path: Option<&Path>) -> Result<LoadedProgram, ModuleError> {
    let base_dir = match entry_path {
        Some(p) => p.parent().unwrap_or_else(|| Path::new(".")),
        None => Path::new("."),
    };

    let mut sa = SyntaxAnalyzer::new(entry_source);
    let entry_program = sa.analyz().map_err(|errs| {
        let msg = errs
            .into_iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        ModuleError(format!("syntax hatası:\n{}", msg))
    })?;

    let (entry_mods, mut entry_program) = split_module_decls(entry_program);

    let mut loader = ModuleLoader::new();
    for m in entry_mods {
        let path = resolve_module_path(base_dir, &m)?;
        loader.load_module_recursive(&path)?;
    }

    let mut source = String::new();
    let mut items = Vec::new();

    for module in &mut loader.modules {
        let header = module_header(&module.path);
        let offset = source.len() + header.len();
        source.push_str(&header);
        source.push_str(&module.source);
        source.push('\n');
        shift_program(&mut module.program, offset);
        items.extend(module.program.items.drain(..));
    }

    let entry_header = module_header(entry_path.unwrap_or_else(|| Path::new("<repl>")));
    let entry_offset = source.len() + entry_header.len();
    source.push_str(&entry_header);
    source.push_str(entry_source);
    source.push('\n');
    shift_program(&mut entry_program, entry_offset);
    items.extend(entry_program.items.drain(..));

    Ok(LoadedProgram {
        program: Program { items },
        source,
    })
}

struct ModuleLoader {
    visited: HashSet<PathBuf>,
    stack: Vec<PathBuf>,
    modules: Vec<LoadedModule>,
}

struct LoadedModule {
    path: PathBuf,
    source: String,
    program: Program,
}

impl ModuleLoader {
    fn new() -> Self {
        Self {
            visited: HashSet::new(),
            stack: Vec::new(),
            modules: Vec::new(),
        }
    }

    fn load_module_recursive(&mut self, path: &Path) -> Result<(), ModuleError> {
        let canonical = fs::canonicalize(path)
            .map_err(|e| ModuleError(format!("modül bulunamadı: {} ({})", path.display(), e)))?;

        if self.stack.contains(&canonical) {
            return Err(ModuleError(format!(
                "modül döngüsü tespit edildi: {}",
                canonical.display()
            )));
        }
        if self.visited.contains(&canonical) {
            return Ok(());
        }

        let source = fs::read_to_string(&canonical)
            .map_err(|e| ModuleError(format!("modül okunamadı: {} ({})", canonical.display(), e)))?;

        let mut sa = SyntaxAnalyzer::new(&source);
        let program = sa.analyz().map_err(|errs| {
            let msg = errs
                .into_iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            ModuleError(format!("modül syntax hatası ({}):\n{}", canonical.display(), msg))
        })?;

        let (mods, program) = split_module_decls(program);
        self.stack.push(canonical.clone());
        let base_dir = canonical.parent().unwrap_or_else(|| Path::new("."));
        for m in mods {
            let path = resolve_module_path(base_dir, &m)?;
            self.load_module_recursive(&path)?;
        }
        self.stack.pop();
        self.visited.insert(canonical.clone());

        self.modules.push(LoadedModule {
            path: canonical,
            source,
            program,
        });
        Ok(())
    }
}

fn resolve_module_path(base_dir: &Path, decl: &ModuleDecl) -> Result<PathBuf, ModuleError> {
    if let Some(path) = &decl.path {
        let p = Path::new(path);
        if p.is_absolute() {
            return Ok(p.to_path_buf());
        }
        if has_parent_dir(p) {
            return Err(ModuleError(
                "göreli modül yolu parent (..) içeremez".into(),
            ));
        }
        return Ok(base_dir.join(p));
    }

    if decl.name.contains('/') || decl.name.contains('\\') {
        return Err(ModuleError("modül adı yalnızca bir identifier olmalıdır".into()));
    }
    let filename = format!("{}.mb", decl.name);
    Ok(base_dir.join(filename))
}

fn has_parent_dir(path: &Path) -> bool {
    path.components()
        .any(|c| matches!(c, std::path::Component::ParentDir))
}

fn module_header(path: &Path) -> String {
    format!("// ---- module: {} ----\n", path.display())
}

fn split_module_decls(program: Program) -> (Vec<ModuleDecl>, Program) {
    let mut mods = Vec::new();
    let mut items = Vec::new();
    for item in program.items {
        match item {
            Item::ModuleDecl(decl) => mods.push(decl),
            other => items.push(other),
        }
    }
    (mods, Program { items })
}

fn shift_program(program: &mut Program, offset: usize) {
    for item in &mut program.items {
        shift_item(item, offset);
    }
}

fn shift_item(item: &mut Item, offset: usize) {
    match item {
        Item::StructDef(_) | Item::EnumDef(_) | Item::ModuleDecl(_) | Item::TypeAlias(_) => {}
        Item::FnDef(def) => {
            for s in &mut def.body {
                shift_stmt(s, offset);
            }
        }
        Item::GlobalLet(b) => shift_expr(&mut b.init, offset),
        Item::GlobalVar(b) => shift_expr(&mut b.init, offset),
        Item::TopLevelStmt(s) => shift_stmt(s, offset),
    }
}

fn shift_stmt(stmt: &mut Stmt, offset: usize) {
    shift_span(&mut stmt.span, offset);
    match &mut stmt.node {
        StmtKind::Let(b) => shift_expr(&mut b.init, offset),
        StmtKind::Var(b) => shift_expr(&mut b.init, offset),
        StmtKind::Assign { value, .. } => shift_expr(value, offset),
        StmtKind::AssignIndex { base, index, value } => {
            shift_expr(base, offset);
            shift_expr(index, offset);
            shift_expr(value, offset);
        }
        StmtKind::Expr(e) => shift_expr(e, offset),
        StmtKind::If { cond, then_b, else_b } => {
            shift_expr(cond, offset);
            for s in then_b {
                shift_stmt(s, offset);
            }
            if let Some(eb) = else_b {
                for s in eb {
                    shift_stmt(s, offset);
                }
            }
        }
        StmtKind::Loop(body) => {
            for s in body {
                shift_stmt(s, offset);
            }
        }
        StmtKind::Match { scrutinee, arms } => {
            shift_expr(scrutinee, offset);
            for arm in arms {
                shift_match_arm(arm, offset);
            }
        }
        StmtKind::Return(expr) => {
            if let Some(e) = expr {
                shift_expr(e, offset);
            }
        }
        StmtKind::Break | StmtKind::Continue => {}
    }
}

fn shift_match_arm(arm: &mut MatchArm, offset: usize) {
    for s in &mut arm.body {
        shift_stmt(s, offset);
    }
    // Pattern'lerin span'i yok.
}

fn shift_expr(expr: &mut Expr, offset: usize) {
    shift_span(&mut expr.span, offset);
    match &mut expr.node {
        ExprKind::Literal(l) => shift_literal(l, offset),
        ExprKind::Ident(_) => {}
        ExprKind::NativeCall(_, args) => {
            for a in args {
                shift_expr(a, offset);
            }
        }
        ExprKind::Binary { left, right, .. } => {
            shift_expr(left, offset);
            shift_expr(right, offset);
        }
        ExprKind::Unary { inner, .. } => shift_expr(inner, offset),
        ExprKind::Call { callee, args } => {
            shift_expr(callee, offset);
            for a in args {
                shift_expr(a, offset);
            }
        }
        ExprKind::Block(stmts) => {
            for s in stmts {
                shift_stmt(s, offset);
            }
        }
        ExprKind::If { cond, then_b, else_b } => {
            shift_expr(cond, offset);
            for s in then_b {
                shift_stmt(s, offset);
            }
            if let Some(eb) = else_b {
                for s in eb {
                    shift_stmt(s, offset);
                }
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            shift_expr(scrutinee, offset);
            for arm in arms {
                shift_match_arm(arm, offset);
            }
        }
        ExprKind::Lambda { body, .. } => shift_expr(body, offset),
        ExprKind::StructLiteral { fields, .. } => {
            for (_, v) in fields {
                shift_expr(v, offset);
            }
        }
        ExprKind::VariantLiteral { data, .. } => {
            if let Some(d) = data {
                shift_expr(d, offset);
            }
        }
        ExprKind::FieldAccess { base, .. } => shift_expr(base, offset),
        ExprKind::Index { base, index } => {
            shift_expr(base, offset);
            shift_expr(index, offset);
        }
        ExprKind::ListLiteral(elems) | ExprKind::ArrayLiteral(elems) => {
            for e in elems {
                shift_expr(e, offset);
            }
        }
        ExprKind::MapLiteral(pairs) => {
            for (k, v) in pairs {
                shift_expr(k, offset);
                shift_expr(v, offset);
            }
        }
        ExprKind::TupleLiteral(elems) => {
            for e in elems {
                shift_expr(e, offset);
            }
        }
        ExprKind::Template { .. } => {}
    }
}

fn shift_literal(lit: &mut Literal, offset: usize) {
    match lit {
        Literal::Some(e) | Literal::Ok(e) | Literal::Err(e) => shift_expr(e, offset),
        _ => {}
    }
}

fn shift_span(span: &mut crate::ast::Span, offset: usize) {
    span.lo = span.lo.saturating_add(offset);
    span.hi = span.hi.saturating_add(offset);
}
