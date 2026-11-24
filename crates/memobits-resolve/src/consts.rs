//! Module-level `const NAME: T = expr;` items.
//!
//! A const is evaluated once at compile time and its value is inlined at every
//! use, so no runtime storage exists and later passes never see the item.
//! Initializers may use literals, other constants (any module, any order) and
//! the built-in operators that statically known expressions already support,
//! with the same checked semantics (`LE001` overflow, `LE002` division by
//! zero, `LE003` shift count). This pass runs after names and imports have
//! been validated, over every loaded module.
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_syntax::numeric::{self, IntKind};
use memobits_syntax::{
    Block, Expr, ExprKind, InterfaceMethod, InterpolationPart, ItemKind, Module, Pattern,
    PatternKind, StatementKind, TupleBinding, Type, TypeArgument, TypeDefinition,
};
use std::collections::{BTreeSet, HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    Char,
    Str,
}

impl CTy {
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "f32" => Self::F32,
            "f64" => Self::F64,
            "bool" => Self::Bool,
            "char" => Self::Char,
            "string" => Self::Str,
            _ => return None,
        })
    }
    fn name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::F32 => "f32",
            Self::F64 => "f64",
            Self::Bool => "bool",
            Self::Char => "char",
            Self::Str => "string",
        }
    }
    fn is_int(self) -> bool {
        self.range().is_some()
    }
    fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
    fn is_numeric(self) -> bool {
        self.is_int() || self.is_float()
    }
    fn is_signed(self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }
    fn range(self) -> Option<(i128, i128)> {
        Some(match self {
            Self::I8 => (i8::MIN as i128, i8::MAX as i128),
            Self::I16 => (i16::MIN as i128, i16::MAX as i128),
            Self::I32 => (i32::MIN as i128, i32::MAX as i128),
            Self::I64 => (i64::MIN as i128, i64::MAX as i128),
            Self::U8 => (0, u8::MAX as i128),
            Self::U16 => (0, u16::MAX as i128),
            Self::U32 => (0, u32::MAX as i128),
            Self::U64 => (0, u64::MAX as i128),
            _ => return None,
        })
    }
    fn int_kind(self) -> Option<IntKind> {
        IntKind::from_name(self.name())
    }
    fn bits(self) -> u32 {
        match self {
            Self::I8 | Self::U8 => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 => 32,
            _ => 64,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum CVal {
    Int(i128),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
}

type Const = (CTy, CVal);
type Key = (String, String);

struct Decl {
    ty: Type,
    value: Expr,
    span: Span,
}

enum Lookup {
    NotConst,
    Failed,
    Value(Const),
}

fn error(category: Category, number: u16, span: Span, message: impl Into<String>) -> Diagnostic {
    let mut d = Diagnostic::new(
        DiagnosticCode::new(category, number).expect("static code"),
        Severity::Error,
        message,
    );
    d.span = Some(span);
    d
}

struct Folder<'a> {
    split: &'a dyn Fn(&str) -> Option<(String, String)>,
    decls: HashMap<Key, Decl>,
    /// Per module: value names that resolve to a constant.
    bindings: HashMap<String, HashMap<String, Key>>,
    /// Per module: global names that are not constants (for the "not a
    /// constant" hint). Unknown names were already reported by the name pass.
    known: HashMap<String, HashSet<String>>,
    values: HashMap<Key, Option<Const>>,
    stack: Vec<Key>,
    cycles_reported: HashSet<Key>,
    diagnostics: Vec<Diagnostic>,
}

/// Evaluate every const of the given modules, inline its uses and remove the
/// const items (and the imports that named them). `split` maps a
/// `module::name` path to its module and member; `prelude` lists project
/// prelude aliases.
pub(crate) fn fold(
    modules: &mut [(String, &mut Module)],
    split: &dyn Fn(&str) -> Option<(String, String)>,
    prelude: &BTreeSet<String>,
) -> Vec<Diagnostic> {
    let mut folder = Folder {
        split,
        decls: HashMap::new(),
        bindings: HashMap::new(),
        known: HashMap::new(),
        values: HashMap::new(),
        stack: Vec::new(),
        cycles_reported: HashSet::new(),
        diagnostics: Vec::new(),
    };
    let mut any_const = false;
    for (module, syntax) in modules.iter() {
        for item in &syntax.items {
            if let ItemKind::Const {
                name, ty, value, ..
            } = &item.kind
            {
                any_const = true;
                folder.decls.insert(
                    (module.clone(), name.clone()),
                    Decl {
                        ty: ty.clone(),
                        value: value.clone(),
                        span: item.span,
                    },
                );
            }
        }
    }
    // Programs without consts and without a repeat count that names a const
    // are untouched: nothing below runs for them.
    if !any_const && !modules.iter().any(|(_, m)| module_names_repeat_count(m)) {
        return Vec::new();
    }
    for (module, syntax) in modules.iter() {
        let mut bindings = HashMap::new();
        let mut known: HashSet<String> = prelude.iter().cloned().collect();
        for item in &syntax.items {
            match &item.kind {
                ItemKind::Const { name, .. } => {
                    bindings.insert(name.clone(), (module.clone(), name.clone()));
                }
                ItemKind::Function { name, .. }
                | ItemKind::Type { name, .. }
                | ItemKind::Interface { name, .. } => {
                    known.insert(name.clone());
                }
                ItemKind::Use { path, alias, .. } => {
                    let Some(bound) = alias.as_ref().or(path.last()) else {
                        continue;
                    };
                    let target = (folder.split)(&path.join("::"));
                    match target {
                        Some(key) if folder.decls.contains_key(&key) => {
                            bindings.insert(bound.clone(), key);
                        }
                        _ => {
                            known.insert(bound.clone());
                        }
                    }
                }
                ItemKind::Extension { .. } | ItemKind::InherentExtension { .. } => {}
            }
        }
        folder.bindings.insert(module.clone(), bindings);
        folder.known.insert(module.clone(), known);
    }
    let mut keys: Vec<Key> = folder.decls.keys().cloned().collect();
    keys.sort();
    for key in &keys {
        let span = folder.decls[key].span;
        folder.value(key, span);
    }
    for (module, syntax) in modules.iter_mut() {
        let mut rewriter = Rewriter {
            folder: &folder,
            module,
            scopes: Vec::new(),
            generics: Vec::new(),
            diagnostics: Vec::new(),
        };
        rewriter.module(syntax);
        let diagnostics = rewriter.diagnostics;
        folder.diagnostics.extend(diagnostics);
        let bound = folder
            .bindings
            .get(module.as_str())
            .cloned()
            .unwrap_or_default();
        syntax.items.retain(|item| match &item.kind {
            ItemKind::Const { .. } => false,
            ItemKind::Use { path, alias, .. } => {
                let name = alias.as_ref().or(path.last());
                !name.is_some_and(|name| {
                    bound
                        .get(name)
                        .is_some_and(|key| (folder.split)(&path.join("::")).as_ref() == Some(key))
                })
            }
            _ => true,
        });
    }
    folder.diagnostics
}

fn module_names_repeat_count(module: &Module) -> bool {
    // Cheap pre-check: only a repeat count spelled as a name needs this pass
    // when no const exists, and then it is an error reported by the rewriter.
    fn expr(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::RepeatArray { value, count } => {
                !count.raw.bytes().all(|b| b.is_ascii_digit() || b == b'_') || expr(value)
            }
            ExprKind::Array(items) => items.iter().any(expr),
            ExprKind::Tuple(items) => items.iter().any(|i| expr(&i.value)),
            ExprKind::Index { base, index } => expr(base) || expr(index),
            ExprKind::Unary { operand, .. } => expr(operand),
            ExprKind::Cast { value, .. } => expr(value),
            ExprKind::Binary { left, right, .. } => expr(left) || expr(right),
            ExprKind::Call {
                callee, arguments, ..
            } => expr(callee) || arguments.iter().any(expr),
            ExprKind::Field { base, .. } => expr(base),
            ExprKind::Struct { fields, .. } => fields.iter().any(|f| expr(&f.value)),
            ExprKind::Block(b) => block(b),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => expr(condition) || block(then_branch) || else_branch.as_deref().is_some_and(expr),
            ExprKind::Match { scrutinee, arms } => {
                expr(scrutinee) || arms.iter().any(|a| expr(&a.body))
            }
            _ => false,
        }
    }
    fn block(b: &Block) -> bool {
        b.statements.iter().any(|s| match &s.kind {
            StatementKind::Binding { value, .. }
            | StatementKind::Destructure { value, .. }
            | StatementKind::TupleDestructure { value, .. }
            | StatementKind::Expression(value)
            | StatementKind::Return(Some(value)) => expr(value),
            StatementKind::Assign { target, value, .. } => expr(target) || expr(value),
            StatementKind::Loop(body) => block(body),
            StatementKind::ForEach { items, body, .. } => expr(items) || block(body),
            StatementKind::RangeLoop {
                start, end, body, ..
            } => expr(start) || expr(end) || block(body),
            _ => false,
        }) || b.tail.as_deref().is_some_and(expr)
    }
    module.items.iter().any(|item| match &item.kind {
        ItemKind::Function { body, .. } => block(body),
        ItemKind::Extension { methods, .. } | ItemKind::InherentExtension { methods, .. } => {
            methods.iter().any(|m| m.body.as_ref().is_some_and(block))
        }
        _ => false,
    })
}

impl Folder<'_> {
    fn display(&self, key: &Key, same_module: bool, relative_to: &str) -> String {
        if same_module && key.0 == relative_to {
            key.1.clone()
        } else {
            format!("{}::{}", key.0, key.1)
        }
    }

    /// The value of a constant, evaluating it on first use. `None` means an
    /// error was already reported for it (or for one of its dependencies).
    fn value(&mut self, key: &Key, use_span: Span) -> Option<Const> {
        if let Some(value) = self.values.get(key) {
            return value.clone();
        }
        if let Some(position) = self.stack.iter().position(|entry| entry == key) {
            let cycle: Vec<Key> = self.stack[position..].to_vec();
            if cycle
                .iter()
                .all(|entry| self.cycles_reported.insert(entry.clone()))
            {
                let mut names: Vec<String> = cycle
                    .iter()
                    .map(|entry| self.display(entry, cycle.iter().all(|e| e.0 == key.0), &key.0))
                    .collect();
                names.push(self.display(key, cycle.iter().all(|e| e.0 == key.0), &key.0));
                self.diagnostics.push(error(
                    Category::StaticOperation,
                    4,
                    use_span,
                    format!("constant cycle: {}", names.join(" -> ")),
                ));
            }
            return None;
        }
        let Some(decl) = self.decls.get(key) else {
            return None;
        };
        let (ty, initializer) = (decl.ty.clone(), decl.value.clone());
        self.stack.push(key.clone());
        let result = self.evaluate_declaration(key, &ty, &initializer);
        self.stack.pop();
        self.values.insert(key.clone(), result.clone());
        result
    }

    fn evaluate_declaration(&mut self, key: &Key, ty: &Type, initializer: &Expr) -> Option<Const> {
        let declared = match (ty.path.as_slice(), ty.arguments.is_empty()) {
            ([name], true) => CTy::from_name(name),
            _ => None,
        };
        let Some(declared) = declared else {
            let hint = if ty.path.as_slice() == ["String"] {
                "; the type is spelled `string`"
            } else {
                ""
            };
            self.diagnostics.push(error(
                Category::Type,
                17,
                ty.span,
                format!(
                    "a const type must be an integer type, f32, f64, bool, char or string{hint}"
                ),
            ));
            return None;
        };
        let (found, value) = self.eval(initializer, Some(declared), &key.0)?;
        if found != declared {
            self.diagnostics.push(error(
                Category::Type,
                2,
                initializer.span,
                format!(
                    "expected {}, found {} (the initializer of const `{}`)",
                    declared.name(),
                    found.name(),
                    key.1
                ),
            ));
            return None;
        }
        Some((declared, value))
    }

    fn fail(
        &mut self,
        category: Category,
        number: u16,
        span: Span,
        message: &str,
    ) -> Option<Const> {
        self.diagnostics
            .push(error(category, number, span, message));
        None
    }

    fn not_constant(&mut self, span: Span, what: &str) -> Option<Const> {
        self.fail(
            Category::StaticOperation,
            5,
            span,
            &format!("{what} is not allowed in a const initializer; use literals, other constants and built-in operators"),
        )
    }

    fn eval(&mut self, expr: &Expr, hint: Option<CTy>, module: &str) -> Option<Const> {
        match &expr.kind {
            ExprKind::Number(raw) => self.number(expr.span, raw, false, hint),
            ExprKind::TypedNumber { .. } => None,
            ExprKind::Bool(value) => Some((CTy::Bool, CVal::Bool(*value))),
            ExprKind::CharLiteral(value) => Some((CTy::Char, CVal::Char(*value))),
            ExprKind::StringLiteral(text) => Some((CTy::Str, CVal::Str(text.clone()))),
            ExprKind::Interpolation(_) => self.not_constant(expr.span, "string interpolation"),
            ExprKind::Path(path) => self.path(expr.span, path, module),
            ExprKind::Unary { operator, operand } => {
                self.unary(expr, operator, operand, hint, module)
            }
            ExprKind::Cast { value, target } => {
                let (source, value) = self.eval(value, None, module)?;
                let target_ty = match (target.path.as_slice(), target.arguments.is_empty()) {
                    ([name], true) => CTy::from_name(name).filter(|ty| ty.is_numeric()),
                    _ => None,
                };
                let Some(target_ty) = target_ty.filter(|_| source.is_numeric()) else {
                    return self.fail(
                        Category::Type,
                        7,
                        expr.span,
                        "numeric casts require an integer or floating-point source and target",
                    );
                };
                Some((target_ty, cast(source, &value, target_ty)))
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => self.binary(expr, operator, left, right, hint, module),
            ExprKind::Call { .. } => self.not_constant(expr.span, "a call"),
            ExprKind::Block(_) | ExprKind::If { .. } | ExprKind::Match { .. } => {
                self.not_constant(expr.span, "a block, `if` or `match`")
            }
            _ => self.not_constant(expr.span, "this expression"),
        }
    }

    fn number(
        &mut self,
        span: Span,
        raw: &str,
        negative: bool,
        hint: Option<CTy>,
    ) -> Option<Const> {
        let cleaned = raw.replace('_', "");
        if raw.contains(['.', 'e', 'E']) {
            let ty = hint.filter(|ty| ty.is_float()).unwrap_or(CTy::F64);
            let Ok(mut value) = cleaned.parse::<f64>() else {
                return self.fail(Category::Type, 8, span, "invalid floating-point literal");
            };
            if negative {
                value = -value;
            }
            if ty == CTy::F32 {
                value = (value as f32) as f64;
            }
            return Some((ty, CVal::Float(value)));
        }
        let ty = hint.filter(|ty| ty.is_int()).unwrap_or(CTy::I32);
        let ty = if negative && !ty.is_signed() {
            CTy::I32
        } else {
            ty
        };
        let Ok(magnitude) = cleaned.parse::<u128>() else {
            return self.fail(
                Category::Type,
                8,
                span,
                &format!("integer literal does not fit {}", ty.name()),
            );
        };
        let value = if negative {
            -(magnitude.min(i128::MAX as u128) as i128)
        } else {
            magnitude.min(i128::MAX as u128) as i128
        };
        let (min, max) = ty.range().expect("integer type");
        if value < min || value > max {
            return self.fail(
                Category::Type,
                8,
                span,
                &format!("integer literal does not fit {}", ty.name()),
            );
        }
        Some((ty, CVal::Int(value)))
    }

    fn path(&mut self, span: Span, path: &[String], module: &str) -> Option<Const> {
        let key = if let [name] = path {
            match self.bindings.get(module).and_then(|b| b.get(name)) {
                Some(key) => key.clone(),
                None => {
                    // Unknown names were already reported by the name pass.
                    if self
                        .known
                        .get(module)
                        .is_some_and(|known| known.contains(name))
                    {
                        return self.fail(
                            Category::StaticOperation,
                            5,
                            span,
                            &format!("`{name}` is not a constant; a const initializer can use only literals, other constants and built-in operators"),
                        );
                    }
                    return None;
                }
            }
        } else {
            match (self.split)(&path.join("::")) {
                Some(key) if self.decls.contains_key(&key) => key,
                _ => {
                    return self.fail(
                        Category::StaticOperation,
                        5,
                        span,
                        &format!("`{}` is not a constant", path.join("::")),
                    );
                }
            }
        };
        self.value(&key, span)
    }

    fn unary(
        &mut self,
        expr: &Expr,
        operator: &str,
        operand: &Expr,
        hint: Option<CTy>,
        module: &str,
    ) -> Option<Const> {
        match operator {
            "-" => {
                if let ExprKind::Number(raw) = &operand.kind {
                    return self.number(expr.span, raw, true, hint);
                }
                let (ty, value) = self.eval(operand, None, module)?;
                match value {
                    CVal::Float(value) if ty.is_float() => Some((ty, CVal::Float(-value))),
                    CVal::Int(value) if ty.is_int() => {
                        if !ty.is_signed() {
                            return self.fail(
                                Category::Type,
                                7,
                                expr.span,
                                "negation requires a signed numeric type",
                            );
                        }
                        self.int_result(expr.span, ty, -value)
                    }
                    _ => self.fail(
                        Category::Type,
                        7,
                        expr.span,
                        "negation requires a signed numeric type or Neg implementation",
                    ),
                }
            }
            "+" => {
                let (ty, value) = self.eval(operand, hint.filter(|ty| ty.is_numeric()), module)?;
                if ty.is_numeric() {
                    Some((ty, value))
                } else {
                    self.fail(
                        Category::Type,
                        7,
                        expr.span,
                        "unary arithmetic requires a number",
                    )
                }
            }
            "!" => {
                let (ty, value) = self.eval(operand, Some(CTy::Bool), module)?;
                match value {
                    CVal::Bool(value) => Some((CTy::Bool, CVal::Bool(!value))),
                    _ => self.mismatch(operand.span, CTy::Bool, ty),
                }
            }
            _ => self.fail(
                Category::Type,
                7,
                expr.span,
                &format!("unsupported unary operator '{operator}'"),
            ),
        }
    }

    fn mismatch(&mut self, span: Span, expected: CTy, found: CTy) -> Option<Const> {
        self.fail(
            Category::Type,
            2,
            span,
            &format!("expected {}, found {}", expected.name(), found.name()),
        )
    }

    fn int_result(&mut self, span: Span, ty: CTy, value: i128) -> Option<Const> {
        let (min, max) = ty.range().expect("integer type");
        if value < min || value > max {
            return self.fail(
                Category::StaticOperation,
                1,
                span,
                "integer overflow in statically known expression",
            );
        }
        Some((ty, CVal::Int(value)))
    }

    fn binary(
        &mut self,
        expr: &Expr,
        operator: &str,
        left: &Expr,
        right: &Expr,
        hint: Option<CTy>,
        module: &str,
    ) -> Option<Const> {
        let bool_op = matches!(operator, "&&" | "||");
        let bit_op = matches!(operator, "&" | "^" | "|" | "<<" | ">>");
        let (left_ty, left_value, right_ty, right_value);
        if bool_op {
            let l = self.eval(left, Some(CTy::Bool), module);
            let r = self.eval(right, Some(CTy::Bool), module);
            let (l, r) = (l?, r?);
            if l.0 != CTy::Bool {
                return self.mismatch(left.span, CTy::Bool, l.0);
            }
            if r.0 != CTy::Bool {
                return self.mismatch(right.span, CTy::Bool, r.0);
            }
            let (CVal::Bool(l), CVal::Bool(r)) = (l.1, r.1) else {
                return None;
            };
            return Some((
                CTy::Bool,
                CVal::Bool(if operator == "&&" { l && r } else { l || r }),
            ));
        }
        if bit_op {
            let shifting = matches!(operator, "<<" | ">>");
            let literal_left = matches!(left.kind, ExprKind::Number(_))
                || matches!(&left.kind, ExprKind::Unary { operator, operand }
                    if (operator == "+" || operator == "-")
                        && matches!(operand.kind, ExprKind::Number(_)));
            let int_hint = hint.filter(|ty| ty.is_int());
            let mut early_right = None;
            let l = if !shifting && int_hint.is_none() && literal_left {
                let right_hint = numeric::is_literal_tree(right).then_some(CTy::U32);
                let r = self.eval(right, right_hint, module)?;
                let l = self.eval(left, Some(r.0), module)?;
                early_right = Some(r);
                l
            } else {
                let fallback = numeric::is_literal_tree(left).then_some(CTy::U32);
                self.eval(left, int_hint.or(fallback), module)?
            };
            if !l.0.is_int() {
                return self.fail(
                    Category::Type,
                    7,
                    left.span,
                    if shifting {
                        "shift requires integers"
                    } else {
                        "bitwise operators require integers"
                    },
                );
            }
            let right_expected = if shifting { CTy::U32 } else { l.0 };
            let r = match early_right {
                Some(r) => r,
                None => self.eval(right, Some(right_expected), module)?,
            };
            if r.0 != right_expected {
                return self.mismatch(right.span, right_expected, r.0);
            }
            let (CVal::Int(lv), CVal::Int(rv)) = (l.1, r.1) else {
                return None;
            };
            let kind = l.0.int_kind()?;
            let value = if shifting {
                match numeric::shift(kind, operator == "<<", lv, rv as u128) {
                    Some(value) => value,
                    None => {
                        return self.fail(
                            Category::StaticOperation,
                            3,
                            expr.span,
                            &format!(
                                "{} shift count must be less than {}",
                                kind.name(),
                                kind.bits
                            ),
                        );
                    }
                }
            } else {
                numeric::bitwise(operator.chars().next().expect("operator"), lv, rv)
            };
            return Some((l.0, CVal::Int(value)));
        }
        let expected_num = hint.filter(|ty| ty.is_numeric());
        let is_literal = |e: &Expr| {
            matches!(e.kind, ExprKind::Number(_))
                || matches!(&e.kind, ExprKind::Unary { operator, operand }
                    if (operator == "+" || operator == "-")
                        && matches!(operand.kind, ExprKind::Number(_)))
        };
        if expected_num.is_none() && is_literal(left) {
            let r = self.eval(right, None, module)?;
            let l = self.eval(left, Some(r.0), module)?;
            (left_ty, left_value, right_ty, right_value) = (l.0, l.1, r.0, r.1);
        } else {
            let l = self.eval(left, expected_num, module)?;
            let r = self.eval(right, Some(l.0), module)?;
            (left_ty, left_value, right_ty, right_value) = (l.0, l.1, r.0, r.1);
        }
        let arithmetic = matches!(operator, "+" | "-" | "*" | "/" | "%");
        let ordering = matches!(operator, "<" | "<=" | ">" | ">=");
        if arithmetic && !left_ty.is_numeric() {
            return self.fail(Category::Type, 7, left.span, "arithmetic requires numbers");
        }
        if operator == "%" && !left_ty.is_int() {
            return self.fail(Category::Type, 7, expr.span, "remainder requires integers");
        }
        if ordering && !left_ty.is_numeric() {
            return self.fail(Category::Type, 7, left.span, "ordering requires numbers");
        }
        if matches!(operator, "==" | "!=")
            && !(left_ty.is_numeric() || matches!(left_ty, CTy::Bool | CTy::Char))
        {
            return self.fail(
                Category::Type,
                7,
                left.span,
                "equality requires numeric or Bool operands",
            );
        }
        if right_ty != left_ty {
            return self.mismatch(right.span, left_ty, right_ty);
        }
        match (&left_value, &right_value) {
            (CVal::Int(l), CVal::Int(r)) => {
                let (l, r) = (*l, *r);
                if arithmetic {
                    let result = match operator {
                        "+" => l.checked_add(r),
                        "-" => l.checked_sub(r),
                        "*" => l.checked_mul(r),
                        "/" | "%" if r == 0 => {
                            return self.fail(
                                Category::StaticOperation,
                                2,
                                expr.span,
                                "division or remainder by zero in statically known expression",
                            );
                        }
                        "/" => l.checked_div(r),
                        _ => l.checked_rem(r),
                    };
                    let Some(result) = result else {
                        return self.fail(
                            Category::StaticOperation,
                            1,
                            expr.span,
                            "integer overflow in statically known expression",
                        );
                    };
                    return self.int_result(expr.span, left_ty, result);
                }
                Some((CTy::Bool, CVal::Bool(compare(operator, l.cmp(&r)))))
            }
            (CVal::Float(l), CVal::Float(r)) => {
                let (l, r) = (*l, *r);
                if arithmetic {
                    let result = if left_ty == CTy::F32 {
                        let (l, r) = (l as f32, r as f32);
                        (match operator {
                            "+" => l + r,
                            "-" => l - r,
                            "*" => l * r,
                            _ => l / r,
                        }) as f64
                    } else {
                        match operator {
                            "+" => l + r,
                            "-" => l - r,
                            "*" => l * r,
                            _ => l / r,
                        }
                    };
                    return Some((left_ty, CVal::Float(result)));
                }
                let result = match operator {
                    "==" => l == r,
                    "!=" => l != r,
                    "<" => l < r,
                    "<=" => l <= r,
                    ">" => l > r,
                    _ => l >= r,
                };
                Some((CTy::Bool, CVal::Bool(result)))
            }
            (CVal::Bool(l), CVal::Bool(r)) => {
                Some((CTy::Bool, CVal::Bool((operator == "==") == (l == r))))
            }
            (CVal::Char(l), CVal::Char(r)) => {
                Some((CTy::Bool, CVal::Bool((operator == "==") == (l == r))))
            }
            _ => None,
        }
    }
}

fn compare(operator: &str, ordering: std::cmp::Ordering) -> bool {
    use std::cmp::Ordering::{Equal, Greater, Less};
    match operator {
        "==" => ordering == Equal,
        "!=" => ordering != Equal,
        "<" => ordering == Less,
        "<=" => ordering != Greater,
        ">" => ordering == Greater,
        _ => ordering != Less,
    }
}

/// Rust `as` semantics between numeric types (NUM-04).
fn cast(source: CTy, value: &CVal, target: CTy) -> CVal {
    match value {
        CVal::Int(value) => {
            if target.is_float() {
                // 64-bit sources convert from their own width (u64 values
                // above i64::MAX are stored unsigned in the i128).
                let number = match (source, target) {
                    (CTy::U64, CTy::F32) => ((*value as u64) as f32) as f64,
                    (CTy::U64, _) => (*value as u64) as f64,
                    (CTy::I64, CTy::F32) => ((*value as i64) as f32) as f64,
                    (CTy::I64, _) => (*value as i64) as f64,
                    (_, CTy::F32) => (*value as f32) as f64,
                    _ => *value as f64,
                };
                CVal::Float(number)
            } else {
                CVal::Int(wrap(*value, target))
            }
        }
        CVal::Float(value) => match target {
            CTy::F32 => CVal::Float((*value as f32) as f64),
            CTy::F64 => CVal::Float(*value),
            CTy::I8 => CVal::Int(*value as i8 as i128),
            CTy::I16 => CVal::Int(*value as i16 as i128),
            CTy::I32 => CVal::Int(*value as i32 as i128),
            CTy::I64 => CVal::Int(*value as i64 as i128),
            CTy::U8 => CVal::Int(*value as u8 as i128),
            CTy::U16 => CVal::Int(*value as u16 as i128),
            CTy::U32 => CVal::Int(*value as u32 as i128),
            _ => CVal::Int(*value as u64 as i128),
        },
        other => other.clone(),
    }
}

fn wrap(value: i128, target: CTy) -> i128 {
    let bits = target.bits();
    let mask = if bits == 64 {
        u64::MAX as u128
    } else {
        (1u128 << bits) - 1
    };
    let wrapped = (value as u128) & mask;
    if target.is_signed() && wrapped & (1u128 << (bits - 1)) != 0 {
        (wrapped as i128) - (1i128 << bits)
    } else {
        wrapped as i128
    }
}

struct Rewriter<'a, 'b> {
    folder: &'a Folder<'b>,
    module: &'a str,
    scopes: Vec<HashSet<String>>,
    /// Generic parameter names (type and const) of the enclosing items.
    generics: Vec<HashSet<String>>,
    diagnostics: Vec<Diagnostic>,
}

impl Rewriter<'_, '_> {
    fn lookup(&self, name: &str) -> Lookup {
        if self.scopes.iter().any(|scope| scope.contains(name)) {
            return Lookup::NotConst;
        }
        match self
            .folder
            .bindings
            .get(self.module)
            .and_then(|b| b.get(name))
        {
            None => Lookup::NotConst,
            Some(key) => match self.folder.values.get(key) {
                Some(Some(value)) => Lookup::Value(value.clone()),
                _ => Lookup::Failed,
            },
        }
    }

    fn lookup_path(&self, path: &[String]) -> Lookup {
        match path {
            [name] => self.lookup(name),
            _ => match (self.folder.split)(&path.join("::")) {
                Some(key) if self.folder.decls.contains_key(&key) => {
                    match self.folder.values.get(&key) {
                        Some(Some(value)) => Lookup::Value(value.clone()),
                        _ => Lookup::Failed,
                    }
                }
                _ => Lookup::NotConst,
            },
        }
    }

    fn error(&mut self, category: Category, number: u16, span: Span, message: String) {
        self.diagnostics
            .push(error(category, number, span, message));
    }

    fn module(&mut self, module: &mut Module) {
        for item in &mut module.items {
            match &mut item.kind {
                ItemKind::Function {
                    generic_parameters,
                    bounds,
                    parameters,
                    result,
                    body,
                    ..
                } => {
                    let names: HashSet<String> =
                        generic_parameters.iter().map(|p| p.name.clone()).collect();
                    self.generics.push(names.clone());
                    for bound in bounds {
                        self.ty(&mut bound.interface);
                    }
                    for parameter in parameters.iter_mut() {
                        self.ty(&mut parameter.ty);
                    }
                    if let Some(result) = result {
                        self.ty(result);
                    }
                    let mut scope = names;
                    scope.extend(parameters.iter().map(|p| p.name.clone()));
                    self.scopes.push(scope);
                    self.block(body);
                    self.scopes.pop();
                    self.generics.pop();
                }
                ItemKind::Type {
                    generic_parameters,
                    bounds,
                    definition,
                    base,
                    ..
                } => {
                    self.generics
                        .push(generic_parameters.iter().map(|p| p.name.clone()).collect());
                    for bound in bounds {
                        self.ty(&mut bound.interface);
                    }
                    if let Some(base) = base {
                        self.ty(base);
                    }
                    match definition {
                        TypeDefinition::Alias(ty) => self.ty(ty),
                        TypeDefinition::Bodyless => {}
                        TypeDefinition::Struct(fields) => {
                            for field in fields {
                                self.ty(&mut field.ty);
                            }
                        }
                        TypeDefinition::Enum(variants) => {
                            for variant in variants {
                                for payload in &mut variant.payload {
                                    self.ty(payload);
                                }
                            }
                        }
                    }
                    self.generics.pop();
                }
                ItemKind::Interface { methods, .. } => self.methods(methods, &HashSet::new()),
                ItemKind::Extension {
                    target,
                    interface,
                    associated_types,
                    methods,
                    ..
                } => {
                    self.ty(target);
                    self.ty(interface);
                    for binding in associated_types {
                        if let Some(ty) = &mut binding.ty {
                            self.ty(ty);
                        }
                    }
                    self.methods(methods, &HashSet::new());
                }
                ItemKind::InherentExtension {
                    target,
                    generic_parameters,
                    methods,
                    ..
                } => {
                    let names: HashSet<String> =
                        generic_parameters.iter().map(|p| p.name.clone()).collect();
                    self.generics.push(names.clone());
                    self.ty(target);
                    self.methods(methods, &names);
                    self.generics.pop();
                }
                ItemKind::Use { .. } | ItemKind::Const { .. } => {}
            }
        }
    }

    fn methods(&mut self, methods: &mut [InterfaceMethod], generics: &HashSet<String>) {
        for method in methods {
            for parameter in &mut method.parameters {
                self.ty(&mut parameter.ty);
            }
            if let Some(result) = &mut method.result {
                self.ty(result);
            }
            if let Some(body) = &mut method.body {
                let mut scope = generics.clone();
                scope.insert("self".to_owned());
                scope.extend(method.parameters.iter().map(|p| p.name.clone()));
                self.scopes.push(scope);
                self.block(body);
                self.scopes.pop();
            }
        }
    }

    fn shadowed_by_generic(&self, name: &str) -> bool {
        self.generics.iter().any(|names| names.contains(name))
    }

    /// Replace constants used as array lengths or const arguments.
    fn ty(&mut self, ty: &mut Type) {
        let span = ty.span;
        for argument in &mut ty.arguments {
            let name = match argument {
                TypeArgument::Const(name) => Some(name.clone()),
                TypeArgument::Type(inner)
                    if inner.path.len() == 1 && inner.arguments.is_empty() =>
                {
                    Some(inner.path[0].clone())
                }
                _ => None,
            };
            if let Some(name) = name {
                if !self.shadowed_by_generic(&name) {
                    match self.lookup(&name) {
                        Lookup::Value((CTy::U32, CVal::Int(value))) => {
                            *argument = TypeArgument::Integer(memobits_syntax::IntegerLiteral {
                                span,
                                raw: value.to_string(),
                            });
                            continue;
                        }
                        Lookup::Value((found, _)) => {
                            self.error(
                                Category::Type,
                                17,
                                span,
                                format!(
                                    "const `{name}` is {}; an array length or const argument must be a u32 constant",
                                    found.name()
                                ),
                            );
                            continue;
                        }
                        Lookup::Failed | Lookup::NotConst => {}
                    }
                }
            }
            match argument {
                TypeArgument::Type(inner)
                | TypeArgument::Reference {
                    referent: inner, ..
                } => self.ty(inner),
                TypeArgument::TupleField { ty, .. } => self.ty(ty),
                TypeArgument::Const(_) | TypeArgument::Integer(_) => {}
            }
        }
    }

    fn type_arguments(&mut self, span: Span, arguments: &mut Vec<TypeArgument>) {
        let mut wrapper = Type {
            span,
            path: Vec::new(),
            arguments: std::mem::take(arguments),
        };
        self.ty(&mut wrapper);
        *arguments = wrapper.arguments;
    }

    fn block(&mut self, block: &mut Block) {
        self.scopes.push(HashSet::new());
        for statement in &mut block.statements {
            match &mut statement.kind {
                StatementKind::Binding {
                    name,
                    annotation,
                    value,
                    ..
                } => {
                    if let Some(annotation) = annotation {
                        self.ty(annotation);
                    }
                    self.expr(value);
                    self.scopes.last_mut().unwrap().insert(name.clone());
                }
                StatementKind::Destructure { fields, value, .. } => {
                    self.expr(value);
                    for field in fields {
                        self.scopes
                            .last_mut()
                            .unwrap()
                            .insert(field.binding.clone());
                    }
                }
                StatementKind::TupleDestructure {
                    elements, value, ..
                } => {
                    self.expr(value);
                    for element in elements.iter() {
                        self.bind_tuple(element);
                    }
                }
                StatementKind::Assign { target, value, .. } => {
                    self.assignment_target(target);
                    self.expr(value);
                }
                StatementKind::Expression(value) | StatementKind::Return(Some(value)) => {
                    self.expr(value)
                }
                StatementKind::Return(None) | StatementKind::Break | StatementKind::Continue => {}
                StatementKind::Loop(body) => self.block(body),
                StatementKind::ForEach {
                    binding,
                    items,
                    body,
                } => {
                    self.expr(items);
                    self.scopes.push(HashSet::from([binding.clone()]));
                    self.block(body);
                    self.scopes.pop();
                }
                StatementKind::RangeLoop {
                    binding,
                    start,
                    end,
                    body,
                    ..
                } => {
                    self.expr(start);
                    self.expr(end);
                    self.scopes.push(HashSet::from([binding.clone()]));
                    self.block(body);
                    self.scopes.pop();
                }
            }
        }
        if let Some(tail) = &mut block.tail {
            self.expr(tail);
        }
        self.scopes.pop();
    }

    fn bind_tuple(&mut self, element: &TupleBinding) {
        if let Some(nested) = &element.nested {
            for element in nested {
                self.bind_tuple(element);
            }
        } else if element.binding != "_" {
            self.scopes
                .last_mut()
                .unwrap()
                .insert(element.binding.clone());
        }
    }

    fn assignment_target(&mut self, target: &mut Expr) {
        let mut root = &*target;
        loop {
            match &root.kind {
                ExprKind::Index { base, .. } | ExprKind::Field { base, .. } => root = base,
                _ => break,
            }
        }
        if let ExprKind::Path(path) = &root.kind {
            if matches!(self.lookup_path(path), Lookup::Value(_) | Lookup::Failed) {
                let span = root.span;
                self.error(
                    Category::Type,
                    4,
                    span,
                    format!("cannot assign to constant '{}'", path.join("::")),
                );
                return;
            }
        }
        self.expr(target);
    }

    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Wildcard => {}
            PatternKind::Binding(name) => {
                if self
                    .folder
                    .bindings
                    .get(self.module)
                    .is_some_and(|b| b.contains_key(name))
                {
                    self.error(
                        Category::Type,
                        17,
                        pattern.span,
                        format!(
                            "constant patterns are not supported yet: `{name}` would bind a new variable here; compare with `==` in an `if` or rename the binding"
                        ),
                    );
                }
                self.scopes.last_mut().unwrap().insert(name.clone());
            }
            PatternKind::Variant { slots, .. } => {
                for slot in slots {
                    self.pattern(slot);
                }
            }
            PatternKind::Tuple(elements) => {
                for element in elements {
                    self.pattern(element);
                }
            }
        }
    }

    fn inline(&mut self, expr: &mut Expr, constant: Const) {
        let span = expr.span;
        expr.kind = match constant {
            (ty, CVal::Int(value)) => ExprKind::TypedNumber {
                raw: value.to_string(),
                ty: Type {
                    span,
                    path: vec![ty.name().to_owned()],
                    arguments: Vec::new(),
                },
            },
            (ty, CVal::Float(value)) => ExprKind::TypedNumber {
                raw: format!("{value:?}"),
                ty: Type {
                    span,
                    path: vec![ty.name().to_owned()],
                    arguments: Vec::new(),
                },
            },
            (_, CVal::Bool(value)) => ExprKind::Bool(value),
            (_, CVal::Char(value)) => ExprKind::CharLiteral(value),
            (_, CVal::Str(text)) => ExprKind::StringLiteral(text),
        };
    }

    fn exprs(&mut self, expressions: &mut [Expr]) {
        for expression in expressions {
            self.expr(expression);
        }
    }

    fn expr(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Path(path) => {
                if let Lookup::Value(constant) = self.lookup_path(path) {
                    self.inline(expr, constant);
                }
            }
            ExprKind::Interpolation(parts) => {
                let mut merged: Vec<InterpolationPart> = Vec::new();
                let mut changed = false;
                for part in std::mem::take(parts) {
                    let text = match &part {
                        InterpolationPart::Text(text) => Some(text.clone()),
                        InterpolationPart::Value(value) => match &value.kind {
                            ExprKind::Path(path) => match self.lookup_path(path) {
                                Lookup::Value((_, CVal::Int(v))) => Some(v.to_string()),
                                Lookup::Value((_, CVal::Bool(v))) => Some(v.to_string()),
                                Lookup::Value((_, CVal::Char(v))) => Some(v.to_string()),
                                Lookup::Value((_, CVal::Str(v))) => Some(v),
                                Lookup::Value((_, CVal::Float(_))) => {
                                    let span = value.span;
                                    self.error(
                                        Category::Type,
                                        17,
                                        span,
                                        "formatting floating-point values in string interpolation is not supported yet".into(),
                                    );
                                    Some(String::new())
                                }
                                _ => None,
                            },
                            _ => None,
                        },
                    };
                    match (text, part) {
                        (Some(text), InterpolationPart::Value(_)) => {
                            changed = true;
                            push_text(&mut merged, &text);
                        }
                        (Some(text), InterpolationPart::Text(_)) => push_text(&mut merged, &text),
                        (None, part) => merged.push(part),
                    }
                }
                if changed
                    && merged
                        .iter()
                        .all(|p| matches!(p, InterpolationPart::Text(_)))
                {
                    let text: String = merged
                        .iter()
                        .map(|p| match p {
                            InterpolationPart::Text(t) => t.as_str(),
                            InterpolationPart::Value(_) => "",
                        })
                        .collect();
                    expr.kind = ExprKind::StringLiteral(text);
                } else {
                    *parts = merged;
                }
            }
            ExprKind::Array(elements) => self.exprs(elements),
            ExprKind::Tuple(elements) => {
                for element in elements {
                    self.expr(&mut element.value);
                }
            }
            ExprKind::RepeatArray { value, count } => {
                self.expr(value);
                if !count.raw.bytes().all(|b| b.is_ascii_digit() || b == b'_') {
                    let name = count.raw.clone();
                    match self.lookup(&name) {
                        Lookup::Value((CTy::U32, CVal::Int(v))) => count.raw = v.to_string(),
                        Lookup::Value((found, _)) => {
                            let span = count.span;
                            self.error(
                                Category::Type,
                                17,
                                span,
                                format!(
                                    "const `{name}` is {}; an array repeat count must be a u32 constant",
                                    found.name()
                                ),
                            );
                        }
                        Lookup::Failed => {}
                        Lookup::NotConst => {
                            let span = count.span;
                            self.error(
                                Category::Name,
                                1,
                                span,
                                format!("unknown constant '{name}' in an array repeat count"),
                            );
                        }
                    }
                }
            }
            ExprKind::Index { base, index } => {
                self.expr(base);
                self.expr(index);
            }
            ExprKind::Unary { operand, .. } => self.expr(operand),
            ExprKind::Cast { value, target } => {
                self.expr(value);
                self.ty(target);
            }
            ExprKind::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Call {
                callee,
                arguments,
                interface,
            } => {
                self.expr(callee);
                self.exprs(arguments);
                if let Some(interface) = interface {
                    self.ty(interface);
                }
            }
            ExprKind::Field { base, .. } => self.expr(base),
            ExprKind::Struct {
                type_arguments,
                fields,
                ..
            } => {
                let span = expr.span;
                self.type_arguments(span, type_arguments);
                for field in fields {
                    self.expr(&mut field.value);
                }
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition);
                self.block(then_branch);
                if let Some(other) = else_branch {
                    self.expr(other);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.scopes.push(HashSet::new());
                    self.pattern(&arm.pattern);
                    self.expr(&mut arm.body);
                    self.scopes.pop();
                }
            }
            ExprKind::Number(_)
            | ExprKind::TypedNumber { .. }
            | ExprKind::StringLiteral(_)
            | ExprKind::CharLiteral(_)
            | ExprKind::Bool(_) => {}
        }
    }
}

fn push_text(parts: &mut Vec<InterpolationPart>, text: &str) {
    if text.is_empty() {
        return;
    }
    if let Some(InterpolationPart::Text(last)) = parts.last_mut() {
        last.push_str(text);
    } else {
        parts.push(InterpolationPart::Text(text.to_owned()));
    }
}
