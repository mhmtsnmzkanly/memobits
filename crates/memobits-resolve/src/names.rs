use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_syntax::{
    Block, Expr, ExprKind, ItemKind, Module, StatementKind, Type, TypeArgument, TypeDefinition,
};
use std::collections::{BTreeMap, BTreeSet};

/// Check unqualified expression names. Qualified paths are returned to the
/// module loader for visibility checking and dependency discovery.
pub(crate) fn check(
    module: &Module,
    prelude: impl Iterator<Item = (String, String)>,
) -> (Vec<Diagnostic>, Vec<(String, Span, bool)>) {
    let prelude: BTreeMap<String, String> = prelude.collect();
    let mut imports = prelude.clone();
    let mut globals: BTreeSet<String> = prelude.keys().cloned().collect();
    for item in &module.items {
        match &item.kind {
            ItemKind::Function { name, .. } | ItemKind::Type { name, .. } => {
                globals.insert(name.clone());
            }
            ItemKind::Use { path, alias, .. } => {
                if let Some(name) = alias.as_ref().or(path.last()) {
                    globals.insert(name.clone());
                    imports.insert(name.clone(), path.join("::"));
                }
            }
        }
    }
    let mut types: BTreeSet<String> = [
        "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "Bool", "String",
        "Char",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    types.extend(prelude.keys().cloned());
    let mut variants = BTreeMap::new();
    for item in &module.items {
        match &item.kind {
            ItemKind::Type {
                name, definition, ..
            } => {
                types.insert(name.clone());
                if let TypeDefinition::Enum(v) = definition {
                    variants.insert(
                        name.clone(),
                        v.iter().map(|v| v.name.clone()).collect::<BTreeSet<_>>(),
                    );
                }
            }
            // Imported annotation targets are verified after graph loading.
            ItemKind::Use { path, alias, .. } => {
                if let Some(n) = alias.as_ref().or(path.last()) {
                    types.insert(n.clone());
                }
            }
            _ => {}
        }
    }
    let mut checker = Checker {
        types,
        imports,
        variants,
        scopes: vec![globals],
        diagnostics: vec![],
        qualified: vec![],
    };
    for item in &module.items {
        if let ItemKind::Function {
            parameters,
            body,
            result,
            ..
        } = &item.kind
        {
            if let Some(ty) = result {
                checker.ty(ty);
            }
            checker.scopes.push(BTreeSet::new());
            for parameter in parameters {
                checker.ty(&parameter.ty);
                if !checker
                    .scopes
                    .last_mut()
                    .unwrap()
                    .insert(parameter.name.clone())
                {
                    checker.error(
                        2,
                        parameter.span,
                        format!("duplicate parameter '{}'", parameter.name),
                    );
                }
            }
            checker.block(body);
            checker.scopes.pop();
        }
    }
    for item in &module.items {
        if let ItemKind::Type { definition, .. } = &item.kind {
            match definition {
                TypeDefinition::Alias(ty) => checker.ty(ty),
                TypeDefinition::Struct(fields) => {
                    let mut names = BTreeSet::new();
                    for field in fields {
                        if !names.insert(&field.name) {
                            checker.error(
                                5,
                                field.span,
                                format!("duplicate field '{}'", field.name),
                            );
                        }
                        checker.ty(&field.ty);
                    }
                }
                TypeDefinition::Enum(variants) => {
                    let mut names = BTreeSet::new();
                    for variant in variants {
                        if !names.insert(&variant.name) {
                            checker.error(
                                6,
                                variant.span,
                                format!("duplicate variant '{}'", variant.name),
                            );
                        }
                        for ty in &variant.payload {
                            checker.ty(ty);
                        }
                    }
                }
            }
        }
    }
    (checker.diagnostics, checker.qualified)
}
struct Checker {
    types: BTreeSet<String>,
    imports: BTreeMap<String, String>,
    variants: BTreeMap<String, BTreeSet<String>>,
    scopes: Vec<BTreeSet<String>>,
    diagnostics: Vec<Diagnostic>,
    qualified: Vec<(String, Span, bool)>,
}
impl Checker {
    fn ty(&mut self, ty: &Type) {
        for argument in &ty.arguments {
            if let TypeArgument::Type(element) = argument {
                self.ty(element);
            }
        }
        if ty.path == ["Array"] {
            return;
        }
        if ty.path.len() > 1 {
            self.qualified.push((ty.path.join("::"), ty.span, true));
        } else if let Some(path) = self.imports.get(&ty.path[0]) {
            self.qualified.push((path.clone(), ty.span, true));
        } else if !self.types.contains(&ty.path[0]) {
            self.error(3, ty.span, format!("unknown type '{}'", ty.path[0]));
        }
    }
    fn error(&mut self, number: u16, span: Span, message: String) {
        let mut d = Diagnostic::new(
            DiagnosticCode::new(Category::Name, number).unwrap(),
            Severity::Error,
            message,
        );
        d.span = Some(span);
        self.diagnostics.push(d);
    }
    fn block(&mut self, block: &Block) {
        self.scopes.push(BTreeSet::new());
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Binding {
                    name,
                    value,
                    annotation,
                    ..
                } => {
                    if let Some(ty) = annotation {
                        self.ty(ty);
                    }
                    self.expr(value);
                    // Shadowing starts after the initializer is evaluated.
                    self.scopes.last_mut().unwrap().insert(name.clone());
                }
                StatementKind::Assign { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                StatementKind::Expression(e) => self.expr(e),
                StatementKind::Return(Some(e)) => self.expr(e),
                StatementKind::Loop(b) => self.block(b),
                _ => {}
            }
        }
        if let Some(tail) = &block.tail {
            self.expr(tail);
        }
        self.scopes.pop();
    }
    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Path(path) if path.len() == 1 => {
                if !self.scopes.iter().rev().any(|s| s.contains(&path[0])) {
                    self.error(1, expr.span, format!("unknown name '{}'", path[0]));
                }
            }
            ExprKind::Path(path) => {
                if path.len() == 2 && self.variants.contains_key(&path[0]) {
                    if !self.variants[&path[0]].contains(&path[1]) {
                        self.error(
                            4,
                            expr.span,
                            format!("unknown variant '{}'", path.join("::")),
                        );
                    }
                } else {
                    let expanded = if let Some(import) = self.imports.get(&path[0]) {
                        format!("{}::{}", import, path[1..].join("::"))
                    } else {
                        path.join("::")
                    };
                    self.qualified.push((expanded, expr.span, false));
                }
            }
            ExprKind::Array(elements) => {
                for element in elements {
                    self.expr(element);
                }
            }
            ExprKind::RepeatArray { value, .. } => self.expr(value),
            ExprKind::Index { base, index } => {
                self.expr(base);
                self.expr(index);
            }
            ExprKind::Unary { operand, .. } => self.expr(operand),
            ExprKind::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee);
                for arg in arguments {
                    self.expr(arg);
                }
            }
            ExprKind::Field { base, .. } => self.expr(base),
            ExprKind::Block(b) => self.block(b),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition);
                self.block(then_branch);
                if let Some(e) = else_branch {
                    self.expr(e);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use memobits_diagnostics::SourceId;

    #[test]
    fn duplicate_members_report_the_second_member() {
        for (source, code, member) in [
            ("type Point { x: i32, x: i32 }", "NE005", "x: i32"),
            ("type State [ Idle, Idle ]", "NE006", "Idle"),
        ] {
            let parsed = memobits_syntax::parse(SourceId(0), source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let (errors, _) = check(&parsed.module, std::iter::empty());
            assert_eq!(errors.len(), 1);
            assert_eq!(errors[0].code.to_string(), code);
            assert_eq!(errors[0].span.unwrap().start, source.rfind(member).unwrap());
        }
    }
}

#[cfg(test)]
mod array_tests {
    use super::*;
    use memobits_diagnostics::SourceId;

    #[test]
    fn array_element_types_and_expression_children_are_resolved() {
        let parsed = memobits_syntax::parse(
            SourceId(0),
            "fn f(a: Array<Array<Missing, 2>, 3>) { [unknown]; [other; 2]; a[index]; }",
        );
        assert!(parsed.diagnostics.is_empty());
        let (diagnostics, _) = check(&parsed.module, std::iter::empty());
        for name in ["Missing", "unknown", "other", "index"] {
            assert!(
                diagnostics.iter().any(|d| d.message.contains(name)),
                "{name}: {diagnostics:?}"
            );
        }
        assert_eq!(diagnostics.len(), 4);
    }

    #[test]
    fn nested_array_elements_discover_qualified_type_dependencies() {
        let parsed = memobits_syntax::parse(
            SourceId(0),
            "fn f(a: Array<Array<self::model::Value, 2>, 3>) {}",
        );
        let (diagnostics, qualified) = check(&parsed.module, std::iter::empty());
        assert!(diagnostics.is_empty());
        assert_eq!(qualified.len(), 1);
        assert_eq!(qualified[0].0, "self::model::Value");
        assert!(qualified[0].2);
    }
}
