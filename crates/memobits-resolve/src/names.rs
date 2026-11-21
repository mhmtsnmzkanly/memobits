use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_syntax::{
    templates, Block, Expr, ExprKind, ItemKind, Module, PatternKind, StatementKind, Type,
    TypeArgument, TypeDefinition,
};
use std::collections::{BTreeMap, BTreeSet};

/// Check unqualified expression names. Qualified paths are returned to the
/// module loader for visibility checking and dependency discovery.
pub(crate) fn check(
    module: &Module,
    prelude: impl Iterator<Item = (String, String)>,
    allow_self_type: bool,
) -> (Vec<Diagnostic>, Vec<(String, Span, bool)>) {
    let prelude: BTreeMap<String, String> = prelude.collect();
    let mut imports = prelude.clone();
    let mut globals: BTreeSet<String> = prelude.keys().cloned().collect();
    for item in &module.items {
        match &item.kind {
            ItemKind::Function { name, .. }
            | ItemKind::Type { name, .. }
            | ItemKind::Interface { name, .. } => {
                globals.insert(name.clone());
            }
            ItemKind::Use { path, alias, .. } => {
                if path.len() == 1 {
                    continue;
                }
                if let Some(name) = alias.as_ref().or(path.last()) {
                    globals.insert(name.clone());
                    imports.insert(name.clone(), path.join("::"));
                }
            }
            ItemKind::Extension { .. } | ItemKind::InherentExtension { .. } => {}
        }
    }
    let mut types: BTreeSet<String> = [
        "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "Bool", "String",
        "string", "Char",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    if allow_self_type {
        types.insert("Self".to_owned());
    }
    types.extend(prelude.keys().cloned());
    let mut variants = BTreeMap::new();
    let mut aliases = BTreeMap::new();
    for item in &module.items {
        match &item.kind {
            ItemKind::Type {
                name, definition, ..
            } => {
                types.insert(name.clone());
                if let TypeDefinition::Alias(target) = definition {
                    aliases.insert(name.clone(), target);
                }
                if let TypeDefinition::Enum(v) = definition {
                    variants.insert(
                        name.clone(),
                        v.iter().map(|v| v.name.clone()).collect::<BTreeSet<_>>(),
                    );
                }
            }
            ItemKind::Interface { name, .. } => {
                types.insert(name.clone());
            }
            // Imported annotation targets are verified after graph loading.
            ItemKind::Use { path, alias, .. } => {
                if path.len() == 1 {
                    continue;
                }
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
        aliases,
        generic_types: Vec::new(),
        scopes: vec![globals],
        diagnostics: vec![],
        qualified: vec![],
    };
    for item in &module.items {
        if let ItemKind::Function {
            generic_parameters,
            bounds,
            parameters,
            body,
            result,
            ..
        } = &item.kind
        {
            checker.generic_types.push(
                generic_parameters
                    .iter()
                    .filter(|parameter| {
                        matches!(parameter.kind, memobits_syntax::GenericParameterKind::Type)
                    })
                    .map(|parameter| parameter.name.clone())
                    .collect(),
            );
            for bound in bounds {
                checker.ty(&bound.interface);
            }
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
            checker.generic_types.pop();
        }
    }
    for item in &module.items {
        if let ItemKind::Type {
            definition,
            base,
            generic_parameters,
            bounds,
            ..
        } = &item.kind
        {
            checker.generic_types.push(
                generic_parameters
                    .iter()
                    .filter(|parameter| {
                        matches!(parameter.kind, memobits_syntax::GenericParameterKind::Type)
                    })
                    .map(|parameter| parameter.name.clone())
                    .collect(),
            );
            for bound in bounds {
                checker.ty(&bound.interface);
            }
            if let Some(base) = base {
                checker.ty(base);
            }
            match definition {
                TypeDefinition::Alias(ty) => checker.ty(ty),
                TypeDefinition::Bodyless => {}
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
            checker.generic_types.pop();
        }
    }
    for item in &module.items {
        let method_owner = match &item.kind {
            ItemKind::Interface { .. } => "interface",
            ItemKind::Extension { .. } | ItemKind::InherentExtension { .. } => "extension",
            _ => continue,
        };
        if let ItemKind::Interface {
            associated_types, ..
        } = &item.kind
        {
            checker
                .generic_types
                .push(associated_types.iter().cloned().collect());
        }
        let (target, interface, methods) = match &item.kind {
            ItemKind::Interface { methods, .. } => (None, None, methods.as_slice()),
            ItemKind::Extension {
                target,
                interface,
                methods,
                ..
            } => (Some(target), Some(interface), methods.as_slice()),
            ItemKind::InherentExtension {
                target, methods, ..
            } => (Some(target), None, methods.as_slice()),
            _ => continue,
        };
        if let Some(target) = target {
            checker.ty(target);
        }
        if let Some(interface) = interface {
            checker.ty(interface);
        }
        let mut names = BTreeSet::new();
        for method in methods {
            if !names.insert(&method.name) {
                checker.error(
                    5,
                    method.span,
                    format!("duplicate {method_owner} method '{}'", method.name),
                );
            }
            checker.scopes.push(BTreeSet::from(["self".to_owned()]));
            for parameter in &method.parameters {
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
            if let Some(result) = &method.result {
                checker.ty(result);
            }
            if let Some(body) = &method.body {
                checker.block(body);
            }
            checker.scopes.pop();
        }
        if matches!(&item.kind, ItemKind::Interface { .. }) {
            checker.generic_types.pop();
        }
    }
    (checker.diagnostics, checker.qualified)
}

struct Checker<'a> {
    types: BTreeSet<String>,
    imports: BTreeMap<String, String>,
    variants: BTreeMap<String, BTreeSet<String>>,
    /// Local `type Name = path;` aliases, followed when a variant path starts
    /// with an alias name.
    aliases: BTreeMap<String, &'a Type>,
    generic_types: Vec<BTreeSet<String>>,
    scopes: Vec<BTreeSet<String>>,
    diagnostics: Vec<Diagnostic>,
    qualified: Vec<(String, Span, bool)>,
}
impl Checker<'_> {
    fn ty(&mut self, ty: &Type) {
        for argument in &ty.arguments {
            match argument {
                TypeArgument::Type(ty) | TypeArgument::Reference { referent: ty, .. } => {
                    self.ty(ty)
                }
                TypeArgument::TupleField { ty, .. } => self.ty(ty),
                TypeArgument::Integer(_) => {}
                TypeArgument::Const(_) => {}
            }
        }
        if ty.path.as_slice() == ["\0tuple"] {
            return;
        }
        if templates::lookup_type(ty).is_some() {
            return;
        }
        if ty.path.len() > 1 {
            if self
                .generic_types
                .iter()
                .any(|parameters| parameters.contains(&ty.path[0]))
            {
                // Projection validity is resolved by type analysis against the
                // unique selected generic interface evidence.
                if ty.path.len() != 2 {
                    self.error(
                        8,
                        ty.span,
                        format!(
                            "nested associated type projection '{}' is not supported",
                            ty.path.join("::")
                        ),
                    );
                }
                return;
            }
            self.qualified.push((ty.path.join("::"), ty.span, true));
        } else if let Some(path) = self.imports.get(&ty.path[0]) {
            self.qualified.push((path.clone(), ty.span, true));
        } else if !self.types.contains(&ty.path[0])
            && !self
                .generic_types
                .iter()
                .any(|parameters| parameters.contains(&ty.path[0]))
        {
            self.error(3, ty.span, format!("unknown type '{}'", ty.path[0]));
        }
    }
    /// A path of two or more segments: a local enum variant (possibly through
    /// local aliases) is checked here, anything else goes to the module loader.
    fn qualified_path(&mut self, path: &[String], span: Span) {
        let mut head = vec![path[0].clone()];
        let mut seen = BTreeSet::new();
        while head.len() == 1 && seen.insert(head[0].clone()) {
            match self.aliases.get(&head[0]) {
                Some(target) => {
                    if templates::lookup_type(target).is_some_and(|template| {
                        matches!(
                            template.id,
                            templates::TemplateId::Bytes | templates::TemplateId::List
                        )
                    }) {
                        self.error(4, span, format!("unknown variant '{}'", path.join("::")));
                        return;
                    }
                    head = target.path.clone();
                }
                None => break,
            }
        }
        let mut full = head;
        full.extend(path[1..].iter().cloned());
        if let [head, _] = full.as_slice() {
            if !self.imports.contains_key(head)
                && templates::lookup(std::slice::from_ref(head))
                    .is_some_and(|template| !template.variants.is_empty())
            {
                // Local aliases expanded to a built-in template have no module to load.
                return;
            }
        }
        if full.len() == 2 && self.variants.contains_key(&full[0]) {
            if !self.variants[&full[0]].contains(&full[1]) {
                self.error(4, span, format!("unknown variant '{}'", path.join("::")));
            }
        } else {
            let expanded = if let Some(import) = self.imports.get(&full[0]) {
                format!("{}::{}", import, full[1..].join("::"))
            } else {
                full.join("::")
            };
            self.qualified.push((expanded, span, false));
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
                StatementKind::Destructure {
                    path,
                    fields,
                    value,
                    ..
                } => {
                    self.ty(&Type {
                        span: statement.span,
                        path: path.clone(),
                        arguments: Vec::new(),
                    });
                    self.expr(value);
                    for field in fields {
                        self.scopes
                            .last_mut()
                            .unwrap()
                            .insert(field.binding.clone());
                    }
                }
                StatementKind::Assign { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                StatementKind::Expression(e) => self.expr(e),
                StatementKind::Return(Some(e)) => self.expr(e),
                StatementKind::Loop(b) => self.block(b),
                StatementKind::ForEach {
                    binding,
                    items,
                    body,
                } => {
                    self.expr(items);
                    self.scopes.push(BTreeSet::from([binding.clone()]));
                    self.block(body);
                    self.scopes.pop();
                }
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
                if !self.scopes.iter().rev().any(|s| s.contains(&path[0]))
                    && templates::variant(&path[0]).is_none()
                {
                    self.error(1, expr.span, format!("unknown name '{}'", path[0]));
                }
            }
            ExprKind::Path(path) => self.qualified_path(path, expr.span),
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
            ExprKind::Call {
                callee,
                arguments,
                interface,
            } => {
                // An unbound `drop` is a built-in only in call position.
                if !matches!(&callee.kind, ExprKind::Path(path) if path.as_slice() == ["drop"]
                    && !self.scopes.iter().rev().any(|scope| scope.contains("drop")))
                {
                    self.expr(callee);
                }
                for arg in arguments {
                    self.expr(arg);
                }
                if let Some(interface) = interface {
                    self.ty(interface);
                }
            }
            ExprKind::Field { base, .. } => self.expr(base),
            ExprKind::Struct {
                path,
                type_arguments,
                fields,
            } => {
                // The literal names a type: resolve it like a type annotation.
                self.ty(&Type {
                    span: expr.span,
                    path: path.clone(),
                    arguments: type_arguments.clone(),
                });
                for field in fields {
                    self.expr(&field.value);
                }
            }
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
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.scopes.push(BTreeSet::new());
                    if let PatternKind::Variant { path, slots } = &arm.pattern.kind {
                        if path.len() > 1 {
                            self.qualified_path(path, arm.pattern.span);
                        }
                        for slot in slots {
                            if let Some(name) = &slot.name {
                                self.scopes.last_mut().unwrap().insert(name.clone());
                            }
                        }
                    }
                    self.expr(&arm.body);
                    self.scopes.pop();
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
            let (errors, _) = check(&parsed.module, std::iter::empty(), false);
            assert_eq!(errors.len(), 1);
            assert_eq!(errors[0].code.to_string(), code);
            assert_eq!(errors[0].span.unwrap().start, source.rfind(member).unwrap());
        }
    }
}

#[cfg(test)]
mod alias_variant_tests {
    use super::*;
    use memobits_diagnostics::SourceId;

    fn run(source: &str) -> (Vec<Diagnostic>, Vec<(String, Span, bool)>) {
        let parsed = memobits_syntax::parse(SourceId(0), source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        check(&parsed.module, std::iter::empty(), false)
    }

    #[test]
    fn aliases_of_local_enums_resolve_variant_paths_in_expressions_and_patterns() {
        let (diagnostics, qualified) = run(
            "type Shape [ Empty, Circle(f64) ] type S = Shape; type T = S; \
             fn f(s: S) -> f64 { let a := T::Circle(1.0); let b := S::Empty; \
             match s { S::Empty => 0.0, T::Circle(r) => r } }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert!(qualified.is_empty(), "{qualified:?}");
    }

    #[test]
    fn an_unknown_variant_through_an_alias_is_ne004() {
        let (diagnostics, _) = run("type Shape [ Empty ] type S = Shape; \
             fn f(s: S) -> i32 { let a := S::Missing; match s { S::Gone => 0, _ => 1 } }");
        let codes: Vec<String> = diagnostics.iter().map(|d| d.code.to_string()).collect();
        assert_eq!(codes, ["NE004", "NE004"], "{diagnostics:?}");
    }

    #[test]
    fn an_alias_of_an_imported_enum_is_checked_by_the_module_loader() {
        let (diagnostics, qualified) =
            run("type S = shapes::Shape; fn f() { let a := S::Circle(1.0); }");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert!(
            qualified
                .iter()
                .any(|(path, _, _)| path == "shapes::Shape::Circle"),
            "{qualified:?}"
        );
    }

    #[test]
    fn pattern_bindings_are_scoped_to_their_arm() {
        let (diagnostics, _) =
            run("type E [ A(i32), B ] fn f(e: E) -> i32 { match e { E::A(n) => n, E::B => n } }");
        let codes: Vec<String> = diagnostics.iter().map(|d| d.code.to_string()).collect();
        assert_eq!(codes, ["NE001"], "{diagnostics:?}");
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
        let (diagnostics, _) = check(&parsed.module, std::iter::empty(), false);
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
        let (diagnostics, qualified) = check(&parsed.module, std::iter::empty(), false);
        assert!(diagnostics.is_empty());
        assert_eq!(qualified.len(), 1);
        assert_eq!(qualified[0].0, "self::model::Value");
        assert!(qualified[0].2);
    }
}
