//! Resolution of the `Self` type name.
//!
//! Inside an `extend` block (inherent, trailing or `extend T of Interface`)
//! `Self` names the extended type, including its generic arguments. It is
//! replaced by the target type right after parsing, so later passes only ever
//! see ordinary type names. Everywhere else `Self` is an error: outside an
//! `extend` block there is nothing to name, and interface declarations do not
//! support it yet.
use crate::{
    Block, Expr, ExprKind, InterfaceMethod, ItemKind, Module, Parameter, Pattern, PatternKind,
    StatementKind, Type, TypeArgument, TypeDefinition,
};
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};

const OUTSIDE: &str = "`Self` is only available inside an `extend` block, where it names the extended type; write the type's name here";
const INTERFACE: &str = "`Self` in interface declarations is not supported yet; write the implementing type in the `extend` block instead";

enum Mode {
    Extend(Type),
    Outside(&'static str),
}

struct Resolver {
    mode: Mode,
    diagnostics: Vec<Diagnostic>,
    /// The module has `use alloc::Box;`: an applied `Box<T>` names the alloc
    /// layer's box, spelled `alloc::Box<T>` from here on.
    box_imported: bool,
}

pub(crate) fn resolve(module: &mut Module, diagnostics: &mut Vec<Diagnostic>) {
    let box_imported = module.items.iter().any(|item| {
        matches!(&item.kind, ItemKind::Use { path, alias: None, .. }
            if path.as_slice() == ["alloc", "Box"])
    });
    for item in &mut module.items {
        let mut resolver = Resolver {
            mode: Mode::Outside(OUTSIDE),
            diagnostics: Vec::new(),
            box_imported,
        };
        match &mut item.kind {
            ItemKind::Function {
                parameters,
                result,
                body,
                bounds,
                ..
            } => {
                resolver.parameters(parameters);
                resolver.optional_type(result);
                for bound in bounds {
                    resolver.ty(&mut bound.interface);
                }
                resolver.block(body);
            }
            ItemKind::Type {
                definition, base, ..
            } => {
                match definition {
                    TypeDefinition::Alias(ty) => resolver.ty(ty),
                    TypeDefinition::Struct(fields) => {
                        for field in fields {
                            resolver.ty(&mut field.ty);
                        }
                    }
                    TypeDefinition::Enum(variants) => {
                        for variant in variants {
                            for ty in &mut variant.payload {
                                resolver.ty(ty);
                            }
                        }
                    }
                    TypeDefinition::Bodyless => {}
                }
                if let Some(base) = base {
                    resolver.ty(base);
                }
            }
            ItemKind::Const { ty, value, .. } => {
                resolver.ty(ty);
                resolver.expr(value);
            }
            ItemKind::Interface { methods, .. } => {
                resolver.mode = Mode::Outside(INTERFACE);
                resolver.methods(methods);
            }
            ItemKind::Extension {
                target,
                interface,
                associated_types,
                methods,
                ..
            } => {
                resolver.ty(target);
                resolver.ty(interface);
                resolver.mode = Mode::Extend(target.clone());
                for binding in associated_types {
                    resolver.optional_type(&mut binding.ty);
                }
                resolver.methods(methods);
            }
            ItemKind::InherentExtension {
                target, methods, ..
            } => {
                resolver.ty(target);
                resolver.mode = Mode::Extend(target.clone());
                resolver.methods(methods);
            }
            ItemKind::Use { .. } => {}
        }
        diagnostics.append(&mut resolver.diagnostics);
    }
}

fn error(span: Span, message: impl Into<String>) -> Diagnostic {
    let mut d = Diagnostic::new(
        DiagnosticCode::new(Category::Syntax, 2).unwrap(),
        Severity::Error,
        message,
    );
    d.span = Some(span);
    d
}

impl Resolver {
    fn fail(&mut self, span: Span, detail: &str) {
        let message = match &self.mode {
            Mode::Outside(message) => (*message).to_owned(),
            Mode::Extend(_) => detail.to_owned(),
        };
        self.diagnostics.push(error(span, message));
    }

    fn methods(&mut self, methods: &mut [InterfaceMethod]) {
        for method in methods {
            self.parameters(&mut method.parameters);
            self.optional_type(&mut method.result);
            if let Some(body) = &mut method.body {
                self.block(body);
            }
        }
    }

    fn parameters(&mut self, parameters: &mut [Parameter]) {
        for parameter in parameters {
            self.ty(&mut parameter.ty);
        }
    }

    fn optional_type(&mut self, ty: &mut Option<Type>) {
        if let Some(ty) = ty {
            self.ty(ty);
        }
    }

    fn ty(&mut self, ty: &mut Type) {
        for argument in &mut ty.arguments {
            match argument {
                TypeArgument::Type(inner) => self.ty(inner),
                TypeArgument::TupleField { ty: inner, .. } => self.ty(inner),
                TypeArgument::Reference { referent, .. } => self.ty(referent),
                TypeArgument::Const(_) | TypeArgument::Integer(_) => {}
            }
        }
        if self.box_imported && ty.path.as_slice() == ["Box"] && !ty.arguments.is_empty() {
            ty.path = vec!["alloc".into(), "Box".into()];
        }
        if ty.path.first().map(String::as_str) != Some("Self") {
            return;
        }
        let Mode::Extend(target) = &self.mode else {
            return self.fail(ty.span, "");
        };
        if ty.path.len() != 1 {
            return self.fail(
                ty.span,
                "`Self::...` is not a type; `Self` names the extended type itself",
            );
        }
        if !ty.arguments.is_empty() {
            return self.fail(
                ty.span,
                "`Self` takes no type arguments; it already carries the extended type's own",
            );
        }
        let span = ty.span;
        *ty = target.clone();
        ty.span = span;
    }

    /// A path in a pattern, struct literal or destructure: `Self` or
    /// `Self::Variant` becomes the target's path.
    fn path(&mut self, span: Span, path: &mut Vec<String>) -> Option<Vec<TypeArgument>> {
        if path.first().map(String::as_str) != Some("Self") {
            return None;
        }
        let Mode::Extend(target) = &self.mode else {
            self.fail(span, "");
            return None;
        };
        let mut resolved = target.path.clone();
        resolved.extend(path.drain(1..));
        *path = resolved;
        Some(target.arguments.clone())
    }

    fn block(&mut self, block: &mut Block) {
        for statement in &mut block.statements {
            match &mut statement.kind {
                StatementKind::Destructure { path, value, .. } => {
                    self.path(statement.span, path);
                    self.expr(value);
                }
                StatementKind::TupleDestructure { value, .. } => self.expr(value),
                StatementKind::Binding {
                    annotation, value, ..
                } => {
                    self.optional_type(annotation);
                    self.expr(value);
                }
                StatementKind::Assign { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                StatementKind::Expression(expr) => self.expr(expr),
                StatementKind::Return(expr) => {
                    if let Some(expr) = expr {
                        self.expr(expr);
                    }
                }
                StatementKind::Loop(body) => self.block(body),
                StatementKind::ForEach { items, body, .. } => {
                    self.expr(items);
                    self.block(body);
                }
                StatementKind::RangeLoop {
                    start, end, body, ..
                } => {
                    self.expr(start);
                    self.expr(end);
                    self.block(body);
                }
                StatementKind::Break | StatementKind::Continue => {}
            }
        }
        if let Some(tail) = &mut block.tail {
            self.expr(tail);
        }
    }

    fn expr(&mut self, expr: &mut Expr) {
        let span = expr.span;
        match &mut expr.kind {
            ExprKind::Array(items) => items.iter_mut().for_each(|item| self.expr(item)),
            ExprKind::Tuple(items) => items.iter_mut().for_each(|item| self.expr(&mut item.value)),
            ExprKind::RepeatArray { value, .. } => self.expr(value),
            ExprKind::Index { base, index } => {
                self.expr(base);
                self.expr(index);
            }
            ExprKind::Number(_)
            | ExprKind::TypedNumber { .. }
            | ExprKind::StringLiteral(_)
            | ExprKind::CharLiteral(_)
            | ExprKind::Bool(_)
            | ExprKind::Interpolation(_) => {}
            ExprKind::Path(path) => {
                if path.first().map(String::as_str) == Some("Self") {
                    if path.len() == 1 {
                        self.fail(span, "`Self` names a type, not a value; use `Self { ... }` or `Self::Variant`");
                    } else {
                        self.path(span, path);
                    }
                }
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
                arguments
                    .iter_mut()
                    .for_each(|argument| self.expr(argument));
                self.optional_type(interface);
            }
            ExprKind::Field { base, .. } => self.expr(base),
            ExprKind::Struct {
                path,
                type_arguments,
                fields,
            } => {
                if let Some(arguments) = self.path(span, path) {
                    if type_arguments.is_empty() {
                        *type_arguments = arguments;
                    } else {
                        self.fail(
                            span,
                            "`Self` takes no type arguments; it already carries the extended type's own",
                        );
                    }
                }
                for argument in type_arguments.iter_mut() {
                    match argument {
                        TypeArgument::Type(inner) => self.ty(inner),
                        TypeArgument::TupleField { ty, .. } => self.ty(ty),
                        TypeArgument::Reference { referent, .. } => self.ty(referent),
                        TypeArgument::Const(_) | TypeArgument::Integer(_) => {}
                    }
                }
                fields
                    .iter_mut()
                    .for_each(|field| self.expr(&mut field.value));
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::Function(function) => {
                for parameter in &mut function.parameters {
                    if let Some(ty) = &mut parameter.ty {
                        self.ty(ty);
                    }
                }
                self.optional_type(&mut function.result);
                self.block(&mut function.body);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition);
                self.block(then_branch);
                if let Some(branch) = else_branch {
                    self.expr(branch);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.pattern(&mut arm.pattern);
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&mut arm.body);
                }
            }
        }
    }

    fn pattern(&mut self, pattern: &mut Pattern) {
        let span = pattern.span;
        match &mut pattern.kind {
            PatternKind::Variant { path, slots } => {
                if path.len() == 1 && path[0] == "Self" {
                    self.fail(
                        span,
                        "`Self` names a type, not a variant; write `Self::Variant`",
                    );
                } else {
                    self.path(span, path);
                }
                slots.iter_mut().for_each(|slot| self.pattern(slot));
            }
            PatternKind::Tuple(items) | PatternKind::Or(items) => {
                items.iter_mut().for_each(|item| self.pattern(item));
            }
            PatternKind::Wildcard
            | PatternKind::Binding(_)
            | PatternKind::Literal(_)
            | PatternKind::Constant { .. } => {}
        }
    }
}
