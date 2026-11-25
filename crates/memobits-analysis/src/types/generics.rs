//! Generic functions: inference of type and const arguments from call
//! arguments (or an expected function type), per-bound evidence selection and
//! the specialization request shared by calls and function values.
use super::*;
use memobits_syntax::templates::TemplateId;
use memobits_syntax::TypeArgument;

/// The declared type and const parameter names of a generic function.
pub(super) struct ParameterSet {
    types: HashSet<String>,
    consts: HashSet<String>,
}

/// The type and const arguments known so far.
#[derive(Clone, Default)]
pub(super) struct Bindings {
    types: HashMap<String, Ty>,
    consts: HashMap<String, u32>,
}

pub(super) fn parameter_set(template: &GenericFunctionTemplate) -> ParameterSet {
    let mut set = ParameterSet {
        types: HashSet::new(),
        consts: HashSet::new(),
    };
    for parameter in &template.generic_parameters {
        match parameter.kind {
            GenericParameterKind::Type => set.types.insert(parameter.name.clone()),
            GenericParameterKind::Const(_) => set.consts.insert(parameter.name.clone()),
        };
    }
    set
}

/// Structural validity of a generic function declaration: the only checks that
/// do not depend on a concrete specialization.
pub(super) fn validate_template(template: &GenericFunctionTemplate) -> Result<(), String> {
    let set = parameter_set(template);
    let mut seen = HashSet::new();
    for parameter in &template.generic_parameters {
        if !seen.insert(parameter.name.as_str()) {
            return Err(format!(
                "generic parameter '{}' is declared more than once",
                parameter.name
            ));
        }
        if let GenericParameterKind::Const(ty) = &parameter.kind {
            if ty.path != ["u32"] || !ty.arguments.is_empty() {
                return Err(format!(
                    "const parameter '{}' must have type u32",
                    parameter.name
                ));
            }
        }
    }
    for bound in &template.bounds {
        if !set.types.contains(&bound.parameter) {
            return Err(format!(
                "bound '{}: ...' names '{}', which is not a type parameter of '{}'",
                bound.parameter, bound.parameter, template.name
            ));
        }
        if !bound.interface.arguments.is_empty() {
            return Err("interface bounds with type arguments are not supported".into());
        }
    }
    Ok(())
}

fn names_in(ty: &Type, out: &mut Vec<String>) {
    if let Some(first) = ty.path.first() {
        if !first.starts_with('\0') {
            out.push(first.clone());
        }
    }
    for argument in &ty.arguments {
        match argument {
            TypeArgument::Type(ty) => names_in(ty, out),
            TypeArgument::TupleField { ty, .. } => names_in(ty, out),
            TypeArgument::Reference { referent, .. } => names_in(referent, out),
            TypeArgument::Const(name) => out.push(name.clone()),
            TypeArgument::Integer(_) => {}
        }
    }
}

fn mentions_parameters(ty: &Type, set: &ParameterSet) -> bool {
    let mut names = Vec::new();
    names_in(ty, &mut names);
    names
        .iter()
        .any(|name| set.types.contains(name) || set.consts.contains(name))
}

fn has_unbound(ty: &Type, set: &ParameterSet, bindings: &Bindings) -> bool {
    let mut names = Vec::new();
    names_in(ty, &mut names);
    names.iter().any(|name| {
        (set.types.contains(name) && !bindings.types.contains_key(name))
            || (set.consts.contains(name) && !bindings.consts.contains_key(name))
    })
}

fn has_projection(ty: &Type, set: &ParameterSet) -> bool {
    (ty.path.len() >= 2 && set.types.contains(&ty.path[0]))
        || ty.arguments.iter().any(|argument| match argument {
            TypeArgument::Type(ty) => has_projection(ty, set),
            TypeArgument::TupleField { ty, .. } => has_projection(ty, set),
            TypeArgument::Reference { referent, .. } => has_projection(referent, set),
            _ => false,
        })
}

fn strip_reference(ty: &Ty) -> &Ty {
    match ty {
        Ty::Reference { inner, .. } => inner,
        other => other,
    }
}

fn is_function_literal(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::Function(_))
}

impl Checker {
    fn bind_const(
        &self,
        name: &str,
        value: u32,
        set: &ParameterSet,
        bindings: &mut Bindings,
    ) -> bool {
        if !set.consts.contains(name) {
            return true;
        }
        match bindings.consts.get(name) {
            Some(previous) => *previous == value,
            None => {
                bindings.consts.insert(name.to_owned(), value);
                true
            }
        }
    }

    fn unify_argument(
        &self,
        module: &str,
        pattern: &TypeArgument,
        actual: &ResolvedArgument,
        set: &ParameterSet,
        bindings: &mut Bindings,
    ) -> bool {
        match (pattern, actual) {
            (TypeArgument::Type(ty), ResolvedArgument::Type(actual)) => {
                self.unify(module, ty, actual, set, bindings)
            }
            (TypeArgument::Type(ty), ResolvedArgument::Integer(value))
                if ty.path.len() == 1 && ty.arguments.is_empty() =>
            {
                self.bind_const(&ty.path[0], *value, set, bindings)
            }
            (TypeArgument::Const(name), ResolvedArgument::Integer(value)) => {
                self.bind_const(name, *value, set, bindings)
            }
            (TypeArgument::Integer(_), ResolvedArgument::Integer(_)) => true,
            _ => false,
        }
    }

    /// Matches a written parameter type against a concrete type, binding the
    /// declared type and const parameters it mentions. A type that mentions
    /// none is checked later against the specialized signature; associated
    /// projections are resolved from evidence and also left to that check.
    pub(super) fn unify(
        &self,
        module: &str,
        pattern: &Type,
        actual: &Ty,
        set: &ParameterSet,
        bindings: &mut Bindings,
    ) -> bool {
        if matches!(actual, Ty::Error | Ty::Never) || !mentions_parameters(pattern, set) {
            return true;
        }
        if pattern.path.len() >= 2 && set.types.contains(&pattern.path[0]) {
            return true;
        }
        if pattern.path.len() == 1 && pattern.arguments.is_empty() {
            if set.types.contains(&pattern.path[0]) {
                return infer_direct_type_parameter(
                    &set.types,
                    pattern,
                    actual,
                    &mut bindings.types,
                )
                .is_ok();
            }
            return true;
        }
        if pattern.path.first().is_some_and(|part| part == "\0fn") {
            let Ty::Function(parameters, result, _) = actual else {
                return false;
            };
            let Some((TypeArgument::Type(written_result), written)) =
                pattern.arguments.split_last()
            else {
                return false;
            };
            if written.len() != parameters.len() {
                return false;
            }
            for (written, parameter) in written.iter().zip(parameters) {
                let (access, ty) = match written {
                    TypeArgument::Type(ty) => (IrAccess::Owned, ty),
                    TypeArgument::Reference {
                        access, referent, ..
                    } => (ir_access(*access), referent),
                    _ => return false,
                };
                if access != parameter.access
                    || !self.unify(module, ty, &parameter.ty, set, bindings)
                {
                    return false;
                }
            }
            return self.unify(module, written_result, result, set, bindings);
        }
        if pattern.path.as_slice() == ["\0tuple"] {
            let Ty::Tuple(id, _, _) = actual else {
                return false;
            };
            let info = self.table.info(*id);
            if info.fields.len() != pattern.arguments.len() {
                return false;
            }
            for (written, field) in pattern.arguments.iter().zip(&info.fields) {
                let ty = match written {
                    TypeArgument::Type(ty) => ty,
                    TypeArgument::TupleField { ty, .. } => ty.as_ref(),
                    _ => return false,
                };
                if !self.unify(module, ty, &field.ty, set, bindings) {
                    return false;
                }
            }
            return true;
        }
        if let Some(template) = registry::lookup_type(pattern) {
            match (template.id, actual) {
                (TemplateId::Array, Ty::Array(element, length)) => {
                    let [first, second] = pattern.arguments.as_slice() else {
                        return false;
                    };
                    return self.unify_argument(
                        module,
                        first,
                        &ResolvedArgument::Type(element.as_ref().clone()),
                        set,
                        bindings,
                    ) && self.unify_argument(
                        module,
                        second,
                        &ResolvedArgument::Integer(*length),
                        set,
                        bindings,
                    );
                }
                (TemplateId::List, Ty::List(element)) => {
                    let [first] = pattern.arguments.as_slice() else {
                        return false;
                    };
                    return self.unify_argument(
                        module,
                        first,
                        &ResolvedArgument::Type(element.as_ref().clone()),
                        set,
                        bindings,
                    );
                }
                (TemplateId::Option | TemplateId::Result, Ty::Enum(id, _)) => {
                    let Some((found, arguments)) = self.table.template_arguments(*id) else {
                        return false;
                    };
                    if found != template.id || arguments.len() != pattern.arguments.len() {
                        return false;
                    }
                    return pattern
                        .arguments
                        .iter()
                        .zip(&arguments)
                        .all(|(written, actual)| {
                            self.unify_argument(module, written, actual, set, bindings)
                        });
                }
                _ => return false,
            }
        }
        // A generic nominal type, `Wrap<T, N>`.
        let (Ty::Struct(id, _) | Ty::Enum(id, _)) = actual else {
            return false;
        };
        let (Some(key), Some(origin), Some(arguments)) = (
            self.table.generic_definition_key(module, pattern),
            self.table.generic_origin(*id),
            self.table.generic_arguments(*id),
        ) else {
            return false;
        };
        if key != origin || arguments.len() != pattern.arguments.len() {
            return false;
        }
        pattern
            .arguments
            .iter()
            .zip(&arguments)
            .all(|(written, actual)| self.unify_argument(module, written, actual, set, bindings))
    }

    /// Resolves a type written in the template's module under the given
    /// arguments and evidence.
    fn resolve_declared(
        &mut self,
        template: &GenericFunctionTemplate,
        ty: &Type,
        bindings: &Bindings,
        evidence: &[GenericEvidence],
    ) -> Ty {
        let types = std::mem::replace(&mut self.generic_types, bindings.types.clone());
        let consts = std::mem::replace(&mut self.generic_consts, bindings.consts.clone());
        let held = std::mem::replace(&mut self.generic_evidence, evidence.to_vec());
        let module = std::mem::replace(&mut self.module, template.module.clone());
        let resolved = self.type_path(ty);
        self.module = module;
        self.generic_evidence = held;
        self.generic_consts = consts;
        self.generic_types = types;
        resolved
    }

    /// Resolves a parameter type that may still mention unbound parameters: a
    /// function type keeps `Ty::Error` for an unbound result (the closure's own
    /// result then decides it).
    fn resolve_partial(
        &mut self,
        template: &GenericFunctionTemplate,
        ty: &Type,
        set: &ParameterSet,
        bindings: &Bindings,
        evidence: &[GenericEvidence],
    ) -> Option<Ty> {
        if !has_unbound(ty, set, bindings) {
            return Some(self.resolve_declared(template, ty, bindings, evidence));
        }
        if ty.path.first().is_none_or(|part| part != "\0fn") {
            return None;
        }
        let (TypeArgument::Type(result), written) = ty.arguments.split_last()? else {
            return None;
        };
        let mut parameters = Vec::new();
        for parameter in written {
            let (access, ty) = match parameter {
                TypeArgument::Type(ty) => (IrAccess::Owned, ty),
                TypeArgument::Reference {
                    access, referent, ..
                } => (ir_access(*access), referent),
                _ => return None,
            };
            let resolved = self
                .resolve_partial(template, ty, set, bindings, evidence)
                .unwrap_or(Ty::Error);
            parameters.push(FunctionParameter {
                access,
                ty: resolved,
            });
        }
        let result = self
            .resolve_partial(template, result, set, bindings, evidence)
            .unwrap_or(Ty::Error);
        Some(Ty::Function(
            parameters,
            Box::new(result),
            ty.path.len() > 1,
        ))
    }

    /// Selects the evidence of every bound whose parameter is bound and not yet
    /// selected: the evidence forwarded by the enclosing generic function, else
    /// the one visible implementation. Returns false after reporting an error.
    fn select_evidence(
        &mut self,
        template: &GenericFunctionTemplate,
        bindings: &Bindings,
        selected: &mut Vec<GenericEvidence>,
        span: Span,
    ) -> bool {
        for (index, bound) in template.bounds.iter().enumerate() {
            let interface = &template.bound_interfaces[index];
            if selected
                .iter()
                .any(|found| found.parameter == bound.parameter && found.interface == *interface)
            {
                continue;
            }
            let Some(target) = bindings.types.get(&bound.parameter).cloned() else {
                continue;
            };
            let forwarded = self
                .generic_evidence
                .iter()
                .find(|evidence| {
                    evidence.interface == *interface && evidence.candidate.target == target
                })
                .map(|evidence| evidence.candidate.clone());
            let candidate = if let Some(candidate) = forwarded {
                candidate
            } else {
                let matching = self
                    .extension_candidates
                    .iter()
                    .filter(|candidate| {
                        candidate.visible
                            && candidate.target == target
                            && candidate.interface.as_deref() == Some(interface.as_str())
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                if matching.is_empty() {
                    self.error(
                        7,
                        span,
                        format!(
                            "no visible implementation of '{interface}' for {} satisfies generic bound '{}: {interface}' of '{}'",
                            name(&target),
                            bound.parameter,
                            template.name
                        ),
                    );
                    return false;
                }
                if matching.len() > 1 {
                    let locations = matching
                        .iter()
                        .map(|candidate| {
                            format!(
                                "{}:{}..{}",
                                candidate.module, candidate.span.start, candidate.span.end
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    self.error(
                        7,
                        span,
                        format!(
                            "ambiguous generic evidence for bound '{}: {interface}'; candidates: {locations}",
                            bound.parameter
                        ),
                    );
                    return false;
                }
                matching[0].clone()
            };
            selected.push(GenericEvidence {
                parameter: bound.parameter.clone(),
                interface: interface.clone(),
                candidate,
            });
        }
        true
    }

    /// Builds the specialization for fully known arguments and registers it
    /// (or finds the existing one with the same key).
    #[allow(clippy::too_many_arguments)]
    fn register_specialization(
        &mut self,
        template: &GenericFunctionTemplate,
        bindings: &Bindings,
        evidence: Vec<GenericEvidence>,
        parameter_types: Vec<FunctionParameter>,
        result: Ty,
        span: Span,
    ) -> Option<(FunctionId, Ty)> {
        let function_ty = Ty::Function(parameter_types, Box::new(result), false);
        let Some(IrType::Function(signature)) = super::ir_scalar_function(&function_ty) else {
            self.error(
                7,
                span,
                "generic specialization has a type outside the executable function subset",
            );
            return None;
        };
        let evidence_key = evidence
            .iter()
            .map(|evidence| {
                format!(
                    "{}:{}@{}..{}",
                    evidence.parameter,
                    evidence.candidate.module,
                    evidence.candidate.span.start,
                    evidence.candidate.span.end
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let mut types = bindings
            .types
            .iter()
            .map(|(name, ty)| format!("{name}={ty:?}"))
            .collect::<Vec<_>>();
        types.sort();
        let mut consts = bindings
            .consts
            .iter()
            .map(|(name, value)| format!("{name}={value}"))
            .collect::<Vec<_>>();
        consts.sort();
        let key = format!(
            "{}::{}@{}..{}<{function_ty:?}>[{evidence_key}]{{{}|{}}}",
            template.module,
            template.name,
            template.span.start,
            template.span.end,
            types.join(","),
            consts.join(",")
        );
        let registry = self
            .specialization_registry
            .as_ref()
            .expect("generic specialization registry is present")
            .clone();
        let mut registry = registry.borrow_mut();
        let id = if let Some(id) = registry.by_key.get(&key).copied() {
            id
        } else {
            let id = FunctionId(registry.next_id);
            registry.next_id += 1;
            registry.by_key.insert(key.clone(), id);
            registry.requests.push(GenericSpecialization {
                template: template.clone(),
                substitution: bindings.types.clone(),
                const_substitution: bindings.consts.clone(),
                evidence,
                signature,
                id,
                key,
            });
            id
        };
        Some((id, function_ty))
    }

    /// Reports the parameters no argument fixed.
    fn report_uninferred(
        &mut self,
        template: &GenericFunctionTemplate,
        bindings: &Bindings,
        span: Span,
        how: &str,
    ) -> bool {
        for parameter in &template.generic_parameters {
            let known = match parameter.kind {
                GenericParameterKind::Type => bindings.types.contains_key(&parameter.name),
                GenericParameterKind::Const(_) => bindings.consts.contains_key(&parameter.name),
            };
            if !known && how == "from a diverging argument" {
                self.error(
                    2,
                    span,
                    format!(
                        "cannot infer the generic function type from a diverging argument without an expected result type (type argument '{}' of '{}')",
                        parameter.name, template.name
                    ),
                );
                return false;
            }
            if !known {
                self.error(
                    2,
                    span,
                    format!(
                        "cannot infer {} argument '{}' of generic function '{}' {how}",
                        match parameter.kind {
                            GenericParameterKind::Type => "the type",
                            GenericParameterKind::Const(_) => "the const",
                        },
                        parameter.name,
                        template.name
                    ),
                );
                return false;
            }
        }
        true
    }

    fn finish_specialization(
        &mut self,
        template: &GenericFunctionTemplate,
        set: &ParameterSet,
        bindings: &Bindings,
        mut selected: Vec<GenericEvidence>,
        span: Span,
    ) -> Option<(Vec<FunctionParameter>, Ty, Vec<GenericEvidence>)> {
        let _ = set;
        if !self.select_evidence(template, bindings, &mut selected, span) {
            return None;
        }
        // Evidence in bound order, so the key does not depend on discovery order.
        let ordered = template
            .bounds
            .iter()
            .enumerate()
            .filter_map(|(index, bound)| {
                selected
                    .iter()
                    .find(|found| {
                        found.parameter == bound.parameter
                            && found.interface == template.bound_interfaces[index]
                    })
                    .cloned()
            })
            .collect::<Vec<_>>();
        let mut parameter_types = Vec::new();
        for parameter in &template.parameters {
            let ty = self.resolve_declared(template, &parameter.ty, bindings, &ordered);
            parameter_types.push(FunctionParameter {
                access: ir_access(parameter.access),
                ty,
            });
        }
        let result = template
            .result
            .as_ref()
            .map(|result| self.resolve_declared(template, result, bindings, &ordered))
            .unwrap_or(UNIT);
        if result == Ty::Error || parameter_types.iter().any(|p| p.ty == Ty::Error) {
            return None;
        }
        Some((parameter_types, result, ordered))
    }

    /// A bare path naming a generic function (not shadowed by a local).
    fn is_generic_function_value(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Path(path) => {
                (path.len() > 1
                    || (self.lookup(&path[0]).is_none() && !self.functions.contains_key(&path[0])))
                    && self.generic_template_for(path).is_some()
            }
            _ => false,
        }
    }

    pub(super) fn generic_template_for(&self, path: &[String]) -> Option<GenericFunctionTemplate> {
        if path.len() == 1 {
            self.generic_functions.get(&path[0]).cloned()
        } else {
            let expanded = self.imports.get(&path[0]).map_or_else(
                || path.join("::"),
                |target| format!("{}::{}", target, path[1..].join("::")),
            );
            self.generic_functions
                .get(expanded.strip_prefix("self::").unwrap_or(&expanded))
                .cloned()
        }
    }

    /// A call of a generic function: every type and const argument is inferred
    /// from the arguments (in written order, function literals last) and from
    /// the expected result, the evidence of each bound is selected, and the
    /// specialization for the arguments and evidence is requested.
    pub(super) fn generic_identity_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        arguments: &[Expr],
        expected: Option<&Ty>,
    ) -> Ty {
        let ExprKind::Path(path) = &callee.kind else {
            unreachable!("guarded generic function path")
        };
        let Some(template) = self.generic_template_for(path) else {
            return Ty::Error;
        };
        let fail = |this: &mut Self, arguments: &[Expr]| {
            for argument in arguments {
                this.expr(argument, None);
            }
            Ty::Error
        };
        if let Err(message) = validate_template(&template) {
            self.error(
                7,
                template.span,
                format!(
                    "generic function '{}::{}' is invalid: {message}",
                    template.module, template.name
                ),
            );
            return fail(self, arguments);
        }
        if arguments.len() != template.parameters.len() {
            self.error(
                10,
                expr.span,
                format!(
                    "expected {} arguments, found {}",
                    template.parameters.len(),
                    arguments.len()
                ),
            );
            return fail(self, arguments);
        }
        let set = parameter_set(&template);
        let mut bindings = Bindings::default();
        let mut selected: Vec<GenericEvidence> = Vec::new();
        let mut actuals: Vec<Option<(Ty, bool)>> = vec![None; arguments.len()];
        let mut diverges = false;
        let mut failed = false;
        // What the expected result suggests for parameters the arguments may
        // leave to a literal (`let x: u32 = fold(xs, 0, ...)`).
        let mut hints = Bindings::default();
        if let (Some(result), Some(expected)) = (&template.result, expected) {
            let _ = self.unify(&template.module, result, expected, &set, &mut hints);
        }
        // Pass 1 handles ordinary arguments in written order; pass 2 the ones
        // that wait for earlier arguments (projections, function literals).
        for pass in 0..2 {
            for (index, argument) in arguments.iter().enumerate() {
                if actuals[index].is_some() {
                    continue;
                }
                let parameter = &template.parameters[index];
                let unbound = has_unbound(&parameter.ty, &set, &bindings);
                let generic_value = self.is_generic_function_value(argument);
                let literal = is_function_literal(argument) || generic_value;
                let waits = literal || (unbound && has_projection(&parameter.ty, &set));
                if pass == 0 && waits {
                    continue;
                }
                if pass == 1 && waits && unbound && !literal {
                    // Still unresolved after every plain argument.
                    self.error(
                        2,
                        argument.span,
                        format!(
                            "cannot infer the type of this argument of generic function '{}'; its parameter type depends on an associated type of an unfixed type parameter",
                            template.name
                        ),
                    );
                    failed = true;
                    continue;
                }
                if !self.select_evidence(&template, &bindings, &mut selected, expr.span) {
                    return Ty::Error;
                }
                let access = ir_access(parameter.access);
                let hint = (parameter.ty.path.len() == 1 && parameter.ty.arguments.is_empty())
                    .then(|| hints.types.get(&parameter.ty.path[0]).cloned())
                    .flatten();
                let partial =
                    self.resolve_partial(&template, &parameter.ty, &set, &bindings, &selected);
                let (actual, unknown) = match partial {
                    Some(ty) if !unbound || literal => {
                        if literal {
                            if let Ty::Function(params, _, _) = &ty {
                                let describe = if generic_value {
                                    "generic function value"
                                } else {
                                    "function literal"
                                };
                                if params.iter().any(|p| p.ty == Ty::Error) {
                                    self.error(
                                        2,
                                        argument.span,
                                        format!("cannot infer the parameter types of this {describe}: the generic parameters of its function type are not fixed by the other arguments"),
                                    );
                                    failed = true;
                                    actuals[index] = Some((Ty::Error, true));
                                    continue;
                                }
                            }
                        }
                        let param = FunctionParameter { access, ty };
                        let value_hint = if generic_value {
                            Some(param.ty.clone())
                        } else {
                            hint.clone()
                        };
                        let actual = self.check_call_argument_mode(
                            argument,
                            Some(&param),
                            true,
                            unbound,
                            value_hint.as_ref(),
                        );
                        (actual, unbound)
                    }
                    other => {
                        let ty = other.unwrap_or(Ty::Error);
                        let param = FunctionParameter { access, ty };
                        let value_hint = if generic_value {
                            Some(param.ty.clone())
                        } else {
                            hint.clone()
                        };
                        let actual = self.check_call_argument_mode(
                            argument,
                            Some(&param),
                            true,
                            true,
                            value_hint.as_ref(),
                        );
                        (actual, true)
                    }
                };
                diverges |= actual == Ty::Never;
                if actual == Ty::Error {
                    failed = true;
                }
                if unknown
                    && !self.unify(
                        &template.module,
                        &parameter.ty,
                        strip_reference(&actual),
                        &set,
                        &mut bindings,
                    )
                {
                    self.error(
                        2,
                        argument.span,
                        format!(
                            "cannot infer a consistent type for the generic parameter of '{}': found {}",
                            template.name,
                            name(&actual)
                        ),
                    );
                    failed = true;
                }
                actuals[index] = Some((actual, unknown));
            }
        }
        if failed {
            return Ty::Error;
        }
        if let (Some(result), Some(expected)) = (&template.result, expected) {
            if !matches!(expected, Ty::Error | Ty::Never)
                && !self.unify(&template.module, result, expected, &set, &mut bindings)
            {
                // The result check below reports the mismatch.
            }
        }
        let how = if diverges {
            "from a diverging argument"
        } else {
            "from its arguments"
        };
        if !self.report_uninferred(&template, &bindings, expr.span, how) {
            return Ty::Error;
        }
        let Some((parameter_types, result, evidence)) =
            self.finish_specialization(&template, &set, &bindings, selected, expr.span)
        else {
            return Ty::Error;
        };
        for (index, argument) in arguments.iter().enumerate() {
            let Some((actual, true)) = &actuals[index] else {
                continue;
            };
            let parameter = &parameter_types[index];
            if *actual == Ty::Error {
                continue;
            }
            if parameter.access == IrAccess::Owned || matches!(actual, Ty::Function(..)) {
                self.ensure(actual, &parameter.ty, argument.span);
            } else if let Ty::Reference { inner, .. } = actual {
                if !compatible(inner, &parameter.ty) {
                    self.error(
                        2,
                        argument.span,
                        format!(
                            "expected {} {}, found {}",
                            access_name(parameter.access),
                            name(&parameter.ty),
                            name(actual)
                        ),
                    );
                }
            }
        }
        if let Some(expected) = expected {
            self.ensure(&result, expected, expr.span);
        }
        let Some((specialization_id, function_ty)) = self.register_specialization(
            &template,
            &bindings,
            evidence,
            parameter_types,
            result.clone(),
            expr.span,
        ) else {
            return Ty::Error;
        };
        self.generic_path_targets.insert(
            callee as *const Expr as usize,
            (specialization_id, function_ty),
        );
        self.expr(callee, None);
        if diverges {
            Ty::Never
        } else {
            result
        }
    }

    /// A generic function named as a value. Only an expected function type
    /// can fix its type arguments, so the specialization is chosen from it.
    pub(super) fn generic_function_value(
        &mut self,
        expr: &Expr,
        id: Option<ExprId>,
        template: GenericFunctionTemplate,
        expected: Option<&Ty>,
    ) -> Ty {
        let display = format!("{}::{}", template.module, template.name);
        let Some(Ty::Function(expected_parameters, expected_result, _)) = expected else {
            self.error(
                2,
                expr.span,
                format!(
                    "generic function '{}' cannot be used as a value without an expected function type that fixes its type arguments (for example `let f: fn(i32) -> i32 = {};`)",
                    template.name, template.name
                ),
            );
            return Ty::Error;
        };
        if let Err(message) = validate_template(&template) {
            self.error(
                7,
                template.span,
                format!("generic function '{display}' is invalid: {message}"),
            );
            return Ty::Error;
        }
        if expected_parameters.len() != template.parameters.len() {
            self.error(
                10,
                expr.span,
                format!(
                    "generic function '{}' takes {} arguments, but the expected function type has {}",
                    template.name,
                    template.parameters.len(),
                    expected_parameters.len()
                ),
            );
            return Ty::Error;
        }
        let set = parameter_set(&template);
        let mut bindings = Bindings::default();
        let mut consistent = true;
        for (parameter, wanted) in template.parameters.iter().zip(expected_parameters) {
            consistent &= ir_access(parameter.access) == wanted.access
                && self.unify(
                    &template.module,
                    &parameter.ty,
                    &wanted.ty,
                    &set,
                    &mut bindings,
                );
        }
        if let Some(result) = &template.result {
            // A result that disagrees with the expected one is reported below
            // as a mismatch of the whole function type.
            let _ = self.unify(
                &template.module,
                result,
                expected_result,
                &set,
                &mut bindings,
            );
        }
        if !consistent
            || !self.report_uninferred(
                &template,
                &bindings,
                expr.span,
                "from the expected function type",
            )
        {
            if consistent {
                return Ty::Error;
            }
            self.error(
                2,
                expr.span,
                format!(
                    "the expected function type does not fix the type arguments of generic function '{}'",
                    template.name
                ),
            );
            return Ty::Error;
        }
        let Some((parameter_types, result, evidence)) =
            self.finish_specialization(&template, &set, &bindings, Vec::new(), expr.span)
        else {
            return Ty::Error;
        };
        let function_ty = Ty::Function(parameter_types.clone(), Box::new(result.clone()), false);
        let expected_ty = Ty::Function(expected_parameters.clone(), expected_result.clone(), false);
        let open_result = **expected_result == Ty::Error
            && matches!(&function_ty, Ty::Function(found, _, _) if found == expected_parameters);
        if function_ty != expected_ty && !open_result {
            self.error(
                2,
                expr.span,
                format!(
                    "expected {}, found {} (generic function '{}')",
                    name(&expected_ty),
                    name(&function_ty),
                    template.name
                ),
            );
            return Ty::Error;
        }
        let Some((specialization_id, function_ty)) = self.register_specialization(
            &template,
            &bindings,
            evidence,
            parameter_types,
            result,
            expr.span,
        ) else {
            return Ty::Error;
        };
        if let (Some(facts), Some(expression)) = (self.facts.as_mut(), id) {
            facts.path_uses.push(PathUse {
                expression,
                target: PathTarget::Function(specialization_id),
                access: None,
            });
        }
        function_ty
    }

    /// `T::Name` or `T::Interface::Name`: an associated type of the evidence
    /// selected for one of `T`'s bounds. When several bounds of `T` define the
    /// name, the written type must name the interface.
    pub(super) fn associated_projection(&mut self, ty: &Type) -> Ty {
        let parameter = &ty.path[0];
        let written = ty.path.join("::");
        let (interface, associated) = match ty.path.as_slice() {
            [_, associated] => (None, associated),
            [_, interface, associated] => (Some(interface), associated),
            _ => {
                self.error(
                    8,
                    ty.span,
                    format!("nested associated type projection '{written}' is not supported; name an interface bound with `{parameter}::Interface::Name`"),
                );
                return Ty::Error;
            }
        };
        let matches = self
            .generic_evidence
            .iter()
            .filter(|evidence| {
                &evidence.parameter == parameter
                    && evidence.candidate.associated_types.contains_key(associated)
                    && interface.is_none_or(|interface| {
                        evidence.interface.rsplit("::").next() == Some(interface.as_str())
                    })
            })
            .cloned()
            .collect::<Vec<_>>();
        if let Some(interface) = interface {
            let named = self.generic_evidence.iter().any(|evidence| {
                &evidence.parameter == parameter
                    && evidence.interface.rsplit("::").next() == Some(interface.as_str())
            });
            if !named {
                self.error(
                    8,
                    ty.span,
                    format!("nested associated type projection '{written}' is not supported; '{interface}' is not an interface bound of '{parameter}' (only `{parameter}::Name` and `{parameter}::Interface::Name` are)"),
                );
                return Ty::Error;
            }
        }
        match matches.as_slice() {
            [found] => found.candidate.associated_types[associated].clone(),
            [] => {
                self.error(
                    8,
                    ty.span,
                    format!("associated type projection '{written}' is unresolved in this generic context"),
                );
                Ty::Error
            }
            [first, second, ..] => {
                self.error(
                    8,
                    ty.span,
                    format!(
                        "associated type '{associated}' of '{parameter}' is ambiguous: bounds '{parameter}: {}' and '{parameter}: {}' both define it; qualify it as `{parameter}::Interface::{associated}`",
                        first.interface, second.interface
                    ),
                );
                Ty::Error
            }
        }
    }
}
