//! Target-rooted local module loading and import visibility validation.
//! Includes lexical expression-name checking; type checking is a later pass.
mod names;
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, SourceId, Span};
use memobits_project::Project;
use memobits_syntax::{templates, ItemKind, Module, TypeArgument, TypeDefinition};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug)]
pub enum Target {
    Application,
    Library,
}
pub struct SourceModule {
    pub id: SourceId,
    pub path: std::path::PathBuf,
    pub text: String,
    pub syntax: Module,
}
pub struct Resolution {
    pub modules: BTreeMap<String, SourceModule>,
    pub diagnostics: Vec<Diagnostic>,
}
struct Reference {
    from: Option<String>,
    path: String,
    span: Option<Span>,
    public: bool,
    requires_type: bool,
}
fn error(number: u16, message: String, span: Option<Span>) -> Diagnostic {
    let mut d = Diagnostic::new(
        DiagnosticCode::new(Category::Module, number).unwrap(),
        Severity::Error,
        message,
    );
    d.span = span;
    d
}
fn split(path: &str, project: &Project) -> Option<(String, String)> {
    let path = path.strip_prefix("self::").unwrap_or(path);
    // Prefer the longest known module prefix; remaining segments may name an
    // enum variant rather than another module.
    if let Some(module) = project
        .modules
        .iter()
        .filter(|m| {
            path.strip_prefix(&m.name)
                .is_some_and(|tail| tail.starts_with("::"))
        })
        .max_by_key(|m| m.name.len())
    {
        return Some((module.name.clone(), path[module.name.len() + 2..].into()));
    }
    let (module, name) = path.rsplit_once("::")?;
    Some((module.into(), name.into()))
}

/// Follow a variant's type aliases in their defining modules. The references
/// collected from each alias declaration independently check target visibility.
fn variant_exists(
    mut module: String,
    mut name: String,
    variant: &str,
    project: &Project,
    modules: &BTreeMap<String, SourceModule>,
    imports: &BTreeMap<String, BTreeMap<String, String>>,
) -> bool {
    let mut seen = BTreeSet::new();
    loop {
        if !seen.insert((module.clone(), name.clone())) {
            // Analysis diagnoses alias cycles at the declaration.
            return true;
        }
        let Some(source) = modules.get(&module) else {
            return false;
        };
        let definition = source
            .syntax
            .items
            .iter()
            .find_map(|item| match &item.kind {
                ItemKind::Type {
                    name: candidate,
                    definition,
                    ..
                } if candidate == &name => Some(definition),
                _ => None,
            });
        match definition {
            Some(TypeDefinition::Enum(variants)) => {
                return variants.iter().any(|candidate| candidate.name == variant);
            }
            Some(TypeDefinition::Alias(target)) => {
                if let Some(template) = templates::lookup(&target.path) {
                    return template.variant_index(variant).is_some();
                }
                let [head, tail @ ..] = target.path.as_slice() else {
                    return false;
                };
                if tail.is_empty()
                    && source.syntax.items.iter().any(
                        |item| matches!(&item.kind, ItemKind::Type { name, .. } if name == head),
                    )
                {
                    name = head.clone();
                    continue;
                }
                let expanded = match imports[&module].get(head) {
                    Some(path) if tail.is_empty() => path.clone(),
                    Some(path) => format!("{}::{}", path, tail.join("::")),
                    None if tail.is_empty() => return false,
                    None => target.path.join("::"),
                };
                let Some((target_module, target_name)) = split(&expanded, project) else {
                    return false;
                };
                module = target_module;
                name = target_name;
            }
            _ => return false,
        }
    }
}

/// Resolve explicit imports from a target's modules. Binary/source dependency
/// loading are not implemented by this pass yet.
pub fn resolve(project: &Project, target: Target) -> Resolution {
    let mut result = Resolution {
        modules: BTreeMap::new(),
        diagnostics: vec![],
    };
    let mut pending = Vec::new();
    match target {
        Target::Application => match &project.manifest.package.entry {
            Some(entry) => pending.push(Reference {
                from: None,
                path: entry.clone(),
                span: None,
                public: false,
                requires_type: false,
            }),
            None => result.diagnostics.push(error(
                1,
                "application target requires package.entry".into(),
                None,
            )),
        },
        Target::Library => {
            if project.manifest.export.is_empty() {
                result
                    .diagnostics
                    .push(error(1, "library target requires exports".into(), None));
            }
            for path in project.manifest.export.values() {
                pending.push(Reference {
                    from: None,
                    path: path.clone(),
                    span: None,
                    public: true,
                    requires_type: false,
                });
            }
        }
    }
    let mut visited = BTreeSet::new();
    let mut references = Vec::new();
    let mut imports = BTreeMap::new();
    while let Some(reference) = pending.pop() {
        let Some((module, _)) = split(&reference.path, project) else {
            result.diagnostics.push(error(
                2,
                format!("expected a module-qualified definition: {}", reference.path),
                reference.span,
            ));
            continue;
        };
        references.push(reference);
        if !visited.insert(module.clone()) {
            continue;
        }
        let Some(candidate) = project.modules.iter().find(|m| m.name == module) else {
            result.diagnostics.push(error(3, format!("module '{module}' is unavailable (external dependency loading is not implemented)"), None));
            continue;
        };
        let text = match std::fs::read_to_string(&candidate.path) {
            Ok(text) => text,
            Err(e) => {
                result.diagnostics.push(error(
                    4,
                    format!("{}: {e}", candidate.path.display()),
                    None,
                ));
                continue;
            }
        };
        let id = SourceId(
            project
                .modules
                .iter()
                .position(|m| m.name == module)
                .unwrap() as u32,
        );
        let parsed = memobits_syntax::parse(id, &text);
        result.diagnostics.extend(parsed.diagnostics);
        let mut names = BTreeSet::new();
        for item in &parsed.module.items {
            let name = match &item.kind {
                ItemKind::Function { name, .. } | ItemKind::Type { name, .. } => Some(name.clone()),
                ItemKind::Use { path, alias, .. } => {
                    pending.push(Reference {
                        from: Some(module.clone()),
                        path: path.join("::"),
                        span: Some(item.span),
                        public: true,
                        requires_type: false,
                    });
                    alias.clone().or_else(|| path.last().cloned())
                }
            };
            if let Some(name) = name {
                if !names.insert(name.clone()) {
                    result.diagnostics.push(error(
                        5,
                        format!("duplicate module binding '{name}'"),
                        Some(item.span),
                    ));
                }
            }
        }
        for (alias, path) in &project.manifest.prelude {
            if !names.insert(alias.clone()) {
                result.diagnostics.push(error(
                    5,
                    format!("prelude name '{alias}' conflicts with a module binding"),
                    None,
                ));
            }
            pending.push(Reference {
                from: Some(module.clone()),
                path: path.clone(),
                span: None,
                public: true,
                requires_type: false,
            });
        }
        // Public APIs cannot expose module-private local types. Imported type
        // visibility is validated through their references separately.
        let private_types: BTreeSet<&str> = parsed
            .module
            .items
            .iter()
            .filter_map(|item| match &item.kind {
                ItemKind::Type {
                    public: false,
                    name,
                    ..
                } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        let mut type_imports = project.manifest.prelude.clone();
        for item in &parsed.module.items {
            if let ItemKind::Use { path, alias, .. } = &item.kind {
                if let Some(name) = alias.as_ref().or(path.last()) {
                    type_imports.insert(name.clone(), path.join("::"));
                }
            }
        }
        for item in &parsed.module.items {
            let mut exposed = Vec::new();
            match &item.kind {
                ItemKind::Function {
                    public: true,
                    parameters,
                    result,
                    ..
                } => {
                    exposed.extend(parameters.iter().map(|p| &p.ty));
                    exposed.extend(result.iter());
                }
                ItemKind::Type {
                    public: true,
                    definition,
                    ..
                } => match definition {
                    memobits_syntax::TypeDefinition::Alias(ty) => exposed.push(ty),
                    memobits_syntax::TypeDefinition::Struct(fields) => {
                        exposed.extend(fields.iter().filter(|f| f.public).map(|f| &f.ty))
                    }
                    memobits_syntax::TypeDefinition::Enum(variants) => {
                        exposed.extend(variants.iter().flat_map(|v| &v.payload))
                    }
                },
                _ => {}
            }
            while let Some(ty) = exposed.pop() {
                exposed.extend(ty.arguments.iter().filter_map(|argument| match argument {
                    TypeArgument::Type(ty) => Some(ty),
                    TypeArgument::Integer(_) => None,
                }));
                let qualified = if ty.path.len() == 1 {
                    type_imports
                        .get(&ty.path[0])
                        .cloned()
                        .unwrap_or_else(|| ty.path[0].clone())
                } else {
                    ty.path.join("::")
                };
                let local_name = if !qualified.contains("::") {
                    Some(qualified.as_str())
                } else {
                    let normalized = qualified.strip_prefix("self::").unwrap_or(&qualified);
                    normalized
                        .strip_prefix(&format!("{module}::"))
                        .filter(|name| !name.contains("::"))
                };
                if local_name.is_some_and(|name| private_types.contains(name)) {
                    result.diagnostics.push(error(
                        10,
                        format!("public signature exposes private type '{}'", qualified),
                        Some(ty.span),
                    ));
                }
            }
        }
        let (diagnostics, qualified) = names::check(
            &parsed.module,
            project
                .manifest
                .prelude
                .iter()
                .map(|(alias, path)| (alias.clone(), path.clone())),
        );
        result.diagnostics.extend(diagnostics);
        for (path, span, requires_type) in qualified {
            pending.push(Reference {
                from: Some(module.clone()),
                path,
                span: Some(span),
                public: true,
                requires_type,
            });
        }
        imports.insert(module.clone(), type_imports);
        result.modules.insert(
            module,
            SourceModule {
                id,
                path: candidate.path.clone(),
                text,
                syntax: parsed.module,
            },
        );
    }
    for reference in references {
        let (module, name) = split(&reference.path, project).unwrap();
        let Some(source) = result.modules.get(&module) else {
            continue;
        };
        let (definition_name, variant) = name
            .split_once("::")
            .map_or((name.as_str(), None), |(n, v)| (n, Some(v)));
        let declaration = source
            .syntax
            .items
            .iter()
            .find_map(|item| match &item.kind {
                ItemKind::Function {
                    public, name: n, ..
                }
                | ItemKind::Type {
                    public, name: n, ..
                } if n == definition_name => {
                    let is_type = matches!(item.kind, ItemKind::Type { .. });
                    Some((*public, is_type))
                }
                _ => None,
            });
        match declaration {
            None => result.diagnostics.push(error(
                6,
                format!("definition '{}::{name}' does not exist", module),
                reference.span,
            )),
            Some((false, _)) if reference.public && reference.from.as_deref() != Some(&module) => {
                result.diagnostics.push(error(
                    7,
                    format!("definition '{}::{name}' is private", module),
                    reference.span,
                ))
            }
            Some((_, is_type))
                if variant.is_some_and(|variant| {
                    !is_type
                        || !variant_exists(
                            module.clone(),
                            definition_name.to_owned(),
                            variant,
                            project,
                            &result.modules,
                            &imports,
                        )
                }) =>
            {
                result.diagnostics.push(error(
                    6,
                    format!("definition '{}::{name}' does not exist", module),
                    reference.span,
                ))
            }
            Some((_, is_type)) if reference.requires_type && (!is_type || variant.is_some()) => {
                result.diagnostics.push(error(
                    8,
                    format!("definition '{}::{name}' is not a type", module),
                    reference.span,
                ))
            }
            Some((_, is_type))
                if reference.from.is_none()
                    && !reference.public
                    && (is_type || variant.is_some()) =>
            {
                result.diagnostics.push(error(
                    9,
                    "application entry must be a function".into(),
                    reference.span,
                ))
            }
            _ => {}
        }
    }
    result
}
