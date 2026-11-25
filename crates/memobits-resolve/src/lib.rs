//! Target-rooted local module loading and import visibility validation.
//! Includes lexical expression-name checking; type checking is a later pass.
mod consts;
mod names;
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, SourceId, Span};
use memobits_project::Project;
use memobits_syntax::{
    templates, AssociatedTypeBinding, InterfaceMethod, ItemKind, Module, Type, TypeArgument,
    TypeDefinition,
};
use std::collections::{BTreeMap, BTreeSet, HashSet};

#[derive(Clone, Copy, Debug)]
pub enum Target {
    Application,
    Library,
    /// Every project module, including its `test fn` items.
    Test,
}
pub struct SourceModule {
    pub id: SourceId,
    pub path: std::path::PathBuf,
    pub text: String,
    pub syntax: Module,
}
pub struct Resolution {
    pub package: String,
    pub modules: BTreeMap<String, SourceModule>,
    pub diagnostics: Vec<Diagnostic>,
    /// Non-failing warnings from every parsed module (never abort a command).
    pub warnings: Vec<Diagnostic>,
    /// Explicit direct module imports, kept separate from symbol imports and preludes.
    pub module_imports: BTreeMap<String, BTreeSet<String>>,
}
/// One extension declaration visible to a module under IFACE-04.
#[derive(Clone, Debug)]
pub struct ExtensionCandidate {
    pub package: String,
    pub module: String,
    pub public: bool,
    pub span: Span,
    pub target: Type,
    pub interface: Type,
    pub associated_types: Vec<AssociatedTypeBinding>,
    pub methods: Vec<InterfaceMethod>,
}
/// One inherent extension declaration visible to a module.
#[derive(Clone, Debug)]
pub struct InherentExtensionCandidate {
    pub package: String,
    pub module: String,
    pub public: bool,
    pub span: Span,
    pub target: Type,
    pub generic_parameters: Vec<memobits_syntax::GenericParameter>,
    pub methods: Vec<InterfaceMethod>,
}
impl Resolution {
    /// Return extension declarations from every loaded module. Callers still
    /// need to apply direct-edge and visibility rules.
    pub fn all_extension_candidates(&self) -> Vec<ExtensionCandidate> {
        let mut candidates = Vec::new();
        for (declaring_module, source) in &self.modules {
            for item in &source.syntax.items {
                if let ItemKind::Extension {
                    public,
                    target,
                    interface,
                    associated_types,
                    methods,
                } = &item.kind
                {
                    candidates.push(ExtensionCandidate {
                        package: self.package.clone(),
                        module: declaring_module.clone(),
                        public: *public,
                        span: item.span,
                        target: target.clone(),
                        interface: interface.clone(),
                        associated_types: associated_types.clone(),
                        methods: methods.clone(),
                    });
                }
            }
        }
        candidates
    }

    /// Return local extension declarations plus public declarations from
    /// explicitly and directly imported modules. Symbol imports, preludes and
    /// transitive loads do not contribute candidates.
    pub fn extension_candidates(&self, module: &str) -> Vec<ExtensionCandidate> {
        let directly_imported = self.module_imports.get(module);
        self.all_extension_candidates()
            .into_iter()
            .filter(|candidate| {
                candidate.module == module
                    || (candidate.public
                        && directly_imported
                            .is_some_and(|imports| imports.contains(&candidate.module)))
            })
            .collect()
    }

    pub fn all_inherent_extension_candidates(&self) -> Vec<InherentExtensionCandidate> {
        self.modules
            .iter()
            .flat_map(|(module, source)| {
                source.syntax.items.iter().filter_map(|item| {
                    let ItemKind::InherentExtension {
                        public,
                        target,
                        generic_parameters,
                        methods,
                    } = &item.kind
                    else {
                        return None;
                    };
                    Some(InherentExtensionCandidate {
                        package: self.package.clone(),
                        module: module.clone(),
                        public: *public,
                        span: item.span,
                        target: target.clone(),
                        generic_parameters: generic_parameters.clone(),
                        methods: methods.clone(),
                    })
                })
            })
            .collect()
    }

    pub fn inherent_extension_candidates(&self, module: &str) -> Vec<InherentExtensionCandidate> {
        let directly_imported = self.module_imports.get(module);
        self.all_inherent_extension_candidates()
            .into_iter()
            .filter(|candidate| {
                candidate.module == module
                    || (candidate.public
                        && directly_imported
                            .is_some_and(|imports| imports.contains(&candidate.module)))
            })
            .collect()
    }
}
struct Reference {
    from: Option<String>,
    path: String,
    span: Option<Span>,
    public: bool,
    requires_type: bool,
    /// With `requires_type`: a `const` is also accepted (type argument).
    or_const: bool,
    module_only: bool,
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
    if path == "core::ops" {
        return Some(("core::ops".into(), String::new()));
    }
    if path == templates::ALLOC_MODULE {
        return Some((path.into(), String::new()));
    }
    if let Some(name) = path.strip_prefix("alloc::") {
        return Some((templates::ALLOC_MODULE.into(), name.into()));
    }
    if let Some(name) = path.strip_prefix("core::ops::") {
        return Some(("core::ops".into(), name.into()));
    }
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
const CORE_OPS_SOURCE: &str = "pub interface Add { type Rhs; type Output; fn add(self, rhs: Rhs) -> Output; }\npub interface Sub { type Rhs; type Output; fn sub(self, rhs: Rhs) -> Output; }\npub interface Mul { type Rhs; type Output; fn mul(self, rhs: Rhs) -> Output; }\npub interface Div { type Rhs; type Output; fn div(self, rhs: Rhs) -> Output; }\npub interface Rem { type Rhs; type Output; fn rem(self, rhs: Rhs) -> Output; }\npub interface BitAnd { type Rhs; type Output; fn bitand(self, rhs: Rhs) -> Output; }\npub interface BitOr { type Rhs; type Output; fn bitor(self, rhs: Rhs) -> Output; }\npub interface BitXor { type Rhs; type Output; fn bitxor(self, rhs: Rhs) -> Output; }\npub interface Shl { type Rhs; type Output; fn shl(self, rhs: Rhs) -> Output; }\npub interface Shr { type Rhs; type Output; fn shr(self, rhs: Rhs) -> Output; }\npub interface Neg { type Output; fn neg(self) -> Output; }\npub interface PartialEq { type Rhs; fn eq(borrow self, rhs: Rhs) -> bool; }\npub interface PartialOrd { type Rhs; fn lt(borrow self, rhs: Rhs) -> bool; fn le(borrow self, rhs: Rhs) -> bool; fn gt(borrow self, rhs: Rhs) -> bool; fn ge(borrow self, rhs: Rhs) -> bool; }\npub interface AddAssign { type Rhs; fn add_assign(share self, rhs: Rhs); }\npub interface SubAssign { type Rhs; fn sub_assign(share self, rhs: Rhs); }\npub interface MulAssign { type Rhs; fn mul_assign(share self, rhs: Rhs); }\npub interface DivAssign { type Rhs; fn div_assign(share self, rhs: Rhs); }\npub interface RemAssign { type Rhs; fn rem_assign(share self, rhs: Rhs); }\npub interface BitAndAssign { type Rhs; fn bitand_assign(share self, rhs: Rhs); }\npub interface BitOrAssign { type Rhs; fn bitor_assign(share self, rhs: Rhs); }\npub interface BitXorAssign { type Rhs; fn bitxor_assign(share self, rhs: Rhs); }\npub interface ShlAssign { type Rhs; fn shl_assign(share self, rhs: Rhs); }\npub interface ShrAssign { type Rhs; fn shr_assign(share self, rhs: Rhs); }";
fn is_core_module(name: &str) -> bool {
    name == "core::ops"
}
/// Source text of a Rust-owned virtual module. `alloc` declares `List` only so
/// that imports validate; the type itself is compiler-implemented and the
/// module is removed from the resolution once references are checked.
fn virtual_source(name: &str) -> Option<&'static str> {
    match name {
        "core::ops" => Some(CORE_OPS_SOURCE),
        templates::ALLOC_MODULE => Some(ALLOC_SOURCE),
        _ => None,
    }
}
const ALLOC_SOURCE: &str = "pub type List;\npub type Box;";
fn is_project_module(project: &Project, name: &str) -> bool {
    virtual_source(name).is_some() || project.modules.iter().any(|item| item.name == name)
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
            Some(TypeDefinition::Bodyless) => return false,
            Some(TypeDefinition::Enum(variants)) => {
                return variants.iter().any(|candidate| candidate.name == variant);
            }
            Some(TypeDefinition::Alias(target)) => {
                if let Some(template) = templates::lookup_type(target) {
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

/// Fold module-level constants of one standalone module (no imports): evaluate
/// them, inline their uses and drop the const items.
pub fn fold_standalone_constants(module: &mut Module) -> Vec<Diagnostic> {
    let mut modules = [("source".to_owned(), module)];
    consts::fold(&mut modules, &|_| None, &BTreeSet::new())
}

/// Resolve explicit imports from a target's modules. Binary/source dependency
/// loading are not implemented by this pass yet.
pub fn resolve(project: &Project, target: Target) -> Resolution {
    let mut result = Resolution {
        package: project.manifest.package.name.clone(),
        modules: BTreeMap::new(),
        diagnostics: vec![],
        warnings: vec![],
        module_imports: BTreeMap::new(),
    };
    if project
        .modules
        .iter()
        .any(|module| module.name == "core::ops")
    {
        result.diagnostics.push(error(
            11,
            "module path `core::ops` is reserved for the compiler-provided core module".into(),
            None,
        ));
        return result;
    }
    if project
        .modules
        .iter()
        .any(|module| module.name == templates::ALLOC_MODULE)
    {
        result.diagnostics.push(error(
            11,
            "module name `alloc` is reserved for the compiler-provided alloc module".into(),
            None,
        ));
        return result;
    }
    let mut pending = Vec::new();
    match target {
        Target::Application => match &project.manifest.package.entry {
            Some(entry) => pending.push(Reference {
                from: None,
                path: entry.clone(),
                span: None,
                public: false,
                requires_type: false,
                or_const: false,
                module_only: false,
            }),
            None => result.diagnostics.push(error(
                1,
                "application target requires package.entry".into(),
                None,
            )),
        },
        Target::Test => {
            for module in &project.modules {
                pending.push(Reference {
                    from: None,
                    path: module.name.clone(),
                    span: None,
                    public: false,
                    requires_type: false,
                    or_const: false,
                    module_only: true,
                });
            }
        }
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
                    or_const: false,
                    module_only: false,
                });
            }
        }
    }
    let mut visited = BTreeSet::new();
    let mut references = Vec::new();
    let mut imports = BTreeMap::new();
    while let Some(reference) = pending.pop() {
        let module = if reference.module_only {
            if is_project_module(project, &reference.path) {
                Some(reference.path.clone())
            } else {
                None
            }
        } else {
            split(&reference.path, project).map(|(module, _)| module)
        };
        let Some(module) = module else {
            result.diagnostics.push(error(
                2,
                format!("expected a module-qualified definition: {}", reference.path),
                reference.span,
            ));
            continue;
        };
        if module == templates::ALLOC_MODULE && !project.manifest.alloc() {
            result.diagnostics.push(error(
                12,
                "module 'alloc' is unavailable: the project sets `[build] alloc = false`".into(),
                reference.span,
            ));
            continue;
        }
        if reference.module_only {
            if let Some(from) = &reference.from {
                result
                    .module_imports
                    .entry(from.clone())
                    .or_default()
                    .insert(module.clone());
            }
        } else {
            references.push(reference);
        }
        if !visited.insert(module.clone()) {
            continue;
        }
        let text = if let Some(source) = virtual_source(&module) {
            source.to_owned()
        } else if let Some(candidate) = project.modules.iter().find(|m| m.name == module) {
            match std::fs::read_to_string(&candidate.path) {
                Ok(text) => text,
                Err(e) => {
                    result.diagnostics.push(error(
                        4,
                        format!("{}: {e}", candidate.path.display()),
                        None,
                    ));
                    continue;
                }
            }
        } else {
            result.diagnostics.push(error(3, format!("module '{module}' is unavailable (external dependency loading is not implemented)"), None));
            continue;
        };
        let id = SourceId(
            project
                .modules
                .iter()
                .position(|m| m.name == module)
                .unwrap_or(project.modules.len()) as u32,
        );
        let mut parsed = memobits_syntax::parse(id, &text);
        result.diagnostics.extend(parsed.diagnostics);
        result.warnings.extend(parsed.warnings);
        if !matches!(target, Target::Test) {
            // Tests never take part in normal builds or reachability.
            parsed
                .module
                .items
                .retain(|item| !matches!(item.kind, ItemKind::Function { test: true, .. }));
        }
        let mut names = BTreeSet::new();
        for item in &parsed.module.items {
            let name = match &item.kind {
                ItemKind::Function { name, .. }
                | ItemKind::Type { name, .. }
                | ItemKind::Interface { name, .. }
                | ItemKind::Const { name, .. } => Some(name.clone()),
                ItemKind::Extension { .. } | ItemKind::InherentExtension { .. } => None,
                ItemKind::Use { path, alias, .. } => {
                    let module_only = path.join("::") == "core::ops"
                        || (path.len() == 1 && is_project_module(project, &path[0]));
                    pending.push(Reference {
                        from: Some(module.clone()),
                        path: path.join("::"),
                        span: Some(item.span),
                        public: true,
                        requires_type: false,
                        or_const: false,
                        module_only,
                    });
                    (!module_only)
                        .then(|| alias.clone().or_else(|| path.last().cloned()))
                        .flatten()
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
                or_const: false,
                module_only: false,
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
                if path.len() == 1 && is_project_module(project, &path[0]) {
                    continue;
                }
                if let Some(name) = alias.as_ref().or(path.last()) {
                    type_imports.insert(name.clone(), path.join("::"));
                }
            }
        }
        for item in &parsed.module.items {
            let mut exposed = Vec::new();
            let mut exposed_generics = HashSet::new();
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
                    base,
                    ..
                } => {
                    exposed.extend(base.iter());
                    match definition {
                        memobits_syntax::TypeDefinition::Alias(ty) => exposed.push(ty),
                        memobits_syntax::TypeDefinition::Bodyless => {}
                        memobits_syntax::TypeDefinition::Struct(fields) => {
                            exposed.extend(fields.iter().filter(|f| f.public).map(|f| &f.ty))
                        }
                        memobits_syntax::TypeDefinition::Enum(variants) => {
                            exposed.extend(variants.iter().flat_map(|v| &v.payload))
                        }
                    }
                }
                ItemKind::Interface {
                    public: true,
                    methods,
                    ..
                } => {
                    for method in methods {
                        exposed.extend(method.parameters.iter().map(|parameter| &parameter.ty));
                        exposed.extend(method.result.iter());
                    }
                }
                ItemKind::Extension {
                    public: true,
                    target,
                    interface,
                    associated_types: _,
                    methods,
                } => {
                    exposed.push(target);
                    exposed.push(interface);
                    for method in methods {
                        exposed.extend(method.parameters.iter().map(|parameter| &parameter.ty));
                        exposed.extend(method.result.iter());
                    }
                }
                ItemKind::InherentExtension {
                    public: true,
                    target,
                    generic_parameters,
                    methods,
                } => {
                    exposed_generics.extend(generic_parameters.iter().filter_map(|parameter| {
                        matches!(parameter.kind, memobits_syntax::GenericParameterKind::Type)
                            .then(|| parameter.name.as_str())
                    }));
                    exposed.push(target);
                    for method in methods {
                        exposed.extend(method.parameters.iter().map(|parameter| &parameter.ty));
                        exposed.extend(method.result.iter());
                    }
                }
                _ => {}
            }
            while let Some(ty) = exposed.pop() {
                if ty.path.len() == 1 && exposed_generics.contains(ty.path[0].as_str()) {
                    continue;
                }
                exposed.extend(ty.arguments.iter().filter_map(|argument| match argument {
                    TypeArgument::Type(ty) | TypeArgument::Reference { referent: ty, .. } => {
                        Some(ty)
                    }
                    TypeArgument::TupleField { ty, .. } => Some(ty),
                    TypeArgument::Integer(_) => None,
                    TypeArgument::Const(_) => None,
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
            is_core_module(&module),
            project.manifest.alloc(),
        );
        result.diagnostics.extend(diagnostics);
        for (path, span, requires) in qualified {
            pending.push(Reference {
                from: Some(module.clone()),
                path,
                span: Some(span),
                public: true,
                requires_type: requires != names::Requires::Any,
                or_const: requires == names::Requires::TypeOrConst,
                module_only: false,
            });
        }
        imports.insert(module.clone(), type_imports);
        let source_path = project
            .modules
            .iter()
            .find(|candidate| candidate.name == module)
            .map(|candidate| candidate.path.clone())
            .unwrap_or_default();
        result.modules.insert(
            module,
            SourceModule {
                id,
                path: source_path,
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
                // Test functions cannot be named from any source.
                ItemKind::Function { test: true, .. } => None,
                ItemKind::Const {
                    public, name: n, ..
                } if n == definition_name => Some((*public, false, true)),
                ItemKind::Function {
                    public, name: n, ..
                }
                | ItemKind::Type {
                    public, name: n, ..
                }
                | ItemKind::Interface {
                    public, name: n, ..
                } if n == definition_name => {
                    let is_type = matches!(
                        item.kind,
                        ItemKind::Type { .. } | ItemKind::Interface { .. }
                    );
                    Some((*public, is_type, false))
                }
                _ => None,
            });
        match declaration {
            None => result.diagnostics.push(error(
                6,
                format!("definition '{}::{name}' does not exist", module),
                reference.span,
            )),
            Some((false, ..)) if reference.public && reference.from.as_deref() != Some(&module) => {
                result.diagnostics.push(error(
                    7,
                    format!("definition '{}::{name}' is private", module),
                    reference.span,
                ))
            }
            Some((_, is_type, _))
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
            Some((_, _, true)) if reference.requires_type && reference.or_const => {}
            Some((_, is_type, _)) if reference.requires_type && (!is_type || variant.is_some()) => {
                result.diagnostics.push(error(
                    8,
                    format!("definition '{}::{name}' is not a type", module),
                    reference.span,
                ))
            }
            Some((_, _, true)) if reference.from.is_none() => result.diagnostics.push(error(
                9,
                "a const cannot be an application entry or a library export".into(),
                reference.span,
            )),
            Some((_, is_type, _))
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
    {
        let prelude: BTreeSet<String> = project.manifest.prelude.keys().cloned().collect();
        let mut modules: Vec<(String, &mut Module)> = result
            .modules
            .iter_mut()
            .map(|(name, source)| (name.clone(), &mut source.syntax))
            .collect();
        let diagnostics = consts::fold(&mut modules, &|path| split(path, project), &prelude);
        result.diagnostics.extend(diagnostics);
    }
    result.modules.remove(templates::ALLOC_MODULE);
    check_extension_conformance(project, &mut result);
    result
}

fn check_extension_conformance(project: &Project, resolution: &mut Resolution) {
    for (module, source) in &resolution.modules {
        let imports = source
            .syntax
            .items
            .iter()
            .filter_map(|item| match &item.kind {
                ItemKind::Use { path, alias, .. }
                    if !(path.len() == 1
                        && project
                            .modules
                            .iter()
                            .any(|candidate| candidate.name == path[0])) =>
                {
                    alias
                        .as_ref()
                        .or(path.last())
                        .map(|name| (name.clone(), path.join("::")))
                }
                _ => None,
            })
            .chain(
                project
                    .manifest
                    .prelude
                    .iter()
                    .map(|(alias, path)| (alias.clone(), path.clone())),
            )
            .collect::<BTreeMap<_, _>>();
        for item in &source.syntax.items {
            let ItemKind::Extension {
                target,
                interface,
                associated_types,
                methods,
                ..
            } = &item.kind
            else {
                continue;
            };
            let canonical = canonical_type(project, resolution, module, &imports, interface);
            let built_in_interface = interface.path.len() == 1
                && (matches!(
                    interface.path[0].as_str(),
                    "i8" | "i16"
                        | "i32"
                        | "i64"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "f32"
                        | "f64"
                        | "bool"
                        | "string"
                        | "char"
                ) || templates::lookup_type(interface).is_some());
            if built_in_interface {
                resolution.diagnostics.push(error(
                    8,
                    format!(
                        "extension constraint '{}' is not a declared interface",
                        interface.path.join("::")
                    ),
                    Some(interface.span),
                ));
                continue;
            }
            let Some((interface_module, interface_name)) = split(&canonical, project) else {
                resolution.diagnostics.push(error(
                    8,
                    format!(
                        "extension constraint '{}' is not a declared interface",
                        interface.path.join("::")
                    ),
                    Some(interface.span),
                ));
                continue;
            };
            let declaration = resolution
                .modules
                .get(&interface_module)
                .and_then(|source| {
                    source
                        .syntax
                        .items
                        .iter()
                        .find_map(|item| match &item.kind {
                            ItemKind::Interface {
                                name,
                                associated_types: required_associated,
                                methods,
                                public,
                            } if name == &interface_name => {
                                Some((required_associated, methods, *public))
                            }
                            _ => None,
                        })
                });
            let Some((required_associated, required_methods, _)) = declaration else {
                let is_type = resolution
                    .modules
                    .get(&interface_module)
                    .is_some_and(|source| {
                        source.syntax.items.iter().any(|item| {
                            matches!(&item.kind, ItemKind::Type { name, .. } if name == &interface_name)
                        })
                    });
                resolution.diagnostics.push(error(
                    8,
                    if is_type {
                        format!("extension constraint '{interface_module}::{interface_name}' is a type, not an interface")
                    } else {
                        format!("extension constraint '{}' is not a declared interface", interface.path.join("::"))
                    },
                    Some(interface.span),
                ));
                continue;
            };
            let interface_imports = resolution
                .modules
                .get(&interface_module)
                .map(|source| {
                    source
                        .syntax
                        .items
                        .iter()
                        .filter_map(|item| match &item.kind {
                            ItemKind::Use { path, alias, .. } => alias
                                .as_ref()
                                .or(path.last())
                                .map(|name| (name.clone(), path.join("::"))),
                            _ => None,
                        })
                        .collect::<BTreeMap<_, _>>()
                })
                .unwrap_or_default();
            let mut associated_map = BTreeMap::new();
            for binding in associated_types {
                if associated_map.contains_key(&binding.name) {
                    resolution.diagnostics.push(error(
                        5,
                        format!("duplicate associated type binding '{}'", binding.name),
                        Some(binding.span),
                    ));
                    continue;
                }
                if !required_associated.contains(&binding.name) {
                    resolution.diagnostics.push(error(
                        5,
                        format!(
                            "associated type '{}' is not declared by interface '{}::{}'",
                            binding.name, interface_module, interface_name
                        ),
                        Some(binding.span),
                    ));
                    continue;
                }
                if let Some(ty) = &binding.ty {
                    associated_map.insert(
                        binding.name.clone(),
                        canonical_type(project, resolution, module, &imports, ty),
                    );
                }
            }
            for name in required_associated {
                if !associated_map.contains_key(name) {
                    resolution.diagnostics.push(error(
                        5,
                        format!("extension is missing associated type binding '{name}'"),
                        Some(item.span),
                    ));
                }
            }
            for required in required_methods {
                match methods.iter().find(|method| method.name == required.name) {
                    None => resolution.diagnostics.push(error(
                        5,
                        format!("extension is missing interface method '{}'", required.name),
                        Some(item.span),
                    )),
                    Some(actual)
                        if actual.receiver != required.receiver
                            || actual.parameters.len() != required.parameters.len()
                            || actual.parameters.iter().zip(&required.parameters).any(
                                |(left, right)| {
                                    left.access != right.access
                                        || left.mutable != right.mutable
                                        || canonical_type(
                                            project, resolution, module, &imports, &left.ty,
                                        ) != canonical_interface_type(
                                            project,
                                            resolution,
                                            &interface_module,
                                            &interface_imports,
                                            &right.ty,
                                            target,
                                            module,
                                            &imports,
                                            &associated_map,
                                        )
                                },
                            )
                            || actual
                                .result
                                .as_ref()
                                .zip(required.result.as_ref())
                                .is_some_and(|(left, right)| {
                                    canonical_type(project, resolution, module, &imports, left)
                                        != canonical_interface_type(
                                            project,
                                            resolution,
                                            &interface_module,
                                            &interface_imports,
                                            right,
                                            target,
                                            module,
                                            &imports,
                                            &associated_map,
                                        )
                                })
                            || actual.result.is_some() != required.result.is_some() =>
                    {
                        resolution.diagnostics.push(error(
                            5,
                            format!(
                                "extension method '{}' does not match interface '{}::{}' declared here",
                                required.name, interface_module, interface_name
                            ),
                            Some(actual.span),
                        ));
                    }
                    Some(_) => {}
                }
            }
            for extra in methods {
                if !required_methods
                    .iter()
                    .any(|required| required.name == extra.name)
                {
                    resolution.diagnostics.push(error(
                        5,
                        format!(
                            "extension method '{}' is not declared by interface '{}::{}'",
                            extra.name, interface_module, interface_name
                        ),
                        Some(extra.span),
                    ));
                }
            }
        }
    }
}

fn canonical_type(
    project: &Project,
    resolution: &Resolution,
    module: &str,
    imports: &BTreeMap<String, String>,
    ty: &memobits_syntax::Type,
) -> String {
    const BUILTINS: &[&str] = &[
        "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "bool", "string",
        "char",
    ];
    canonical_type_inner(
        project,
        resolution,
        module,
        imports,
        ty,
        &mut BTreeSet::new(),
        BUILTINS,
    )
}

fn canonical_interface_type(
    project: &Project,
    resolution: &Resolution,
    module: &str,
    imports: &BTreeMap<String, String>,
    ty: &memobits_syntax::Type,
    target: &memobits_syntax::Type,
    target_module: &str,
    target_imports: &BTreeMap<String, String>,
    associated: &BTreeMap<String, String>,
) -> String {
    if ty.path.as_slice() == ["Self"] && ty.arguments.is_empty() {
        canonical_type(project, resolution, target_module, target_imports, target)
    } else if ty.path.len() == 1 && ty.arguments.is_empty() {
        associated
            .get(&ty.path[0])
            .cloned()
            .unwrap_or_else(|| canonical_type(project, resolution, module, imports, ty))
    } else {
        canonical_type(project, resolution, module, imports, ty)
    }
}

fn canonical_type_inner(
    project: &Project,
    resolution: &Resolution,
    module: &str,
    imports: &BTreeMap<String, String>,
    ty: &memobits_syntax::Type,
    seen: &mut BTreeSet<String>,
    builtins: &[&str],
) -> String {
    if ty.path.is_empty() {
        return "<invalid-type>".into();
    }
    if ty.path.as_slice() == ["\0tuple"] {
        let elements = ty
            .arguments
            .iter()
            .map(|argument| match argument {
                TypeArgument::Type(element) => canonical_type_inner(
                    project, resolution, module, imports, element, seen, builtins,
                ),
                TypeArgument::TupleField { ty, .. } => {
                    canonical_type_inner(project, resolution, module, imports, ty, seen, builtins)
                }
                _ => "<invalid-tuple-element>".into(),
            })
            .collect::<Vec<_>>();
        return format!("tuple({})", elements.join(","));
    }
    if ty.path.as_slice() == ["\0unit"] {
        return "Unit".into();
    }
    if ty.path.first().is_some_and(|part| part == "\0fn") {
        let parts = ty
            .arguments
            .iter()
            .map(|argument| match argument {
                TypeArgument::Type(element) => canonical_type_inner(
                    project, resolution, module, imports, element, seen, builtins,
                ),
                TypeArgument::Reference {
                    access, referent, ..
                } => format!(
                    "{access:?} {}",
                    canonical_type_inner(
                        project, resolution, module, imports, referent, seen, builtins
                    )
                ),
                _ => "<invalid-function-type>".into(),
            })
            .collect::<Vec<_>>();
        let var = if ty.path.len() > 1 { "var " } else { "" };
        return format!("{var}fn({})", parts.join(","));
    }
    if ty.path.as_slice() == ["\0record"] {
        let mut fields = ty
            .arguments
            .iter()
            .map(|argument| match argument {
                TypeArgument::TupleField {
                    label: Some(label),
                    ty,
                } => (
                    label.clone(),
                    canonical_type_inner(project, resolution, module, imports, ty, seen, builtins),
                ),
                _ => ("<invalid-field>".into(), "<invalid-type>".into()),
            })
            .collect::<Vec<_>>();
        fields.sort_by(|left, right| left.0.cmp(&right.0));
        return format!(
            "record{{{}}}",
            fields
                .into_iter()
                .map(|(label, ty)| format!("{label}:{ty}"))
                .collect::<Vec<_>>()
                .join(",")
        );
    }
    if ty.path.first().is_some_and(|part| part == "\0enum") {
        return format!(
            "anonymous-enum({}:{}:{})",
            ty.span.source.0, ty.span.start, ty.span.end
        );
    }
    let mut path = if ty.path.as_slice() == ["string"] {
        "String".to_owned()
    } else if ty.path.len() == 1
        && (builtins.contains(&ty.path[0].as_str()) || templates::lookup_type(ty).is_some())
    {
        ty.path.join("::")
    } else if let Some(import) = imports.get(&ty.path[0]) {
        if ty.path.len() == 1 {
            import.clone()
        } else {
            format!("{import}::{}", ty.path[1..].join("::"))
        }
    } else if ty.path.len() == 1 {
        format!("{module}::{}", ty.path[0])
    } else {
        ty.path.join("::")
    };
    path = path.strip_prefix("self::").unwrap_or(&path).to_owned();
    let generic_path = if ty.arguments.is_empty() {
        path.clone()
    } else {
        let arguments = ty
            .arguments
            .iter()
            .map(|argument| match argument {
                TypeArgument::Type(ty) => {
                    canonical_type_inner(project, resolution, module, imports, ty, seen, builtins)
                }
                TypeArgument::TupleField { label, ty } => format!(
                    "{}{}",
                    label
                        .as_ref()
                        .map_or_else(String::new, |label| format!("{label}:")),
                    canonical_type_inner(project, resolution, module, imports, ty, seen, builtins)
                ),
                TypeArgument::Reference {
                    access, referent, ..
                } => format!(
                    "{access:?} {}",
                    canonical_type_inner(
                        project, resolution, module, imports, referent, seen, builtins
                    )
                ),
                TypeArgument::Integer(integer) => integer.raw.clone(),
                TypeArgument::Const(name) => name.clone(),
            })
            .collect::<Vec<_>>()
            .join(",");
        format!("{path}<{arguments}>")
    };
    if !ty.arguments.is_empty()
        || builtins.contains(&ty.path[0].as_str())
        || templates::lookup_type(ty).is_some()
    {
        return generic_path;
    }
    let Some((target_module, target_name)) = split(&path, project) else {
        return generic_path;
    };
    let key = format!("{target_module}::{target_name}");
    if !seen.insert(key.clone()) {
        return generic_path;
    }
    let alias = resolution.modules.get(&target_module).and_then(|source| {
        source
            .syntax
            .items
            .iter()
            .find_map(|item| match &item.kind {
                ItemKind::Type {
                    name,
                    definition: TypeDefinition::Alias(target),
                    ..
                } if name == &target_name => Some((
                    syntax_imports(&source.syntax.items, project),
                    target.clone(),
                )),
                _ => None,
            })
    });
    if let Some((alias_imports, target)) = alias {
        let canonical = canonical_type_inner(
            project,
            resolution,
            &target_module,
            &alias_imports,
            &target,
            seen,
            builtins,
        );
        seen.remove(&key);
        return canonical;
    }
    seen.remove(&key);
    generic_path
}

fn syntax_imports(items: &[memobits_syntax::Item], project: &Project) -> BTreeMap<String, String> {
    items
        .iter()
        .filter_map(|item| match &item.kind {
            ItemKind::Use { path, alias, .. }
                if !(path.len() == 1 && project.modules.iter().any(|m| m.name == path[0])) =>
            {
                alias
                    .as_ref()
                    .or(path.last())
                    .map(|name| (name.clone(), path.join("::")))
            }
            _ => None,
        })
        .collect()
}
