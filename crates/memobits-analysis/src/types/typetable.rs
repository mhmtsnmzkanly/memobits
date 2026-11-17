//! Nominal type table shared by every module checked together: struct and enum
//! definitions with canonical identity (`module::Name`), and type aliases
//! resolved to their targets. Structs and enums share one id space.
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use memobits_diagnostics::{Diagnostic, Span};
use memobits_ir::{ErrorAncestry, TypeId};
use memobits_syntax::{Field, ItemKind, Module, Type, TypeDefinition};

use memobits_syntax::templates::{self, ParameterKind, Template, TemplateId};

use super::templates::{resolve_arguments, ResolvedArgument};
use super::{diagnostic, Ty};

#[derive(Clone, Debug)]
pub(super) struct FieldInfo {
    pub name: String,
    pub public: bool,
    pub module: String,
    pub ty: Ty,
    ty_span: Span,
}

impl FieldInfo {
    pub(super) fn visible_in(&self, module: &str) -> bool {
        self.public || self.module == module
    }
}

/// One enum variant: its payload types in declaration order.
#[derive(Clone, Debug)]
pub(super) struct VariantInfo {
    pub name: String,
    pub payload: Vec<Ty>,
}

/// A nominal type: a struct (`fields`) or an enum (`variants`, `is_enum`). The
/// index in `TypeTable::types` is the type's id in the IR type table.
#[derive(Clone, Debug)]
pub(super) struct StructInfo {
    pub name: String,
    pub module: String,
    pub span: Span,
    pub is_enum: bool,
    pub fields: Vec<FieldInfo>,
    pub variants: Vec<VariantInfo>,
}

/// A failed type resolution. The span is the offending type reference, so a
/// caller reports it only if the reference lies inside the type it resolved.
#[derive(Clone, Debug)]
pub(super) struct TypeFailure {
    pub span: Span,
    pub code: u16,
    pub message: String,
}

enum Def {
    /// A struct or enum, by index in `TypeTable::types`.
    Named(u32),
    Alias {
        module: String,
        target: Type,
    },
}

#[derive(Clone)]
enum AliasState {
    Resolving,
    Done(Result<Ty, TypeFailure>),
}

pub(super) struct TypeTable {
    types: Vec<StructInfo>,
    instances: RefCell<Vec<(TemplateId, Vec<ResolvedArgument>, StructInfo)>>,
    defs: HashMap<String, Def>,
    error_parents: HashMap<u32, u32>,
    imports: HashMap<String, HashMap<String, String>>,
    aliases: RefCell<HashMap<String, AliasState>>,
}

fn key(module: &str, name: &str) -> String {
    format!("{module}::{name}")
}

fn normalize(path: &str) -> &str {
    path.strip_prefix("self::").unwrap_or(path)
}

fn within(inner: Span, outer: Span) -> bool {
    inner.source == outer.source && inner.start >= outer.start && inner.end <= outer.end
}

fn primitive(name: &str) -> Option<Ty> {
    Some(Ty::Primitive(match name {
        "i8" => "i8",
        "i16" => "i16",
        "i32" => "i32",
        "i64" => "i64",
        "u8" => "u8",
        "u16" => "u16",
        "u32" => "u32",
        "u64" => "u64",
        "f32" => "f32",
        "f64" => "f64",
        "Bool" => "Bool",
        _ => return None,
    }))
}

impl TypeTable {
    fn error_type(&self, span: Span) -> Ty {
        let mut instances = self.instances.borrow_mut();
        if let Some((index, _)) = instances
            .iter()
            .enumerate()
            .find(|(_, entry)| entry.0 == TemplateId::Error)
        {
            return Ty::Struct((self.types.len() + index) as u32, "Error".into());
        }
        let id = (self.types.len() + instances.len()) as u32;
        instances.push((
            TemplateId::Error,
            Vec::new(),
            StructInfo {
                name: "Error".into(),
                module: "__prelude".into(),
                span,
                is_enum: false,
                fields: vec![FieldInfo {
                    name: "code".into(),
                    public: true,
                    module: "__prelude".into(),
                    ty: Ty::Primitive("u32"),
                    ty_span: span,
                }],
                variants: Vec::new(),
            },
        ));
        Ty::Struct(id, "Error".into())
    }

    pub(super) fn instantiate_enum(
        &self,
        template: &Template,
        arguments: Vec<ResolvedArgument>,
        span: Span,
    ) -> Ty {
        let mut instances = self.instances.borrow_mut();
        if let Some((index, (_, _, info))) = instances
            .iter()
            .enumerate()
            .find(|(_, (id, args, _))| *id == template.id && *args == arguments)
        {
            return Ty::Enum((self.types.len() + index) as u32, info.name.as_str().into());
        }
        let names = arguments
            .iter()
            .map(|argument| match argument {
                ResolvedArgument::Type(ty) => super::name(ty),
                ResolvedArgument::Integer(value) => value.to_string(),
            })
            .collect::<Vec<_>>();
        let name = format!("{}<{}>", template.name, names.join(", "));
        let id = (self.types.len() + instances.len()) as u32;
        let info = StructInfo {
            name: name.clone(),
            module: format!("__prelude::instance{id}"),
            span,
            is_enum: true,
            fields: Vec::new(),
            variants: template
                .variants
                .iter()
                .map(|variant| VariantInfo {
                    name: variant.name.into(),
                    payload: variant
                        .payload
                        .iter()
                        .map(|index| match &arguments[*index] {
                            ResolvedArgument::Type(ty) => ty.clone(),
                            ResolvedArgument::Integer(_) => {
                                unreachable!("enum payload templates require type arguments")
                            }
                        })
                        .collect(),
                })
                .collect(),
        };
        instances.push((template.id, arguments, info));
        Ty::Enum(id, name.into())
    }

    fn instance_template(&self, id: u32) -> Option<TemplateId> {
        let index = (id as usize).checked_sub(self.types.len())?;
        self.instances.borrow().get(index).map(|entry| entry.0)
    }

    pub(super) fn enum_template(&self, id: u32) -> Option<&'static Template> {
        self.instance_template(id).map(templates::by_id)
    }

    fn is_error_type(&self, id: u32) -> bool {
        self.error_parents.contains_key(&id)
            || self.instance_template(id) == Some(TemplateId::Error)
    }

    pub(super) fn error_ancestry(&self, id: u32) -> Option<ErrorAncestry> {
        if let Some(&parent) = self.error_parents.get(&id) {
            Some(ErrorAncestry::Derived(TypeId(parent)))
        } else if self.instance_template(id) == Some(TemplateId::Error) {
            Some(ErrorAncestry::Root)
        } else {
            None
        }
    }

    pub(super) fn has_error_ancestor(&self, actual: &Ty, expected: &Ty) -> bool {
        let (Ty::Struct(mut child, _), Ty::Struct(ancestor, _)) = (actual, expected) else {
            return false;
        };
        while let Some(&parent) = self.error_parents.get(&child) {
            if parent == *ancestor {
                return true;
            }
            child = parent;
        }
        false
    }

    pub(super) fn is_borrow_option(&self, ty: &Ty) -> bool {
        let Ty::Enum(id, _) = ty else { return false };
        let Some(index) = (*id as usize).checked_sub(self.types.len()) else {
            return false;
        };
        matches!(
            self.instances.borrow().get(index),
            Some((TemplateId::Option, args, _))
                if matches!(args.as_slice(), [ResolvedArgument::Type(Ty::Reference { .. })])
        )
    }

    pub(super) fn resolve_local(&self, module: &str, ty: &Type) -> Result<Ty, TypeFailure> {
        if let (
            Some(template),
            [memobits_syntax::TypeArgument::Reference {
                access: memobits_syntax::Access::Borrow,
                referent,
                span,
            }],
        ) = (templates::lookup(&ty.path), ty.arguments.as_slice())
        {
            if template.id == TemplateId::Option {
                let inner = self.resolve(module, referent)?;
                if inner == super::UNIT {
                    return Err(TypeFailure {
                        span: *span,
                        code: 17,
                        message: "Option<borrow T> requires a non-Unit referent".into(),
                    });
                }
                let argument = Ty::Reference {
                    access: memobits_ir::Access::Borrow,
                    inner: Box::new(inner),
                    origin: super::ReferenceOrigin::Temporary,
                };
                return Ok(self.instantiate_enum(
                    template,
                    vec![ResolvedArgument::Type(argument)],
                    ty.span,
                ));
            }
        }
        self.resolve(module, ty)
    }

    pub(super) fn check_template_argument(
        &self,
        template: &Template,
        kind: ParameterKind,
        ty: &Ty,
        span: Span,
    ) -> Result<(), TypeFailure> {
        if self.is_borrow_option(ty) {
            return Err(super::templates::unsupported_reference_argument(
                template, span,
            ));
        }
        if matches!(kind, ParameterKind::ErrorType)
            && !matches!(ty, Ty::Struct(id, _) if self.is_error_type(*id))
        {
            return Err(TypeFailure {
                span,
                code: 2,
                message: format!(
                    "{} requires Error or a type derived from it for its error type argument, found {}",
                    template.name,
                    super::name(ty)
                ),
            });
        }
        Ok(())
    }

    pub fn info(&self, id: u32) -> StructInfo {
        let id = id as usize;
        if id < self.types.len() {
            self.types[id].clone()
        } else {
            self.instances.borrow()[id - self.types.len()].2.clone()
        }
    }

    /// Snapshot all definitions in their ID order for retained IR type facts.
    pub fn definitions(&self) -> Vec<StructInfo> {
        let mut definitions = self.types.clone();
        definitions.extend(self.instances.borrow().iter().map(|entry| entry.2.clone()));
        definitions
    }

    pub fn empty() -> Self {
        Self {
            types: Vec::new(),
            instances: RefCell::new(Vec::new()),
            defs: HashMap::new(),
            error_parents: HashMap::new(),
            imports: HashMap::new(),
            aliases: RefCell::new(HashMap::new()),
        }
    }

    /// Build the table for `modules` (name and syntax). `imports` maps each
    /// module to its local names (use declarations and prelude aliases). Struct
    /// IDs follow module order, then declaration order. Declaration errors
    /// (alias targets, field types, recursion, unsupported field kinds) are
    /// returned once, here.
    pub fn build(
        modules: &[(&str, &Module)],
        imports: HashMap<String, HashMap<String, String>>,
    ) -> (Self, Vec<Diagnostic>) {
        let mut table = Self::empty();
        table.imports = imports;
        let mut diagnostics = Vec::new();
        let mut field_types: Vec<Option<&[Field]>> = Vec::new();
        let mut bases = HashMap::new();
        let mut variant_types: Vec<(usize, &[memobits_syntax::Variant], String)> = Vec::new();
        let mut alias_items = Vec::new();
        for (module, syntax) in modules {
            for item in &syntax.items {
                let ItemKind::Type {
                    name,
                    definition,
                    base,
                    ..
                } = &item.kind
                else {
                    continue;
                };
                if templates::lookup(std::slice::from_ref(name)).is_some() {
                    diagnostics.push(diagnostic(
                        3,
                        item.span,
                        format!("'{}' is reserved for a compiler-known type", name),
                    ));
                }
                let def = match definition {
                    TypeDefinition::Struct(fields) => {
                        let id = table.types.len();
                        table.types.push(StructInfo {
                            name: name.clone(),
                            module: (*module).to_owned(),
                            span: item.span,
                            is_enum: false,
                            fields: Vec::new(),
                            variants: Vec::new(),
                        });
                        field_types.push(Some(fields));
                        if let Some(base) = base {
                            bases.insert(id as u32, base);
                        }
                        Def::Named(id as u32)
                    }
                    TypeDefinition::Alias(target) => {
                        alias_items.push((key(module, name), target));
                        Def::Alias {
                            module: (*module).to_owned(),
                            target: target.clone(),
                        }
                    }
                    TypeDefinition::Enum(variants) => {
                        let id = table.types.len();
                        table.types.push(StructInfo {
                            name: name.clone(),
                            module: (*module).to_owned(),
                            span: item.span,
                            is_enum: true,
                            fields: Vec::new(),
                            variants: Vec::new(),
                        });
                        field_types.push(None);
                        variant_types.push((id, variants, (*module).to_owned()));
                        if variants.is_empty() {
                            diagnostics.push(diagnostic(
                                27,
                                item.span,
                                format!(
                                    "enum '{name}' declares no variants; an enum needs at least one"
                                ),
                            ));
                        }
                        Def::Named(id as u32)
                    }
                };
                if table.defs.insert(key(module, name), def).is_some() {
                    diagnostics.push(diagnostic(
                        14,
                        item.span,
                        format!("duplicate type '{name}'"),
                    ));
                }
            }
        }
        // Establish hierarchy membership before resolving any outcome arguments.
        let derivations = table.check_derivations(&bases, &mut diagnostics);
        // Aliases: resolve each so its own declaration reports its failures.
        for (alias_key, target) in alias_items {
            if let Err(failure) = table.resolve_alias(&alias_key) {
                if within(failure.span, target.span) {
                    diagnostics.push(diagnostic(failure.code, failure.span, failure.message));
                }
            }
        }
        // Ordinary structs first, then valid derivations in base-first order.
        let plain_structs = field_types.iter().enumerate().filter_map(|(id, fields)| {
            fields
                .filter(|_| !table.error_parents.contains_key(&(id as u32)))
                .map(|_| (id as u32, None))
        });
        let field_order: Vec<_> = plain_structs
            .chain(derivations.into_iter().map(|(id, base)| (id, Some(base))))
            .collect();
        for (id, base) in field_order {
            let mut infos = base.map_or_else(Vec::new, |base| table.info(base).fields);
            let inherited_count = infos.len();
            let info = &table.types[id as usize];
            let mut declared = HashSet::new();
            for field in field_types[id as usize].expect("struct fields") {
                if !declared.insert(&field.name) {
                    diagnostics.push(diagnostic(
                        23,
                        field.span,
                        format!(
                            "struct '{}' declares field '{}' more than once",
                            info.name, field.name
                        ),
                    ));
                } else if infos[..inherited_count]
                    .iter()
                    .any(|inherited| inherited.name == field.name)
                {
                    diagnostics.push(diagnostic(
                        23,
                        field.span,
                        format!(
                            "error type '{}' redeclares inherited field '{}'",
                            info.name, field.name
                        ),
                    ));
                }
                let ty = match table.resolve(&info.module, &field.ty) {
                    Ok(ty) => ty,
                    Err(failure) => {
                        if within(failure.span, field.ty.span) {
                            diagnostics.push(diagnostic(
                                failure.code,
                                failure.span,
                                failure.message,
                            ));
                        }
                        Ty::Error
                    }
                };
                infos.push(FieldInfo {
                    name: field.name.clone(),
                    public: field.public,
                    module: info.module.clone(),
                    ty,
                    ty_span: field.ty.span,
                });
            }
            table.types[id as usize].fields = infos;
        }
        // Enum variants: payload types are resolved like field types.
        let mut payload_spans: Vec<(usize, Vec<Span>)> = Vec::new();
        for (id, variants, module) in &variant_types {
            let mut infos: Vec<VariantInfo> = Vec::new();
            let mut spans = Vec::new();
            for variant in *variants {
                let mut payload = Vec::new();
                for ty in &variant.payload {
                    let resolved = match table.resolve(module, ty) {
                        Ok(ty) => ty,
                        Err(failure) => {
                            if within(failure.span, ty.span) {
                                diagnostics.push(diagnostic(
                                    failure.code,
                                    failure.span,
                                    failure.message,
                                ));
                            }
                            Ty::Error
                        }
                    };
                    payload.push(resolved);
                    spans.push(ty.span);
                }
                infos.push(VariantInfo {
                    name: variant.name.clone(),
                    payload,
                });
            }
            table.types[*id].variants = infos;
            payload_spans.push((*id, spans));
        }
        // A type that contains itself by value, directly or through struct
        // fields, enum payloads and arrays, would have infinite size.
        let mut recursion = |id: usize, ty: &Ty, span: Span, table: &Self| {
            let mut contained = Vec::new();
            contained_types(ty, &mut contained);
            for target in contained {
                if table.reaches(target, id) {
                    let what = |index: usize| {
                        if table.info(index as u32).is_enum {
                            "enum"
                        } else {
                            "struct"
                        }
                    };
                    diagnostics.push(diagnostic(
                        26,
                        span,
                        format!(
                            "recursive {}: '{}' contains '{}' by value, so '{}' would have infinite size",
                            what(id),
                            table.types[id].name,
                            table.info(target as u32).name,
                            table.types[id].name
                        ),
                    ));
                    break;
                }
            }
        };
        for (id, info) in table.types.iter().enumerate() {
            for field in &info.fields {
                recursion(id, &field.ty, field.ty_span, &table);
            }
        }
        for (id, spans) in &payload_spans {
            let payloads = table.types[*id]
                .variants
                .iter()
                .flat_map(|variant| variant.payload.iter().cloned())
                .collect::<Vec<_>>();
            for (ty, span) in payloads.iter().zip(spans) {
                recursion(*id, ty, *span, &table);
            }
        }
        (table, diagnostics)
    }

    /// Validate ancestry and return the parent links in base-first order.
    fn check_derivations(
        &mut self,
        bases: &HashMap<u32, &Type>,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Vec<(u32, u32)> {
        let mut visited = HashSet::new();
        let mut ordered = Vec::new();
        for id in 0..self.types.len() as u32 {
            let mut child = id;
            let mut chain = Vec::new();
            while let Some(&base) = bases.get(&child) {
                if !visited.insert(child) {
                    break;
                }
                let module = &self.types[child as usize].module;
                let parent = match self.resolve_error_base(module, base) {
                    Ok(parent) if self.is_error_type(parent) || bases.contains_key(&parent) => {
                        parent
                    }
                    Ok(_) => {
                        diagnostics.push(diagnostic(17, base.span, non_error_base(base)));
                        break;
                    }
                    Err(failure) => {
                        if within(failure.span, base.span) {
                            diagnostics.push(diagnostic(
                                failure.code,
                                failure.span,
                                failure.message,
                            ));
                        }
                        break;
                    }
                };
                chain.push((child, parent));
                if self.is_error_type(parent) {
                    for (child, parent) in chain.drain(..).rev() {
                        self.error_parents.insert(child, parent);
                        ordered.push((child, parent));
                    }
                    break;
                }
                child = parent;
            }
            if let Some(&(last, parent)) = chain.last() {
                if chain.iter().any(|&(child, _)| child == parent) {
                    let span = bases[&last].span;
                    let name = &self.types[parent as usize].name;
                    diagnostics.push(diagnostic(
                        26,
                        span,
                        format!("error derivation cycle through '{name}'"),
                    ));
                }
            }
        }
        ordered
    }

    /// Follow nominal aliases without instantiating templates that may depend on
    /// the hierarchy being built (for example, `Result<i32, Derived>`).
    fn resolve_error_base(&self, module: &str, base: &Type) -> Result<u32, TypeFailure> {
        let mut module = module;
        let mut ty = base;
        let mut aliases = HashSet::new();
        loop {
            if templates::lookup(&ty.path).is_some_and(|template| template.id == TemplateId::Error)
            {
                let Ty::Struct(id, _) = self.resolve(module, ty)? else {
                    unreachable!("Error is a struct");
                };
                return Ok(id);
            }
            if templates::lookup(&ty.path).is_some()
                || matches!(ty.path.as_slice(), [name] if primitive(name).is_some())
            {
                return Err(TypeFailure {
                    span: base.span,
                    code: 17,
                    message: non_error_base(base),
                });
            }
            match self.lookup_definition(module, ty) {
                Some((_, Def::Named(id))) if ty.arguments.is_empty() => return Ok(*id),
                Some((
                    key,
                    Def::Alias {
                        module: owner,
                        target,
                    },
                )) if ty.arguments.is_empty() => {
                    if !aliases.insert(key) {
                        return Err(TypeFailure {
                            span: ty.span,
                            code: 26,
                            message: format!("type alias cycle through '{}'", ty.path.join("::")),
                        });
                    }
                    module = owner;
                    ty = target;
                }
                _ => return Err(unresolved_type(ty)),
            }
        }
    }

    /// Whether type `from` reaches type `to` by value, through struct fields,
    /// enum payloads and arrays of any depth.
    fn reaches(&self, from: usize, to: usize) -> bool {
        let mut seen = HashSet::new();
        let mut pending = vec![from];
        while let Some(current) = pending.pop() {
            if current == to {
                return true;
            }
            if !seen.insert(current) {
                continue;
            }
            for field in &self.info(current as u32).fields {
                contained_types(&field.ty, &mut pending);
            }
            for variant in &self.info(current as u32).variants {
                for ty in &variant.payload {
                    contained_types(ty, &mut pending);
                }
            }
        }
        false
    }

    fn resolve_alias(&self, alias_key: &str) -> Result<Ty, TypeFailure> {
        match self.aliases.borrow().get(alias_key) {
            Some(AliasState::Done(result)) => return result.clone(),
            Some(AliasState::Resolving) => unreachable!("cycles are detected by the caller"),
            None => {}
        }
        let Some(Def::Alias { module, target }) = self.defs.get(alias_key) else {
            unreachable!("alias key checked by the caller")
        };
        self.aliases
            .borrow_mut()
            .insert(alias_key.to_owned(), AliasState::Resolving);
        let result = self.resolve(module, target);
        self.aliases
            .borrow_mut()
            .insert(alias_key.to_owned(), AliasState::Done(result.clone()));
        result
    }

    /// Resolve a written type in `module`: primitives, `Array<T, N>`, structs, enums
    /// and aliases (followed to their targets).
    pub fn resolve(&self, module: &str, ty: &Type) -> Result<Ty, TypeFailure> {
        let failure = |code: u16, message: String| TypeFailure {
            span: ty.span,
            code,
            message,
        };
        if let Some(template) = templates::lookup(&ty.path) {
            let arguments = resolve_arguments(template, ty, |kind, argument| {
                let resolved = self.resolve(module, argument)?;
                self.check_template_argument(template, kind, &resolved, argument.span)?;
                Ok(resolved)
            })?;
            match template.id {
                TemplateId::Error => return Ok(self.error_type(ty.span)),
                TemplateId::Option | TemplateId::Result | TemplateId::Attempt => {
                    return Ok(self.instantiate_enum(template, arguments, ty.span));
                }
                TemplateId::Array => {
                    let [ResolvedArgument::Type(element), ResolvedArgument::Integer(count)] =
                        arguments.as_slice()
                    else {
                        unreachable!("template argument contract checked above");
                    };
                    return Ok(Ty::Array(Box::new(element.clone()), *count));
                }
            }
        }
        if !ty.arguments.is_empty() {
            return Err(failure(1, "unsupported type arguments".into()));
        }
        if let [name] = ty.path.as_slice() {
            if let Some(primitive) = primitive(name) {
                return Ok(primitive);
            }
        }
        match self.lookup_definition(module, ty) {
            Some((_, Def::Named(id))) => {
                let info = &self.types[*id as usize];
                let name = info.name.as_str().into();
                Ok(if info.is_enum {
                    Ty::Enum(*id, name)
                } else {
                    Ty::Struct(*id, name)
                })
            }
            Some((definition_key, Def::Alias { .. })) => {
                if matches!(
                    self.aliases.borrow().get(definition_key),
                    Some(AliasState::Resolving)
                ) {
                    return Err(failure(
                        26,
                        format!("type alias cycle through '{}'", ty.path.join("::")),
                    ));
                }
                self.resolve_alias(definition_key)
            }
            None => Err(unresolved_type(ty)),
        }
    }

    fn lookup_definition(&self, module: &str, ty: &Type) -> Option<(&String, &Def)> {
        let imports = self.imports.get(module);
        let expanded = if let [name] = ty.path.as_slice() {
            if self.defs.contains_key(&key(module, name)) {
                key(module, name)
            } else {
                normalize(imports?.get(name)?).to_owned()
            }
        } else {
            let first = &ty.path[0];
            match imports.and_then(|imports| imports.get(first)) {
                Some(target) => format!("{}::{}", target, ty.path[1..].join("::")),
                None => ty.path.join("::"),
            }
        };
        self.defs.get_key_value(normalize(&expanded))
    }
}

fn unresolved_type(ty: &Type) -> TypeFailure {
    TypeFailure {
        span: ty.span,
        code: 1,
        message: format!("unsupported or unresolved type '{}'", ty.path.join("::")),
    }
}

fn non_error_base(base: &Type) -> String {
    format!(
        "error derivation requires Error or a type derived from it as its base, found '{}'",
        base.path.join("::")
    )
}

/// Struct and enum ids contained by value in a field or payload type: the type
/// itself, or the types inside an array of any depth.
fn contained_types(ty: &Ty, out: &mut Vec<usize>) {
    match ty {
        Ty::Struct(id, _) | Ty::Enum(id, _) => out.push(*id as usize),
        Ty::Array(element, _) => contained_types(element, out),
        _ => {}
    }
}

#[cfg(test)]
mod outcome_tests {
    use super::*;
    use memobits_diagnostics::SourceId;

    #[test]
    fn option_instances_share_alias_identity_and_keep_distinct_payloads() {
        let parsed = memobits_syntax::parse(SourceId(0),
            "type Number = i32; type A = Option<Number>; type B = Option<i32>; type C = Option<u32>; type D = Option<Option<i32>>;");
        assert!(parsed.diagnostics.is_empty());
        let (table, diagnostics) = TypeTable::build(&[("", &parsed.module)], HashMap::new());
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let a = table.resolve_alias("::A").unwrap();
        assert_eq!(a, table.resolve_alias("::B").unwrap());
        assert_ne!(a, table.resolve_alias("::C").unwrap());
        assert_ne!(a, table.resolve_alias("::D").unwrap());
        assert_eq!(table.definitions().len(), 3);
        let Ty::Enum(id, _) = a else {
            panic!("expected enum")
        };
        let info = table.info(id);
        assert_eq!(info.variants[0].payload, vec![Ty::Primitive("i32")]);
        assert!(info.variants[1].payload.is_empty());
    }

    #[test]
    fn option_does_not_hide_recursive_value_layouts() {
        let parsed = memobits_syntax::parse(SourceId(0), "type Node { next: Option<Node> }");
        assert!(parsed.diagnostics.is_empty());
        let (_, diagnostics) = TypeTable::build(&[("", &parsed.module)], HashMap::new());
        assert!(!diagnostics.is_empty());
    }
}
