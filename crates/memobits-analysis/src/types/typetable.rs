//! Nominal type table shared by every module checked together: struct and enum
//! definitions with canonical identity (`module::Name`), and type aliases
//! resolved to their targets. Structs and enums share one id space.
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use memobits_diagnostics::{Diagnostic, Span};
use memobits_ir::{ErrorAncestry, TypeId};
use memobits_syntax::{
    Field, GenericParameter, GenericParameterKind, ItemKind, Module, Type, TypeArgument,
    TypeDefinition,
};

use memobits_syntax::templates::{self, ParameterKind, Template, TemplateId};

use super::templates::{resolve_arguments, ResolvedArgument};
use super::{diagnostic, ir_access, FunctionParameter, TupleAliases, Ty};

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
    pub bodyless: bool,
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
    Generic {
        module: String,
        name: String,
        parameters: Vec<GenericParameter>,
        definition: TypeDefinition,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum InstanceKey {
    Template(TemplateId),
    Generic(String),
    Tuple(String),
    Record(String),
    AnonymousEnum(Span, String),
}

#[derive(Clone)]
enum AliasState {
    Resolving,
    Done(Result<Ty, TypeFailure>),
}

pub(super) struct TypeTable {
    types: Vec<StructInfo>,
    instances: RefCell<Vec<(InstanceKey, Vec<ResolvedArgument>, StructInfo)>>,
    defs: HashMap<String, Def>,
    error_parents: HashMap<u32, u32>,
    imports: HashMap<String, HashMap<String, String>>,
    aliases: RefCell<HashMap<String, AliasState>>,
    generic_in_progress: RefCell<HashSet<String>>,
    /// Already-resolved types spliced into written types as `\0ty` paths while
    /// specializing generic method bodies and signatures.
    resolved_arguments: RefCell<Vec<Ty>>,
}

fn key(module: &str, name: &str) -> String {
    format!("{module}::{name}")
}

fn substitute_type(
    written: &Type,
    types: &HashMap<String, Type>,
    constants: &HashMap<String, u32>,
) -> Type {
    if written.path.len() == 1 && written.arguments.is_empty() {
        if let Some(replacement) = types.get(&written.path[0]) {
            return replacement.clone();
        }
    }
    let mut output = written.clone();
    output.arguments = written
        .arguments
        .iter()
        .map(|argument| match argument {
            // A const parameter forwarded as a nominal argument (`Tag<N>`)
            // parses as a type path; substitute its value when it is in scope.
            TypeArgument::Type(ty)
                if ty.path.len() == 1
                    && ty.arguments.is_empty()
                    && !types.contains_key(&ty.path[0])
                    && constants.contains_key(&ty.path[0]) =>
            {
                TypeArgument::Integer(memobits_syntax::IntegerLiteral {
                    span: ty.span,
                    raw: constants[&ty.path[0]].to_string(),
                })
            }
            TypeArgument::Type(ty) => TypeArgument::Type(substitute_type(ty, types, constants)),
            TypeArgument::TupleField { label, ty } => TypeArgument::TupleField {
                label: label.clone(),
                ty: Box::new(substitute_type(ty, types, constants)),
            },
            TypeArgument::Reference {
                span,
                access,
                referent,
            } => TypeArgument::Reference {
                span: *span,
                access: *access,
                referent: substitute_type(referent, types, constants),
            },
            TypeArgument::Integer(integer) => TypeArgument::Integer(integer.clone()),
            TypeArgument::Const(name) => constants.get(name).map_or_else(
                || TypeArgument::Const(name.clone()),
                |value| {
                    TypeArgument::Integer(memobits_syntax::IntegerLiteral {
                        span: written.span,
                        raw: value.to_string(),
                    })
                },
            ),
        })
        .collect();
    output
}

/// Parenthesize a type name when it would otherwise bind wrongly next to `?` or `!`.
fn grouped(name: &str) -> String {
    let mut depth = 0i32;
    let mut loose_operator = false;
    let mut previous = ' ';
    for ch in name.chars() {
        match ch {
            '(' | '<' => depth += 1,
            ')' | '>' => depth -= 1,
            '!' if depth == 0 && previous == ' ' => loose_operator = true,
            _ => {}
        }
        previous = ch;
    }
    if name.starts_with("borrow ") || name.starts_with("share ") || loose_operator {
        format!("({name})")
    } else {
        name.to_owned()
    }
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
        "bool" => "bool",
        "char" => "char",
        _ => return None,
    }))
}

impl TypeTable {
    fn contains_reference(&self, ty: &Ty, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Ty::Reference { .. } => true,
            Ty::Array(element, _) => self.contains_reference(element, visited),
            Ty::Struct(id, _) | Ty::Enum(id, _) => {
                if !visited.insert(*id) {
                    return false;
                }
                let info = self.info(*id);
                info.fields
                    .iter()
                    .any(|field| self.contains_reference(&field.ty, visited))
                    || info
                        .variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|payload| self.contains_reference(payload, visited))
            }
            _ => false,
        }
    }

    fn error_type(&self, span: Span) -> Ty {
        let mut instances = self.instances.borrow_mut();
        if let Some((index, _)) = instances
            .iter()
            .enumerate()
            .find(|(_, entry)| entry.0 == InstanceKey::Template(TemplateId::Error))
        {
            return Ty::Struct((self.types.len() + index) as u32, "Error".into());
        }
        let id = (self.types.len() + instances.len()) as u32;
        instances.push((
            InstanceKey::Template(TemplateId::Error),
            Vec::new(),
            StructInfo {
                name: "Error".into(),
                module: "__prelude".into(),
                span,
                is_enum: false,
                bodyless: false,
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

    pub(super) fn utf8_error_type(&self, span: Span) -> Ty {
        let root = self.error_type(span);
        let offset = self.instantiate_enum(
            templates::by_id(TemplateId::Option),
            vec![ResolvedArgument::Type(Ty::Primitive("i32"))],
            span,
        );
        let mut instances = self.instances.borrow_mut();
        if let Some(index) = instances
            .iter()
            .position(|entry| entry.0 == InstanceKey::Template(TemplateId::Utf8Error))
        {
            return Ty::Struct((self.types.len() + index) as u32, "Utf8Error".into());
        }
        let id = (self.types.len() + instances.len()) as u32;
        instances.push((
            InstanceKey::Template(TemplateId::Utf8Error),
            vec![ResolvedArgument::Type(root)],
            StructInfo {
                name: "Utf8Error".into(),
                module: "__prelude".into(),
                span,
                is_enum: false,
                bodyless: false,
                fields: [("code", Ty::Primitive("u32")), ("offset", offset)]
                    .into_iter()
                    .map(|(name, ty)| FieldInfo {
                        name: name.into(),
                        public: true,
                        module: "__prelude".into(),
                        ty,
                        ty_span: span,
                    })
                    .collect(),
                variants: Vec::new(),
            },
        ));
        Ty::Struct(id, "Utf8Error".into())
    }

    pub(super) fn instantiate_enum(
        &self,
        template: &Template,
        arguments: Vec<ResolvedArgument>,
        span: Span,
    ) -> Ty {
        let mut instances = self.instances.borrow_mut();
        if let Some((index, (_, _, info))) =
            instances.iter().enumerate().find(|(_, (id, args, _))| {
                *id == InstanceKey::Template(template.id) && *args == arguments
            })
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
        let name = match template.id {
            TemplateId::Option => format!("{}?", grouped(&names[0])),
            TemplateId::Result => match names[0].strip_suffix('?') {
                Some(value) => format!("{} ?! {}", value, grouped(&names[1])),
                None => format!("{} ! {}", grouped(&names[0]), grouped(&names[1])),
            },
            _ => format!("{}<{}>", template.name, names.join(", ")),
        };
        let id = (self.types.len() + instances.len()) as u32;
        let info = StructInfo {
            name: name.clone(),
            module: format!("__prelude::instance{id}"),
            span,
            is_enum: true,
            bodyless: false,
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
        instances.push((InstanceKey::Template(template.id), arguments, info));
        Ty::Enum(id, name.into())
    }

    pub(super) fn instantiate_tuple(
        &self,
        elements: Vec<(Option<String>, Ty)>,
        span: Span,
    ) -> Result<Ty, TypeFailure> {
        let aliases = TupleAliases {
            labels: elements.iter().map(|(label, _)| label.clone()).collect(),
            nested: elements
                .iter()
                .map(|(_, ty)| match ty {
                    Ty::Tuple(_, _, aliases) => Some(Box::new(aliases.clone())),
                    _ => None,
                })
                .collect(),
        };
        let identity = format!(
            "{:?}",
            elements
                .iter()
                .map(|(_, ty)| self.semantic_tuple_element_identity(ty))
                .collect::<Vec<_>>()
        );
        let mut instances = self.instances.borrow_mut();
        if let Some((index, (_, _, info))) = instances
            .iter_mut()
            .enumerate()
            .find(|(_, (key, _, _))| *key == InstanceKey::Tuple(identity.clone()))
        {
            return Ok(Ty::Tuple(
                (self.types.len() + index) as u32,
                info.name.as_str().into(),
                aliases,
            ));
        }
        let id = (self.types.len() + instances.len()) as u32;
        let name = format!("Tuple{id}");
        let info = StructInfo {
            name: name.clone(),
            module: "\0tuple".into(),
            span,
            is_enum: false,
            bodyless: false,
            fields: elements
                .iter()
                .enumerate()
                .map(|(index, (_, ty))| FieldInfo {
                    name: index.to_string(),
                    public: true,
                    module: "\0tuple".into(),
                    ty: ty.clone(),
                    ty_span: span,
                })
                .collect(),
            variants: Vec::new(),
        };
        instances.push((InstanceKey::Tuple(identity), Vec::new(), info));
        Ok(Ty::Tuple(id, name.into(), aliases))
    }

    /// Intern an anonymous record by its exact named field/type set. Field
    /// order in the resulting layout is canonical; initializer order remains
    /// in the syntax tree and is honored by lowering.
    pub(super) fn instantiate_record(&self, mut fields: Vec<(String, Ty)>, span: Span) -> Ty {
        fields.sort_by(|left, right| left.0.cmp(&right.0));
        let identity = format!(
            "{:?}",
            fields
                .iter()
                .map(|(name, ty)| (name, self.semantic_tuple_element_identity(ty)))
                .collect::<Vec<_>>()
        );
        let mut instances = self.instances.borrow_mut();
        if let Some((index, (_, _, info))) = instances
            .iter()
            .enumerate()
            .find(|(_, (key, _, _))| *key == InstanceKey::Record(identity.clone()))
        {
            return Ty::Struct((self.types.len() + index) as u32, info.name.as_str().into());
        }
        let id = (self.types.len() + instances.len()) as u32;
        let name = format!("Record{id}");
        let info = StructInfo {
            name: name.clone(),
            module: "\0record".into(),
            span,
            is_enum: false,
            bodyless: false,
            fields: fields
                .into_iter()
                .map(|(name, ty)| FieldInfo {
                    name,
                    public: true,
                    module: "\0record".into(),
                    ty,
                    ty_span: span,
                })
                .collect(),
            variants: Vec::new(),
        };
        instances.push((InstanceKey::Record(identity), Vec::new(), info));
        Ty::Struct(id, name.into())
    }

    pub(super) fn instantiate_anonymous_enum(&self, variants: &[VariantInfo], span: Span) -> Ty {
        let identity = variants
            .iter()
            .map(|variant| {
                format!(
                    "{}({})",
                    variant.name,
                    variant
                        .payload
                        .iter()
                        .map(|ty| self.semantic_tuple_element_identity(ty))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            })
            .collect::<Vec<_>>()
            .join("|");
        let key = InstanceKey::AnonymousEnum(span, identity);
        let mut instances = self.instances.borrow_mut();
        if let Some((index, (_, _, info))) = instances
            .iter()
            .enumerate()
            .find(|(_, (existing, _, _))| existing == &key)
        {
            return Ty::Enum((self.types.len() + index) as u32, info.name.as_str().into());
        }
        let id = (self.types.len() + instances.len()) as u32;
        let name = format!("Enum{id}");
        let info = StructInfo {
            name: name.clone(),
            module: "\0anonymous-enum".into(),
            span,
            is_enum: true,
            bodyless: false,
            fields: Vec::new(),
            variants: variants.to_vec(),
        };
        instances.push((key, Vec::new(), info));
        Ty::Enum(id, name.into())
    }

    fn semantic_tuple_element_identity(&self, ty: &Ty) -> String {
        match ty {
            Ty::Tuple(id, _, _) => {
                let fields = &self.info(*id).fields;
                format!(
                    "tuple({})",
                    fields
                        .iter()
                        .map(|field| self.semantic_tuple_element_identity(&field.ty))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
            Ty::Array(element, count) => {
                format!(
                    "array({}, {count})",
                    self.semantic_tuple_element_identity(element)
                )
            }
            Ty::Reference { access, inner, .. } => format!(
                "reference({access:?}, {})",
                self.semantic_tuple_element_identity(inner)
            ),
            Ty::Function(parameters, result) => format!(
                "function({:?}, {})",
                parameters
                    .iter()
                    .map(|parameter| (
                        parameter.access,
                        self.semantic_tuple_element_identity(&parameter.ty)
                    ))
                    .collect::<Vec<_>>(),
                self.semantic_tuple_element_identity(result)
            ),
            // All remaining variants have no occurrence-local tuple aliases.
            other => format!("{other:?}"),
        }
    }

    fn instance_template(&self, id: u32) -> Option<TemplateId> {
        let index = (id as usize).checked_sub(self.types.len())?;
        self.instances
            .borrow()
            .get(index)
            .and_then(|entry| match entry.0 {
                InstanceKey::Template(id) => Some(id),
                InstanceKey::Generic(_)
                | InstanceKey::Tuple(_)
                | InstanceKey::Record(_)
                | InstanceKey::AnonymousEnum(_, _) => None,
            })
    }

    pub(super) fn enum_template(&self, id: u32) -> Option<&'static Template> {
        self.instance_template(id).map(templates::by_id)
    }

    fn is_error_type(&self, id: u32) -> bool {
        self.error_ancestry(id).is_some()
    }

    pub(super) fn error_ancestry(&self, id: u32) -> Option<ErrorAncestry> {
        if let Some(&parent) = self.error_parents.get(&id) {
            Some(ErrorAncestry::Derived(TypeId(parent)))
        } else if self.instance_template(id) == Some(TemplateId::Error) {
            Some(ErrorAncestry::Root)
        } else if self.instance_template(id) == Some(TemplateId::Utf8Error) {
            let index = id as usize - self.types.len();
            let instances = self.instances.borrow();
            let [ResolvedArgument::Type(Ty::Struct(parent, _))] = instances[index].1.as_slice()
            else {
                unreachable!("Utf8Error has an Error parent");
            };
            Some(ErrorAncestry::Derived(TypeId(*parent)))
        } else {
            None
        }
    }

    pub(super) fn has_error_ancestor(&self, actual: &Ty, expected: &Ty) -> bool {
        let (Ty::Struct(mut child, _), Ty::Struct(ancestor, _)) = (actual, expected) else {
            return false;
        };
        while let Some(ErrorAncestry::Derived(TypeId(parent))) = self.error_ancestry(child) {
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
            Some((InstanceKey::Template(TemplateId::Option), args, _))
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
        ) = (templates::lookup_type(ty), ty.arguments.as_slice())
        {
            if template.id == TemplateId::Option {
                let inner = self.resolve(module, referent)?;
                if matches!(inner, Ty::List(_)) {
                    return Err(TypeFailure {
                        span: *span,
                        code: 17,
                        message: "List borrows cannot be stored in Option in this slice".into(),
                    });
                }
                if inner == super::UNIT {
                    return Err(TypeFailure {
                        span: *span,
                        code: 17,
                        message: "(borrow T)? requires a non-Unit referent".into(),
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

    /// Canonical declaration identity for a named generic type application.
    pub fn generic_definition_key(&self, module: &str, ty: &Type) -> Option<String> {
        let (key, definition) = self.lookup_definition(module, ty)?;
        matches!(definition, Def::Generic { .. }).then(|| key.clone())
    }

    /// The generic declaration that produced a concrete nominal instance.
    pub fn generic_origin(&self, id: u32) -> Option<String> {
        let index = id as usize;
        let instances = self.instances.borrow();
        let instance = instances.get(index.checked_sub(self.types.len())?)?;
        match &instance.0 {
            InstanceKey::Generic(key) => Some(key.clone()),
            InstanceKey::Template(_)
            | InstanceKey::Tuple(_)
            | InstanceKey::Record(_)
            | InstanceKey::AnonymousEnum(_, _) => None,
        }
    }

    /// Concrete arguments of a generic nominal instance, in declaration order.
    pub fn generic_arguments(&self, id: u32) -> Option<Vec<ResolvedArgument>> {
        let index = id as usize;
        let instances = self.instances.borrow();
        let instance = instances.get(index.checked_sub(self.types.len())?)?;
        matches!(&instance.0, InstanceKey::Generic(_)).then(|| instance.1.clone())
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
            generic_in_progress: RefCell::new(HashSet::new()),
            resolved_arguments: RefCell::new(Vec::new()),
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
        let mut table = Self {
            imports,
            ..Self::empty()
        };
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
                    generic_parameters,
                    bounds,
                    ..
                } = &item.kind
                else {
                    continue;
                };
                // Removed built-in spellings stay reserved so their TE001
                // migration guidance can never be shadowed by a user type.
                if matches!(
                    name.as_str(),
                    "String" | "string" | "Option" | "Result" | "Attempt"
                ) || templates::lookup(std::slice::from_ref(name)).is_some()
                {
                    diagnostics.push(diagnostic(
                        3,
                        item.span,
                        format!("'{}' is reserved for a compiler-known type", name),
                    ));
                }
                if !generic_parameters.is_empty() {
                    if !bounds.is_empty() {
                        diagnostics.push(diagnostic(
                            2,
                            item.span,
                            "generic type where-constraints are not implemented yet",
                        ));
                    }
                    match definition {
                        TypeDefinition::Bodyless => diagnostics.push(diagnostic(
                            2,
                            item.span,
                            "generic bodyless types are not supported",
                        )),
                        TypeDefinition::Alias(_) => diagnostics.push(diagnostic(
                            2,
                            item.span,
                            "generic aliases are not supported",
                        )),
                        TypeDefinition::Struct(_) | TypeDefinition::Enum(_) => {}
                    }
                    if base.is_some() {
                        diagnostics.push(diagnostic(
                            2,
                            item.span,
                            "generic derived error types are not supported",
                        ));
                    }
                    if generic_parameters
                        .iter()
                        .any(|parameter| match &parameter.kind {
                            GenericParameterKind::Type => false,
                            GenericParameterKind::Const(ty) => {
                                ty.path.as_slice() != ["u32"] || !ty.arguments.is_empty()
                            }
                        })
                    {
                        diagnostics.push(diagnostic(
                            2,
                            item.span,
                            "const generic parameters must have type u32",
                        ));
                    }
                    let def = Def::Generic {
                        module: (*module).to_owned(),
                        name: name.clone(),
                        parameters: generic_parameters.clone(),
                        definition: definition.clone(),
                    };
                    if table.defs.insert(key(module, name), def).is_some() {
                        diagnostics.push(diagnostic(
                            14,
                            item.span,
                            format!("duplicate type '{name}'"),
                        ));
                    }
                    continue;
                }
                if !bounds.is_empty() {
                    diagnostics.push(diagnostic(
                        2,
                        item.span,
                        "where-constraints require generic parameters",
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
                            bodyless: false,
                            fields: Vec::new(),
                            variants: Vec::new(),
                        });
                        field_types.push(Some(fields));
                        if let Some(base) = base {
                            bases.insert(id as u32, base);
                        }
                        Def::Named(id as u32)
                    }
                    TypeDefinition::Bodyless => {
                        let id = table.types.len();
                        table.types.push(StructInfo {
                            name: name.clone(),
                            module: (*module).to_owned(),
                            span: item.span,
                            is_enum: false,
                            bodyless: true,
                            fields: Vec::new(),
                            variants: Vec::new(),
                        });
                        field_types.push(Some(&[]));
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
                            bodyless: false,
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
            let template = templates::lookup_type(ty);
            if template.is_some_and(|template| {
                matches!(template.id, TemplateId::Error | TemplateId::Utf8Error)
            }) {
                let Ty::Struct(id, _) = self.resolve(module, ty)? else {
                    unreachable!("Error is a struct");
                };
                return Ok(id);
            }
            if template.is_some()
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

    fn instantiate_generic_type(
        &self,
        definition_key: &str,
        module: &str,
        name: &str,
        parameters: &[GenericParameter],
        definition: &TypeDefinition,
        written: &Type,
    ) -> Result<Ty, TypeFailure> {
        let fail = |message: String| TypeFailure {
            span: written.span,
            code: 2,
            message,
        };
        if written.arguments.len() != parameters.len() {
            return Err(fail(format!(
                "type '{name}' requires {} generic arguments",
                parameters.len()
            )));
        }
        let mut resolved = Vec::new();
        let mut type_substitutions = HashMap::new();
        let mut const_substitutions = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(&written.arguments) {
            match (&parameter.kind, argument) {
                (GenericParameterKind::Type, TypeArgument::Type(ty)) => {
                    let ty_value = self.resolve(module, ty)?;
                    type_substitutions.insert(parameter.name.clone(), ty.clone());
                    resolved.push(ResolvedArgument::Type(ty_value));
                }
                (GenericParameterKind::Const(_), TypeArgument::Integer(integer)) => {
                    let value =
                        integer
                            .raw
                            .replace('_', "")
                            .parse::<u32>()
                            .map_err(|_| TypeFailure {
                                span: integer.span,
                                code: 8,
                                message: "const parameter exceeds u32::MAX".into(),
                            })?;
                    const_substitutions.insert(parameter.name.clone(), value);
                    resolved.push(ResolvedArgument::Integer(value));
                }
                (GenericParameterKind::Const(_), TypeArgument::Const(_)) => {
                    return Err(fail(
                        "forwarded const arguments require generic function specialization".into(),
                    ));
                }
                _ => {
                    return Err(fail(format!(
                        "generic argument for '{}' has the wrong kind",
                        parameter.name
                    )));
                }
            }
        }
        if let Some((index, (_, _, info))) =
            self.instances
                .borrow()
                .iter()
                .enumerate()
                .find(|(_, (key, args, _))| {
                    *key == InstanceKey::Generic(definition_key.to_owned()) && *args == resolved
                })
        {
            let id = self.types.len() + index;
            let display = info.name.as_str().into();
            return Ok(if info.is_enum {
                Ty::Enum(id as u32, display)
            } else {
                Ty::Struct(id as u32, display)
            });
        }
        let identity = format!("{definition_key}<{resolved:?}>");
        {
            let mut active = self.generic_in_progress.borrow_mut();
            if active.contains(&identity) {
                return Err(fail(format!(
                    "recursive by-value generic type layout for '{name}'"
                )));
            }
            if active.len() >= 32 {
                return Err(fail("generic type specialization depth exceeds 32".into()));
            }
            active.insert(identity.clone());
        }
        let info_result = (|| {
            let (is_enum, fields, variants) = match definition {
                TypeDefinition::Struct(fields) => {
                    let mut resolved_fields = Vec::new();
                    for field in fields {
                        let field_type =
                            substitute_type(&field.ty, &type_substitutions, &const_substitutions);
                        let ty = self.resolve(module, &field_type)?;
                        resolved_fields.push(FieldInfo {
                            name: field.name.clone(),
                            public: field.public,
                            module: module.to_owned(),
                            ty,
                            ty_span: field.ty.span,
                        });
                    }
                    (false, resolved_fields, Vec::new())
                }
                TypeDefinition::Enum(variants) => {
                    let mut resolved_variants = Vec::new();
                    for variant in variants {
                        let mut payload = Vec::new();
                        for written_type in &variant.payload {
                            let substituted = substitute_type(
                                written_type,
                                &type_substitutions,
                                &const_substitutions,
                            );
                            payload.push(self.resolve(module, &substituted)?);
                        }
                        resolved_variants.push(VariantInfo {
                            name: variant.name.clone(),
                            payload,
                        });
                    }
                    (true, Vec::new(), resolved_variants)
                }
                TypeDefinition::Bodyless => {
                    return Err(fail("generic bodyless types are not supported".into()));
                }
                TypeDefinition::Alias(_) => {
                    return Err(fail("generic aliases are not supported".into()));
                }
            };
            Ok(StructInfo {
                name: format!(
                    "{}<{}>",
                    name,
                    resolved
                        .iter()
                        .map(|arg| match arg {
                            ResolvedArgument::Type(ty) => super::name(ty),
                            ResolvedArgument::Integer(n) => n.to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                module: module.to_owned(),
                span: written.span,
                is_enum,
                bodyless: false,
                fields,
                variants,
            })
        })();
        self.generic_in_progress.borrow_mut().remove(&identity);
        let info = info_result?;
        let mut instances = self.instances.borrow_mut();
        let id = self.types.len() + instances.len();
        let is_enum = info.is_enum;
        let display = info.name.clone();
        instances.push((
            InstanceKey::Generic(definition_key.to_owned()),
            resolved,
            info,
        ));
        Ok(if is_enum {
            Ty::Enum(id as u32, display.into())
        } else {
            Ty::Struct(id as u32, display.into())
        })
    }

    /// Substitute concrete types and const values for generic parameter names
    /// inside the type arguments of a written type. Each concrete type is
    /// spliced in as a `\0ty` path that `resolve` maps straight back to it, so
    /// nested generic arguments such as `Pair<Wrap<T>>` resolve through the
    /// ordinary instantiation path and keep one identity per concrete shape.
    pub(super) fn substitute_generic_arguments(
        &self,
        ty: &Type,
        types: &HashMap<String, Ty>,
        constants: &HashMap<String, u32>,
    ) -> Type {
        let mut written = HashMap::new();
        for (name, concrete) in types {
            let mut interned = self.resolved_arguments.borrow_mut();
            let index = interned
                .iter()
                .position(|candidate| candidate == concrete)
                .unwrap_or_else(|| {
                    interned.push(concrete.clone());
                    interned.len() - 1
                });
            written.insert(
                name.clone(),
                Type {
                    span: ty.span,
                    path: vec!["\0ty".into(), index.to_string()],
                    arguments: Vec::new(),
                },
            );
        }
        substitute_type(ty, &written, constants)
    }

    /// Resolve a written type in `module`, following aliases to their targets.
    pub fn resolve(&self, module: &str, ty: &Type) -> Result<Ty, TypeFailure> {
        if let [marker, index] = ty.path.as_slice() {
            if marker == "\0ty" {
                let found = index
                    .parse::<usize>()
                    .ok()
                    .and_then(|index| self.resolved_arguments.borrow().get(index).cloned());
                return found.ok_or_else(|| TypeFailure {
                    span: ty.span,
                    code: 1,
                    message: "internal resolved type reference is unavailable".into(),
                });
            }
        }
        let failure = |code: u16, message: String| TypeFailure {
            span: ty.span,
            code,
            message,
        };
        if ty.path.is_empty() {
            return Err(failure(1, "type path cannot be empty".into()));
        }
        if ty.path.as_slice() == ["\0tuple"] {
            let label_count = ty
                .arguments
                .iter()
                .filter(|argument| {
                    matches!(argument, TypeArgument::TupleField { label: Some(_), .. })
                })
                .count();
            if label_count != 0 && label_count != ty.arguments.len() {
                return Err(failure(
                    2,
                    "tuple type elements must be either all labeled or all positional".into(),
                ));
            }
            let mut labels = HashSet::new();
            for argument in &ty.arguments {
                if let TypeArgument::TupleField {
                    label: Some(label), ..
                } = argument
                {
                    if !labels.insert(label) {
                        return Err(failure(2, format!("duplicate tuple type label '{label}'")));
                    }
                }
            }
            let elements = ty
                .arguments
                .iter()
                .map(|argument| match argument {
                    TypeArgument::Type(element) => {
                        self.resolve(module, element).map(|ty| (None, ty))
                    }
                    TypeArgument::TupleField { label, ty } => {
                        self.resolve(module, ty).map(|ty| (label.clone(), ty))
                    }
                    _ => Err(failure(
                        17,
                        "tuple type elements must be value types".into(),
                    )),
                })
                .collect::<Result<Vec<_>, _>>()?;
            if elements
                .iter()
                .any(|(_, element)| self.contains_reference(element, &mut HashSet::new()))
            {
                return Err(failure(17, "tuple types cannot contain direct or nested references until embedded tuple loans are supported".into()));
            }
            return self.instantiate_tuple(elements, ty.span);
        }
        if ty.path.as_slice() == ["\0unit"] {
            return Ok(Ty::Primitive("Unit"));
        }
        if ty.path.as_slice() == ["\0fn"] {
            let Some((TypeArgument::Type(result), parameters)) = ty.arguments.split_last() else {
                return Err(failure(2, "malformed function type".into()));
            };
            let parameters = parameters
                .iter()
                .map(|argument| match argument {
                    TypeArgument::Type(parameter) => {
                        self.resolve(module, parameter).map(|ty| FunctionParameter {
                            access: memobits_ir::Access::Owned,
                            ty,
                        })
                    }
                    TypeArgument::Reference {
                        access, referent, ..
                    } => self.resolve(module, referent).map(|ty| FunctionParameter {
                        access: ir_access(*access),
                        ty,
                    }),
                    _ => Err(failure(2, "malformed function type parameter".into())),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let result = self.resolve(module, result)?;
            return Ok(Ty::Function(parameters, Box::new(result)));
        }
        if ty.path.as_slice() == ["\0record"] {
            let mut labels = HashSet::new();
            let fields = ty
                .arguments
                .iter()
                .map(|argument| match argument {
                    TypeArgument::TupleField {
                        label: Some(label),
                        ty,
                    } => {
                        if !labels.insert(label) {
                            return Err(failure(
                                2,
                                format!("duplicate anonymous record field '{label}'"),
                            ));
                        }
                        let field_ty = self.resolve(module, ty)?;
                        if self.contains_reference(&field_ty, &mut HashSet::new()) {
                            return Err(failure(
                                17,
                                "anonymous record fields cannot contain references in this slice"
                                    .into(),
                            ));
                        }
                        Ok((label.clone(), field_ty))
                    }
                    _ => Err(failure(
                        17,
                        "anonymous record types require named value fields".into(),
                    )),
                })
                .collect::<Result<Vec<_>, _>>()?;
            if fields.is_empty() {
                return Err(failure(
                    2,
                    "anonymous record types need at least one field".into(),
                ));
            }
            return Ok(self.instantiate_record(fields, ty.span));
        }
        if ty.path.first().is_some_and(|part| part == "\0enum") {
            if ty.path.len() < 2 {
                return Err(failure(
                    2,
                    "anonymous enum types need at least one variant".into(),
                ));
            }
            let mut seen = HashSet::new();
            let mut payload_specs = HashMap::new();
            for argument in &ty.arguments {
                let TypeArgument::TupleField {
                    label: Some(variant),
                    ty: payload,
                } = argument
                else {
                    return Err(failure(
                        2,
                        "anonymous enum payloads must be associated with a variant name".into(),
                    ));
                };
                if payload_specs
                    .insert(variant.as_str(), payload.as_ref())
                    .is_some()
                {
                    return Err(failure(
                        2,
                        format!(
                            "anonymous enum variant '{variant}' has duplicate payload metadata"
                        ),
                    ));
                }
            }
            let mut variants = Vec::with_capacity(ty.path.len() - 1);
            for variant in &ty.path[1..] {
                if !seen.insert(variant) {
                    return Err(failure(
                        2,
                        format!("anonymous enum variant '{variant}' is declared more than once"),
                    ));
                }
                let payload = payload_specs.remove(variant.as_str());
                let mut payload_types = Vec::new();
                if let Some(payload) = payload {
                    if payload.path.as_slice() != ["\0tuple"] {
                        return Err(failure(
                            2,
                            format!("invalid payload list for anonymous enum variant '{variant}'"),
                        ));
                    }
                    for argument in &payload.arguments {
                        let payload_ty = match argument {
                            TypeArgument::Type(payload_ty) => self.resolve(module, payload_ty)?,
                            _ => {
                                return Err(failure(
                                    17,
                                    "anonymous enum payloads require owned value types".into(),
                                ));
                            }
                        };
                        if self.contains_reference(&payload_ty, &mut HashSet::new()) {
                            return Err(failure(
                                17,
                                "anonymous enum payloads cannot contain references in this slice"
                                    .into(),
                            ));
                        }
                        payload_types.push(payload_ty);
                    }
                    if payload_types.is_empty() {
                        return Err(failure(
                            2,
                            format!("anonymous enum variant '{variant}' has an empty payload"),
                        ));
                    }
                }
                variants.push(VariantInfo {
                    name: variant.clone(),
                    payload: payload_types,
                });
            }
            if !payload_specs.is_empty() {
                return Err(failure(
                    2,
                    "anonymous enum payload metadata names an undeclared variant".into(),
                ));
            }
            return Ok(self.instantiate_anonymous_enum(&variants, ty.span));
        }
        if let Some(template) = templates::lookup_type(ty) {
            let arguments = resolve_arguments(template, ty, |kind, argument| {
                let resolved = self.resolve(module, argument)?;
                self.check_template_argument(template, kind, &resolved, argument.span)?;
                Ok(resolved)
            })?;
            match template.id {
                TemplateId::Error => return Ok(self.error_type(ty.span)),
                TemplateId::Utf8Error => return Ok(self.utf8_error_type(ty.span)),
                TemplateId::Option | TemplateId::Result => {
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
                TemplateId::List => {
                    let [ResolvedArgument::Type(element)] = arguments.as_slice() else {
                        unreachable!("template argument contract checked above");
                    };
                    match element {
                        Ty::Reference { .. } => {
                            return Err(failure(17, "List elements cannot be references".into()))
                        }
                        Ty::Primitive("Unit") => {
                            return Err(failure(17, "List elements cannot be Unit".into()))
                        }
                        _ => {}
                    }
                    return Ok(Ty::List(Box::new(element.clone())));
                }
            }
        }
        if ty.path.last().is_some_and(|name| name == "String") {
            return Err(failure(
                1,
                "'String' is no longer a source type; use lowercase 'string'".into(),
            ));
        }
        if let [name] = ty.path.as_slice() {
            if name == "string" {
                return Ok(Ty::String);
            }
            if let Some(primitive) = primitive(name) {
                return Ok(primitive);
            }
        }
        match self.lookup_definition(module, ty) {
            Some((_, Def::Named(id))) if ty.arguments.is_empty() => {
                let info = &self.types[*id as usize];
                let name = info.name.as_str().into();
                Ok(if info.is_enum {
                    Ty::Enum(*id, name)
                } else {
                    Ty::Struct(*id, name)
                })
            }
            Some((definition_key, Def::Alias { .. })) => {
                if !ty.arguments.is_empty() {
                    return Err(failure(
                        1,
                        "type aliases do not accept generic arguments".into(),
                    ));
                }
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
            Some((
                definition_key,
                Def::Generic {
                    module,
                    name,
                    parameters,
                    definition,
                },
            )) => self.instantiate_generic_type(
                definition_key,
                module,
                name,
                parameters,
                definition,
                ty,
            ),
            Some((_, Def::Named(_))) => {
                Err(failure(1, "type does not accept generic arguments".into()))
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
    let guidance = match ty.path.as_slice() {
        [name] => templates::removed_spelling_guidance(name),
        _ => None,
    };
    TypeFailure {
        span: ty.span,
        code: 1,
        message: guidance.map_or_else(
            || format!("unsupported or unresolved type '{}'", ty.path.join("::")),
            str::to_owned,
        ),
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
        let parsed = memobits_syntax::parse(
            SourceId(0),
            "type Number = i32; type A = Number?; type B = i32?; type C = u32?; type D = i32??;",
        );
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
        let parsed = memobits_syntax::parse(SourceId(0), "type Node { next: Node? }");
        assert!(parsed.diagnostics.is_empty());
        let (_, diagnostics) = TypeTable::build(&[("", &parsed.module)], HashMap::new());
        assert!(!diagnostics.is_empty());
    }

    #[test]
    fn generic_nominal_types_specialize_type_and_const_arguments_once() {
        let parsed = memobits_syntax::parse(
            SourceId(0),
            "type Box<T> { value: T } type Buffer<T, const N: u32> { data: array<T, N> } type Maybe<T> [None, Some(T)] fn use_box(value: Box<i32>) {} fn use_buffer(value: Buffer<u8, 3>) {} fn use_maybe(value: Maybe<i32>) {}",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (table, diagnostics) = TypeTable::build(&[("main", &parsed.module)], HashMap::new());
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let types = parsed
            .module
            .items
            .iter()
            .filter_map(|item| match &item.kind {
                ItemKind::Function { parameters, .. } => Some(parameters[0].ty.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let first_box = table.resolve("main", &types[0]).unwrap();
        assert_eq!(first_box, table.resolve("main", &types[0]).unwrap());
        let second_box_ty = memobits_syntax::parse(SourceId(0), "fn f(value: Box<u32>) {}");
        let ItemKind::Function { parameters, .. } = &second_box_ty.module.items[0].kind else {
            panic!()
        };
        let second_box = table.resolve("main", &parameters[0].ty).unwrap();
        assert_ne!(first_box, second_box);
        let buffer = table.resolve("main", &types[1]).unwrap();
        let Ty::Struct(id, _) = buffer else {
            panic!("expected struct")
        };
        assert_eq!(
            table.info(id).fields[0].ty,
            Ty::Array(Box::new(Ty::Primitive("u8")), 3)
        );
        let maybe = table.resolve("main", &types[2]).unwrap();
        let Ty::Enum(id, _) = maybe else {
            panic!("expected enum")
        };
        assert_eq!(
            table.info(id).variants[1].payload,
            vec![Ty::Primitive("i32")]
        );
    }

    #[test]
    fn generic_type_layout_cycles_and_unbounded_specialization_are_diagnosed() {
        for source in [
            "type Node<T> { next: Node<T> } fn use_node(value: Node<i32>) {}",
            "type Grow<T> { next: Grow<array<T, 2>> } fn use_grow(value: Grow<i32>) {}",
        ] {
            let parsed = memobits_syntax::parse(SourceId(0), source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let (table, diagnostics) =
                TypeTable::build(&[("main", &parsed.module)], HashMap::new());
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            let ItemKind::Function { parameters, .. } = &parsed.module.items[1].kind else {
                panic!()
            };
            let failure = table.resolve("main", &parameters[0].ty).unwrap_err();
            assert!(
                failure.message.contains("recursive by-value")
                    || failure.message.contains("depth exceeds"),
                "{failure:?}"
            );
        }
    }
}
