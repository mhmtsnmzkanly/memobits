//! Nominal type table shared by every module checked together: struct
//! definitions with canonical identity (`module::Name`), type aliases resolved
//! to their targets, and enum declarations (recorded only to report them).
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use memobits_diagnostics::{Diagnostic, Span};
use memobits_syntax::{ItemKind, Module, Type, TypeArgument, TypeDefinition};

use super::{diagnostic, Ty};

#[derive(Clone, Debug)]
pub(super) struct FieldInfo {
    pub name: String,
    pub public: bool,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub(super) struct StructInfo {
    pub name: String,
    pub module: String,
    pub span: Span,
    pub fields: Vec<FieldInfo>,
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
    Struct(u32),
    Alias { module: String, target: Type },
    Enum,
}

#[derive(Clone)]
enum AliasState {
    Resolving,
    Done(Result<Ty, TypeFailure>),
}

pub(super) struct TypeTable {
    pub structs: Vec<StructInfo>,
    defs: HashMap<String, Def>,
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
    pub fn empty() -> Self {
        Self {
            structs: Vec::new(),
            defs: HashMap::new(),
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
        let mut field_types: Vec<(usize, Vec<(&memobits_syntax::Field, String)>)> = Vec::new();
        let mut alias_items = Vec::new();
        for (module, syntax) in modules {
            for item in &syntax.items {
                let ItemKind::Type {
                    name, definition, ..
                } = &item.kind
                else {
                    continue;
                };
                let def = match definition {
                    TypeDefinition::Struct(fields) => {
                        let id = table.structs.len();
                        table.structs.push(StructInfo {
                            name: name.clone(),
                            module: (*module).to_owned(),
                            span: item.span,
                            fields: Vec::new(),
                        });
                        field_types.push((
                            id,
                            fields.iter().map(|f| (f, (*module).to_owned())).collect(),
                        ));
                        Def::Struct(id as u32)
                    }
                    TypeDefinition::Alias(target) => {
                        alias_items.push((key(module, name), target));
                        Def::Alias {
                            module: (*module).to_owned(),
                            target: target.clone(),
                        }
                    }
                    TypeDefinition::Enum(_) => Def::Enum,
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
        // Aliases: resolve each so its own declaration reports its failures.
        for (alias_key, target) in alias_items {
            if let Err(failure) = table.resolve_alias(&alias_key) {
                if within(failure.span, target.span) {
                    diagnostics.push(diagnostic(failure.code, failure.span, failure.message));
                }
            }
        }
        // Struct fields.
        let mut resolved: Vec<Vec<(FieldInfo, Span)>> = Vec::new();
        for (id, fields) in &field_types {
            let mut infos: Vec<(FieldInfo, Span)> = Vec::new();
            for (field, module) in fields {
                if infos.iter().any(|(known, _)| known.name == field.name) {
                    diagnostics.push(diagnostic(
                        23,
                        field.span,
                        format!(
                            "struct '{}' declares field '{}' more than once",
                            table.structs[*id].name, field.name
                        ),
                    ));
                }
                let ty = match table.resolve(module, &field.ty) {
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
                infos.push((
                    FieldInfo {
                        name: field.name.clone(),
                        public: field.public,
                        ty,
                    },
                    field.ty.span,
                ));
            }
            resolved.push(infos);
        }
        for ((id, _), infos) in field_types.iter().zip(&resolved) {
            table.structs[*id].fields = infos.iter().map(|(info, _)| info.clone()).collect();
        }
        // Struct-typed and array-typed fields are outside this package; a struct
        // that contains itself by value is an error whatever the package.
        for ((id, _), infos) in field_types.iter().zip(&resolved) {
            for (info, span) in infos {
                match &info.ty {
                    Ty::Struct(target, target_name) => {
                        if table.reaches(*target as usize, *id) {
                            diagnostics.push(diagnostic(
                                26,
                                *span,
                                format!(
                                    "recursive struct: '{}' contains '{}' by value, so '{}' would have infinite size",
                                    table.structs[*id].name, target_name, table.structs[*id].name
                                ),
                            ));
                        } else {
                            diagnostics.push(diagnostic(
                                17,
                                *span,
                                format!(
                                    "field '{}' has struct type '{}'; struct-typed fields are not supported yet",
                                    info.name, target_name
                                ),
                            ));
                        }
                    }
                    Ty::Array(..) => diagnostics.push(diagnostic(
                        17,
                        *span,
                        format!(
                            "field '{}' has an array type; array-typed fields are not supported yet",
                            info.name
                        ),
                    )),
                    _ => {}
                }
            }
        }
        (table, diagnostics)
    }

    /// Whether struct `from` reaches struct `to` through struct-typed fields.
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
            for field in &self.structs[current].fields {
                if let Ty::Struct(next, _) = &field.ty {
                    pending.push(*next as usize);
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

    /// Resolve a written type in `module`: primitives, `Array<T, N>`, structs and
    /// aliases (followed to their targets). Enums are reported as unsupported.
    pub fn resolve(&self, module: &str, ty: &Type) -> Result<Ty, TypeFailure> {
        let failure = |code: u16, message: String| TypeFailure {
            span: ty.span,
            code,
            message,
        };
        if ty.path == ["Array"] {
            let [TypeArgument::Type(element), TypeArgument::Integer(count)] =
                ty.arguments.as_slice()
            else {
                return Err(failure(
                    2,
                    "Array requires an element type and integer literal length".into(),
                ));
            };
            let element = self.resolve(module, element)?;
            let Ok(count) = count.raw.replace('_', "").parse::<u32>() else {
                return Err(TypeFailure {
                    span: count.span,
                    code: 8,
                    message: "array length exceeds implementation limit u32::MAX".into(),
                });
            };
            if matches!(element, Ty::Struct(..)) {
                return Err(failure(
                    17,
                    "arrays of structs are not supported yet".into(),
                ));
            }
            return Ok(Ty::Array(Box::new(element), count));
        }
        if !ty.arguments.is_empty() {
            return Err(failure(1, "unsupported type arguments".into()));
        }
        let unresolved = || {
            failure(
                1,
                format!("unsupported or unresolved type '{}'", ty.path.join("::")),
            )
        };
        if let [name] = ty.path.as_slice() {
            if let Some(primitive) = primitive(name) {
                return Ok(primitive);
            }
        }
        let imports = self.imports.get(module);
        let expanded = if let [name] = ty.path.as_slice() {
            if self.defs.contains_key(&key(module, name)) {
                key(module, name)
            } else {
                match imports.and_then(|imports| imports.get(name)) {
                    Some(path) => normalize(path).to_owned(),
                    None => return Err(unresolved()),
                }
            }
        } else {
            let first = &ty.path[0];
            match imports.and_then(|imports| imports.get(first)) {
                Some(target) => format!("{}::{}", target, ty.path[1..].join("::")),
                None => ty.path.join("::"),
            }
        };
        let definition_key = normalize(&expanded);
        match self.defs.get(definition_key) {
            Some(Def::Struct(id)) => Ok(Ty::Struct(
                *id,
                self.structs[*id as usize].name.as_str().into(),
            )),
            Some(Def::Alias { .. }) => {
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
            Some(Def::Enum) => Err(failure(
                1,
                format!(
                    "enum type '{}' is not supported as a value type yet",
                    ty.path.join("::")
                ),
            )),
            None => Err(unresolved()),
        }
    }
}
