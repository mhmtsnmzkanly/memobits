//! Compiler-known template shapes shared by parsing, name resolution and analysis.

use crate::Type;

#[derive(Clone, Copy)]
pub enum ParameterKind {
    Type,
    ErrorType,
    Integer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TemplateId {
    Array,
    List,
    Option,
    Result,
    Error,
    Utf8Error,
}

pub struct VariantTemplate {
    pub name: &'static str,
    /// Type-argument indices substituted into this variant's payload.
    pub payload: &'static [usize],
}

pub struct Template {
    pub id: TemplateId,
    pub name: &'static str,
    pub parameters: &'static [ParameterKind],
    pub variants: &'static [VariantTemplate],
    pub argument_error: &'static str,
}

const TEMPLATES: &[Template] = &[
    Template {
        id: TemplateId::Error,
        name: "Error",
        parameters: &[],
        variants: &[],
        argument_error: "Error does not accept type arguments",
    },
    Template {
        id: TemplateId::Utf8Error,
        name: "Utf8Error",
        parameters: &[],
        variants: &[],
        argument_error: "Utf8Error does not accept type arguments",
    },
    Template {
        id: TemplateId::Array,
        variants: &[],
        name: "array",
        parameters: &[ParameterKind::Type, ParameterKind::Integer],
        argument_error: "array requires an element type and integer literal length",
    },
    Template {
        id: TemplateId::List,
        name: "List",
        parameters: &[ParameterKind::Type],
        variants: &[],
        argument_error: "List requires one element type",
    },
    Template {
        id: TemplateId::Option,
        variants: &[
            VariantTemplate {
                name: "Some",
                payload: &[0],
            },
            VariantTemplate {
                name: "None",
                payload: &[],
            },
        ],
        name: "?",
        parameters: &[ParameterKind::Type],
        argument_error: "the optional type operator requires one type",
    },
    Template {
        id: TemplateId::Result,
        name: "!",
        parameters: &[ParameterKind::Type, ParameterKind::ErrorType],
        variants: &[
            VariantTemplate {
                name: "Ok",
                payload: &[0],
            },
            VariantTemplate {
                name: "Err",
                payload: &[1],
            },
        ],
        argument_error: "the fallible type operator requires a value type and an error type",
    },
];

pub fn by_id(id: TemplateId) -> &'static Template {
    TEMPLATES
        .iter()
        .find(|template| template.id == id)
        .expect("registered compiler-known template")
}

pub fn lookup(path: &[String]) -> Option<&'static Template> {
    // Only the applied spellings `array<T, N>` and `List<T>` are built in.
    // Bare names can still refer to a user-defined type or import.
    lookup_applied(path).filter(|template| template.id != TemplateId::List)
}

pub fn lookup_applied(path: &[String]) -> Option<&'static Template> {
    let [name] = path else { return None };
    TEMPLATES.iter().find(|template| template.name == name)
}

pub fn lookup_type(ty: &Type) -> Option<&'static Template> {
    if ty.arguments.is_empty() {
        lookup(&ty.path)
    } else {
        lookup_applied(&ty.path)
    }
}

/// Look up a short prelude variant and its index in the defining template.
pub fn variant(name: &str) -> Option<(&'static Template, usize)> {
    TEMPLATES
        .iter()
        .find_map(|template| template.variant_index(name).map(|index| (template, index)))
}

impl Template {
    pub fn variant_index(&self, name: &str) -> Option<usize> {
        self.variants
            .iter()
            .position(|variant| variant.name == name)
    }

    pub fn annotation(&self) -> String {
        let parameters: Vec<_> = self
            .parameters
            .iter()
            .map(|kind| match kind {
                ParameterKind::Type => "T",
                ParameterKind::ErrorType => "E",
                ParameterKind::Integer => "N",
            })
            .collect();
        match self.id {
            TemplateId::Option => "T?".into(),
            TemplateId::Result => "T ! E".into(),
            _ => format!("{}<{}>", self.name, parameters.join(", ")),
        }
    }
}

/// Replacement guidance for a type spelling that was removed from the language.
/// Type analysis reports it as TE001 when no user-defined type has that name.
pub fn removed_spelling_guidance(name: &str) -> Option<&'static str> {
    Some(match name {
        "Option" => "'Option<T>' is no longer a type; write 'T?' instead",
        "Result" => "'Result<T, E>' is no longer a type; write 'T ! E' instead",
        "Attempt" => "'Attempt<T, E>' is no longer a type; write 'T ?! E' instead",
        "Bool" => "'Bool' is no longer a type; write 'bool' instead",
        "Char" => "'Char' is no longer a type; write 'char' instead",
        "Array" => "'Array<T, N>' is no longer a type; write 'array<T, N>' instead",
        _ => return None,
    })
}

pub fn is_removed_spelling(name: &str) -> bool {
    removed_spelling_guidance(name).is_some()
}
