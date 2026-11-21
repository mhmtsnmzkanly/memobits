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
    Bytes,
    List,
    Option,
    Result,
    Attempt,
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
        name: "Array",
        parameters: &[ParameterKind::Type, ParameterKind::Integer],
        argument_error: "Array requires an element type and integer literal length",
    },
    Template {
        id: TemplateId::Bytes,
        name: "Bytes",
        parameters: &[ParameterKind::Integer],
        variants: &[],
        argument_error: "Bytes requires one integer literal length",
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
        name: "Option",
        parameters: &[ParameterKind::Type],
        argument_error: "Option requires one type argument",
    },
    Template {
        id: TemplateId::Result,
        name: "Result",
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
        argument_error: "Result requires two type arguments",
    },
    Template {
        id: TemplateId::Attempt,
        name: "Attempt",
        parameters: &[ParameterKind::Type, ParameterKind::ErrorType],
        variants: &[
            VariantTemplate {
                name: "Done",
                payload: &[0],
            },
            VariantTemplate {
                name: "Skipped",
                payload: &[],
            },
            VariantTemplate {
                name: "Failed",
                payload: &[1],
            },
        ],
        argument_error: "Attempt requires two type arguments",
    },
];

pub fn by_id(id: TemplateId) -> &'static Template {
    TEMPLATES
        .iter()
        .find(|template| template.id == id)
        .expect("registered compiler-known template")
}

pub fn lookup(path: &[String]) -> Option<&'static Template> {
    // Only the applied spellings Bytes<N> and List<T> are built in.
    // Bare names can still refer to a user-defined type or import.
    lookup_applied(path)
        .filter(|template| !matches!(template.id, TemplateId::Bytes | TemplateId::List))
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
        format!("{}<{}>", self.name, parameters.join(", "))
    }
}
