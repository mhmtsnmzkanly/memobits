//! Parameter contracts for compiler-known type templates. Instantiation remains
//! in the type table so arguments resolve through the same aliases and modules
//! as ordinary types. Register a template only when its implementation is ready.

use memobits_diagnostics::Span;
use memobits_syntax::{
    templates::{ParameterKind, Template},
    Type, TypeArgument,
};

use super::{typetable::TypeFailure, Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ResolvedArgument {
    Type(Ty),
    Integer(u32),
}

pub(super) fn unsupported_reference_argument(template: &Template, span: Span) -> TypeFailure {
    TypeFailure {
        span,
        code: 17,
        message: format!(
            "'{}' reference type arguments require embedded-loan tracking",
            template.annotation()
        ),
    }
}

/// Resolve aliases before an argument participates in instance identity.
pub(super) fn resolve_arguments(
    template: &Template,
    written: &Type,
    mut resolve_type: impl FnMut(ParameterKind, &Type) -> Result<Ty, TypeFailure>,
) -> Result<Vec<ResolvedArgument>, TypeFailure> {
    if written.arguments.len() != template.parameters.len() {
        return Err(TypeFailure {
            span: written.span,
            code: 2,
            message: template.argument_error.into(),
        });
    }
    written
        .arguments
        .iter()
        .zip(template.parameters)
        .map(|(argument, kind)| match (kind, argument) {
            (ParameterKind::Type | ParameterKind::ErrorType, TypeArgument::Type(ty)) => {
                resolve_type(*kind, ty).map(ResolvedArgument::Type)
            }
            (_, TypeArgument::Reference { span, .. }) => {
                Err(unsupported_reference_argument(template, *span))
            }
            (ParameterKind::Integer, TypeArgument::Integer(integer)) => integer
                .raw
                .replace('_', "")
                .parse::<u32>()
                .map(ResolvedArgument::Integer)
                .map_err(|_| TypeFailure {
                    span: integer.span,
                    code: 8,
                    message: "array length exceeds implementation limit u32::MAX".into(),
                }),
            _ => Err(TypeFailure {
                span: written.span,
                code: 2,
                message: template.argument_error.into(),
            }),
        })
        .collect()
}
