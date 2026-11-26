//! Pattern-matrix usefulness for `match`: unreachable arms and uncovered
//! example patterns (Maranget's algorithm over enum and tuple constructors).
use super::{name, MatchPattern, PatternLiteral, Ty};
use std::collections::BTreeSet;

/// A pattern reduced to what coverage cares about: a constructor with
/// sub-patterns, or anything else (`_` and bindings).
#[derive(Clone, Debug)]
pub(super) enum Pat {
    Wild,
    /// An enum variant index, `0` for the single constructor of a tuple, and
    /// `0`/`1` for `false`/`true`.
    Ctor(u32, Vec<Pat>),
    /// An integer, character or string literal: one value of an infinite
    /// domain, so literals alone never cover a type.
    Lit(PatternLiteral),
    /// `p | q`: expanded into separate rows as soon as it heads a column.
    Or(Vec<Pat>),
}

impl Pat {
    pub(super) fn from_fact(pattern: &MatchPattern) -> Pat {
        match pattern {
            MatchPattern::Wildcard | MatchPattern::Bind(_) => Pat::Wild,
            MatchPattern::Variant { variant, args } => {
                Pat::Ctor(*variant, args.iter().map(Pat::from_fact).collect())
            }
            MatchPattern::Tuple(args) => Pat::Ctor(0, args.iter().map(Pat::from_fact).collect()),
            MatchPattern::Literal(PatternLiteral::Bool(value)) => {
                Pat::Ctor(*value as u32, Vec::new())
            }
            MatchPattern::Literal(literal) => Pat::Lit(literal.clone()),
            MatchPattern::Or(alternatives) => {
                Pat::Or(alternatives.iter().map(Pat::from_fact).collect())
            }
        }
    }
}

/// The argument types of every constructor of a type, or `None` when the type
/// has no constructors patterns can name.
pub(super) type Signature<'a> = dyn Fn(&Ty) -> Option<Vec<Vec<Ty>>> + 'a;

/// An example value that no arm covers.
#[derive(Clone, Debug)]
pub(super) enum Witness {
    Wild,
    Ctor(Ty, u32, Vec<Witness>),
}

fn wilds(count: usize) -> Vec<Pat> {
    vec![Pat::Wild; count]
}

fn specialize(rows: &[Vec<Pat>], ctor: u32, arity: usize) -> Vec<Vec<Pat>> {
    rows.iter()
        .filter_map(|row| match &row[0] {
            Pat::Wild => Some([wilds(arity), row[1..].to_vec()].concat()),
            Pat::Ctor(found, args) if *found == ctor => {
                Some([args.clone(), row[1..].to_vec()].concat())
            }
            Pat::Ctor(..) | Pat::Lit(_) | Pat::Or(_) => None,
        })
        .collect()
}

/// Rows that match the literal `literal` in the first column (or any value).
fn specialize_literal(rows: &[Vec<Pat>], literal: &PatternLiteral) -> Vec<Vec<Pat>> {
    rows.iter()
        .filter_map(|row| match &row[0] {
            Pat::Wild => Some(row[1..].to_vec()),
            Pat::Lit(found) if found == literal => Some(row[1..].to_vec()),
            _ => None,
        })
        .collect()
}

/// Replace every row whose first column is an or-pattern by one row per
/// alternative.
fn expand_rows(rows: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    let mut expanded = Vec::new();
    for row in rows {
        if let Some(Pat::Or(alternatives)) = row.first() {
            for alternative in alternatives {
                let mut next = vec![alternative.clone()];
                next.extend_from_slice(&row[1..]);
                expanded.extend(expand_rows(&[next]));
            }
        } else {
            expanded.push(row.clone());
        }
    }
    expanded
}

fn default_rows(rows: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    rows.iter()
        .filter(|row| matches!(row[0], Pat::Wild))
        .map(|row| row[1..].to_vec())
        .collect()
}

fn used_constructors(rows: &[Vec<Pat>]) -> BTreeSet<u32> {
    rows.iter()
        .filter_map(|row| match &row[0] {
            Pat::Ctor(ctor, _) => Some(*ctor),
            Pat::Wild | Pat::Lit(_) | Pat::Or(_) => None,
        })
        .collect()
}

fn arguments_then_rest(arguments: &[Ty], rest: &[Ty]) -> Vec<Ty> {
    [arguments, rest].concat()
}

/// Is there a value matched by `pattern` and by none of `rows`?
pub(super) fn is_useful(
    signature: &Signature,
    rows: &[Vec<Pat>],
    pattern: &[Pat],
    types: &[Ty],
) -> bool {
    let Some((head, rest)) = pattern.split_first() else {
        return rows.is_empty();
    };
    let rows = &expand_rows(rows);
    if let Pat::Or(alternatives) = head {
        return alternatives.iter().any(|alternative| {
            is_useful(
                signature,
                rows,
                &[vec![alternative.clone()], rest.to_vec()].concat(),
                types,
            )
        });
    }
    if let Pat::Lit(literal) = head {
        return is_useful(
            signature,
            &specialize_literal(rows, literal),
            rest,
            &types[1..],
        );
    }
    let constructors = signature(&types[0]);
    match (head, constructors) {
        (Pat::Ctor(ctor, args), Some(constructors)) => {
            let Some(declared) = constructors.get(*ctor as usize) else {
                return false;
            };
            is_useful(
                signature,
                &specialize(rows, *ctor, args.len()),
                &[args.clone(), rest.to_vec()].concat(),
                &arguments_then_rest(declared, &types[1..]),
            )
        }
        (Pat::Wild, Some(constructors)) if used_constructors(rows).len() == constructors.len() => {
            constructors.iter().enumerate().any(|(ctor, declared)| {
                is_useful(
                    signature,
                    &specialize(rows, ctor as u32, declared.len()),
                    &[wilds(declared.len()), rest.to_vec()].concat(),
                    &arguments_then_rest(declared, &types[1..]),
                )
            })
        }
        _ => is_useful(signature, &default_rows(rows), rest, &types[1..]),
    }
}

/// Up to `limit` example value vectors that no row covers; empty when the
/// rows are exhaustive.
pub(super) fn missing(
    signature: &Signature,
    rows: &[Vec<Pat>],
    types: &[Ty],
    limit: usize,
) -> Vec<Vec<Witness>> {
    if limit == 0 {
        return Vec::new();
    }
    let rows = &expand_rows(rows);
    let Some((ty, rest_types)) = types.split_first() else {
        return if rows.is_empty() {
            vec![Vec::new()]
        } else {
            Vec::new()
        };
    };
    let Some(constructors) = signature(ty) else {
        return prefix(
            vec![Witness::Wild],
            missing(signature, &default_rows(rows), rest_types, limit),
            limit,
        );
    };
    // Every constructor in turn: a constructor some row names is explored
    // through its sub-patterns; an unnamed one is uncovered unless a
    // wildcard row (the default matrix) covers the remaining columns.
    let used = used_constructors(rows);
    let mut uncovered_rest: Option<Vec<Vec<Witness>>> = None;
    let mut found = Vec::new();
    for (ctor, declared) in constructors.iter().enumerate() {
        let remaining = limit - found.len();
        if remaining == 0 {
            break;
        }
        if used.contains(&(ctor as u32)) {
            for witness in missing(
                signature,
                &specialize(rows, ctor as u32, declared.len()),
                &arguments_then_rest(declared, rest_types),
                remaining,
            ) {
                let (arguments, rest) = witness.split_at(declared.len());
                let mut vector = vec![Witness::Ctor(ty.clone(), ctor as u32, arguments.to_vec())];
                vector.extend_from_slice(rest);
                found.push(vector);
            }
        } else {
            let rest = uncovered_rest
                .get_or_insert_with(|| missing(signature, &default_rows(rows), rest_types, limit));
            let head = if matches!(ty, Ty::Tuple(..)) {
                Witness::Wild
            } else {
                Witness::Ctor(ty.clone(), ctor as u32, vec![Witness::Wild; declared.len()])
            };
            found.extend(prefix(vec![head], rest.clone(), remaining));
        }
    }
    found
}

fn prefix(head: Vec<Witness>, rest: Vec<Vec<Witness>>, limit: usize) -> Vec<Vec<Witness>> {
    rest.into_iter()
        .take(limit)
        .map(|tail| [head.clone(), tail].concat())
        .collect()
}

/// The names a witness is printed with.
pub(super) trait ConstructorNames {
    /// `Enum::Variant` (or a bare variant for built-in and inline enums) of
    /// an enum constructor.
    fn variant_name(&self, ty: &Ty, variant: u32) -> String;
}

pub(super) fn render(witness: &Witness, names: &dyn ConstructorNames) -> String {
    match witness {
        Witness::Wild => "_".into(),
        Witness::Ctor(ty @ Ty::Box(_), variant, arguments) => render(
            &Witness::Ctor(ty.clone().unboxed(), *variant, arguments.clone()),
            names,
        ),
        Witness::Ctor(Ty::Primitive("bool"), value, _) => (*value == 1).to_string(),
        Witness::Ctor(ty @ Ty::Enum(..), variant, arguments) => {
            let name = names.variant_name(ty, *variant);
            if arguments.is_empty() {
                name
            } else {
                format!("{name}({})", render_all(arguments, names))
            }
        }
        Witness::Ctor(Ty::Tuple(..), _, arguments) => {
            if arguments.len() == 1 {
                format!("({},)", render(&arguments[0], names))
            } else {
                format!("({})", render_all(arguments, names))
            }
        }
        Witness::Ctor(ty, ..) => name(ty),
    }
}

fn render_all(witnesses: &[Witness], names: &dyn ConstructorNames) -> String {
    witnesses
        .iter()
        .map(|witness| render(witness, names))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Variant names read from the type table.
pub(super) struct TableNames<'a>(pub(super) &'a super::TypeTable);

impl ConstructorNames for TableNames<'_> {
    fn variant_name(&self, ty: &Ty, variant: u32) -> String {
        let Ty::Enum(id, _) = ty else {
            return name(ty);
        };
        let info = self.0.info(*id);
        let variant_name = info.variants[variant as usize].name.clone();
        // Built-in (`Some`, `Ok`, ...) and inline enum variants are written
        // bare; a declared enum's variants carry the enum name.
        if self.0.enum_template(*id).is_some() || info.module == "\0anonymous-enum" {
            variant_name
        } else {
            let base = info.name.split('<').next().unwrap_or(&info.name);
            format!("{base}::{variant_name}")
        }
    }
}
