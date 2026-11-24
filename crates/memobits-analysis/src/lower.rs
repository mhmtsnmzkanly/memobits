//! Lower a successfully checked standalone primitive module to control-flow IR.
use std::collections::{HashMap, HashSet};

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    Access, ArrayInit, BinaryOp, Block as IrBlock, BlockId, CanonicalFunction, CanonicalType,
    Constant, Edge, FieldDef, Function, Instruction, InstructionKind, LoanId, Local, LocalId,
    Operand, Primitive, Program, Source, Terminator, TerminatorKind, Type, TypeDef, TypeDefKind,
    UnaryOp, UseMode, ValueId, VariantDef,
};
use memobits_project::Project;
use memobits_resolve::Resolution;
use memobits_syntax::{
    Block, Expr, ExprKind, FieldPattern, ItemKind, MatchArm, Module, Statement, StatementKind,
    TupleBinding,
};

mod arrays;
mod calls;
mod operations;
use operations::{binary_op, primitive_type, unary_op};

fn struct_field_index(definition: &TypeFact, name: &str) -> Option<usize> {
    definition
        .fields
        .iter()
        .position(|field| field.name == name)
        .or_else(|| {
            (definition.module == "\0tuple")
                .then(|| name.parse::<usize>().ok())
                .flatten()
                .filter(|index| *index < definition.fields.len())
        })
}

use crate::types::{
    check_resolved_mode, check_typed_module, CheckMode, ExprId, FunctionFacts, MatchFact,
    MatchPattern, PathTarget, SelectedCall, TypeFact, VariantUse,
};

/// IR type definitions for the checked structs. `module_path` names the module
/// of a standalone definition (whose fact module is empty).
fn program_types(
    structs: &[TypeFact],
    package: &str,
    module_of: impl Fn(&str) -> Vec<String>,
) -> Vec<TypeDef> {
    structs
        .iter()
        .map(|definition| TypeDef {
            path: CanonicalType {
                package: package.into(),
                module: if matches!(
                    definition.module.as_str(),
                    "\0tuple" | "\0record" | "\0anonymous-enum"
                ) {
                    vec![definition.module.clone()]
                } else if definition.module == "__prelude" {
                    vec![definition.module.clone()]
                } else {
                    module_of(&definition.module)
                },
                name: definition.name.clone(),
            },
            span: definition.span,
            error_ancestry: definition.error_ancestry,
            entry_outcome: definition.entry_outcome,
            kind: if definition.is_enum {
                TypeDefKind::Enum {
                    variants: definition
                        .variants
                        .iter()
                        .map(|variant| VariantDef {
                            name: variant.name.clone(),
                            payload: variant.payload.clone(),
                        })
                        .collect(),
                }
            } else {
                TypeDefKind::Struct {
                    fields: definition
                        .fields
                        .iter()
                        .map(|field| FieldDef {
                            name: field.name.clone(),
                            ty: field.ty.clone(),
                        })
                        .collect(),
                }
            },
        })
        .collect()
}
fn error(span: Span, message: impl Into<String>) -> Diagnostic {
    let mut d = Diagnostic::new(
        DiagnosticCode::new(Category::Type, 18).expect("static TE code"),
        Severity::Error,
        message,
    );
    d.span = Some(span);
    d
}

/// Lower a checked standalone module to validated typed IR.
///
/// `package` and `module_path` name the definitions in the resulting program.
/// Type and control-flow errors are returned as diagnostics. Ownership is checked
/// separately with `memobits_ownership::check_moves`.
pub fn lower_module(
    module: &Module,
    package: &str,
    module_path: &[String],
) -> Result<Program, Vec<Diagnostic>> {
    let facts = check_typed_module(module)?;
    let constant_errors = crate::constants::check_module(module, &facts.functions);
    if !constant_errors.is_empty() {
        return Err(constant_errors);
    }
    let mut diagnostics = Vec::new();
    if package.is_empty() || module_path.is_empty() || module_path.iter().any(String::is_empty) {
        let span = module.items.first().map(|i| i.span).unwrap_or(Span {
            source: memobits_diagnostics::SourceId(0),
            start: 0,
            end: 0,
        });
        diagnostics.push(error(span, "package and module path must be nonempty"));
        return Err(diagnostics);
    }
    let mut functions = Vec::new();
    for (item, fact) in module
        .items
        .iter()
        .filter(|i| matches!(i.kind, ItemKind::Function { .. }))
        .zip(&facts.functions)
    {
        let ItemKind::Function {
            name,
            body,
            parameters,
            ..
        } = &item.kind
        else {
            unreachable!()
        };
        let function = Function {
            path: CanonicalFunction {
                package: package.into(),
                module: module_path.to_vec(),
                name: name.clone(),
            },
            span: item.span,
            signature: fact.signature.clone(),
            parameter_locals: fact
                .locals
                .iter()
                .take(parameters.len())
                .map(|l| l.id)
                .collect(),
            locals: fact
                .locals
                .iter()
                .map(|l| Local {
                    name: l.name.clone(),
                    ty: l.ty.clone(),
                    mutable: l.mutable,
                    span: l.span,
                })
                .collect(),
            values: Vec::new(),
            blocks: vec![IrBlock {
                parameters: Vec::new(),
                instructions: Vec::new(),
                terminator: Terminator {
                    span: None,
                    kind: TerminatorKind::Unreachable,
                },
            }],
            entry: BlockId(0),
        };
        let mut builder = Builder::new(function, fact, &facts.types);
        builder.lower_body(body);
        functions.push(builder.function);
    }
    let program = Program {
        functions,
        types: program_types(&facts.types, package, |_| module_path.to_vec()),
    };
    if let Err(errors) = program.validate() {
        for failure in errors {
            let span = failure
                .function
                .and_then(|id| program.functions.get(id.0 as usize))
                .map_or_else(
                    || {
                        module.items.first().map(|i| i.span).unwrap_or(Span {
                            source: memobits_diagnostics::SourceId(0),
                            start: 0,
                            end: 0,
                        })
                    },
                    |f| f.span,
                );
            diagnostics.push(error(
                span,
                format!("IR lowering failed validation: {}", failure.message),
            ));
        }
    }
    if diagnostics.is_empty() {
        Ok(program)
    } else {
        Err(diagnostics)
    }
}

/// Lower all modules retained by a successful target-rooted resolution.
/// Function IDs follow the sorted module and source function order used by the
/// typed facts, so calls preserve canonical identity across module boundaries.
pub fn lower_resolved(
    project: &Project,
    resolution: &Resolution,
) -> Result<Program, Vec<Diagnostic>> {
    let typed = check_resolved_mode(project, resolution, CheckMode::Execution)?;
    for (module_name, source) in &resolution.modules {
        for item in &source.syntax.items {
            let ItemKind::Function {
                external: true,
                name,
                generic_parameters,
                parameters,
                result,
                ..
            } = &item.kind
            else {
                continue;
            };
            let root_module = project
                .manifest
                .package
                .entry
                .as_deref()
                .unwrap_or("")
                .split("::")
                .next()
                .unwrap_or("");
            let signature_matches = generic_parameters.is_empty()
                && parameters.len() == 1
                && !parameters[0].mutable
                && parameters[0].access == memobits_syntax::Access::Owned
                && parameters[0].ty.path.len() == 1
                && parameters[0].ty.path[0] == "i32"
                && parameters[0].ty.arguments.is_empty()
                && result.is_none();
            let declared = project
                .manifest
                .host
                .as_ref()
                .is_some_and(|host| host.imports.iter().any(|import| import.name == *name));
            if module_name != root_module || !signature_matches || !declared {
                return Err(vec![error(
                    item.span,
                    format!(
                        "external function '{name}' must be declared in the application root as `extern fn write_i32(value: i32);` and match [host.imports]"
                    ),
                )]);
            }
        }
    }
    let mut constant_errors = Vec::new();
    for (module_name, source) in &resolution.modules {
        let module_facts = typed
            .functions
            .iter()
            .filter(|facts| facts.source_module == *module_name)
            .cloned()
            .collect::<Vec<_>>();
        constant_errors.extend(crate::constants::check_module(
            &source.syntax,
            &module_facts,
        ));
    }
    if !constant_errors.is_empty() {
        return Err(constant_errors);
    }
    let mut functions = Vec::with_capacity(typed.functions.len());
    for fact in &typed.functions {
        let Some(source) = resolution.modules.get(&fact.source_module) else {
            return Err(vec![error(
                fact.span,
                "typed fact refers to an unknown source module",
            )]);
        };
        let module_name = &fact.source_module;
        let module_path = module_name
            .split("::")
            .map(str::to_owned)
            .collect::<Vec<_>>();
        if fact.id.0 as usize != functions.len() {
            return Err(vec![error(
                fact.span,
                "typed project function ID differs from canonical program order",
            )]);
        }
        let source_function = source.syntax.items.iter().find_map(|item| {
            if item.span != fact.span {
                return None;
            }
            if let ItemKind::Function {
                external,
                name,
                body,
                parameters,
                ..
            } = &item.kind
            {
                (name == &fact.source_name).then_some((
                    name.as_str(),
                    body,
                    parameters.len(),
                    *external,
                ))
            } else {
                None
            }
        });
        let (ir_name, body, parameter_count, external) =
            if let Some((name, body, count, external)) = source_function {
                let ir_name = fact.specialization_key.as_ref().map_or_else(
                    || name.to_owned(),
                    |_| format!("{name}$specialization${}", fact.id.0),
                );
                (ir_name, body, count, external)
            } else {
                let extension = source.syntax.items.iter().find_map(|item| {
                    let (interface, methods) = match &item.kind {
                        ItemKind::Extension {
                            interface, methods, ..
                        } => (Some(interface), methods),
                        ItemKind::InherentExtension { methods, .. } => (None, methods),
                        _ => return None,
                    };
                    methods
                        .iter()
                        .find(|method| method.span == fact.span && method.name == fact.source_name)
                        .and_then(|method| method.body.as_ref())
                        .map(|body| {
                            let name = interface.map_or_else(
                                || inherent_function_name(item.span.start, &fact.source_name),
                                |interface| {
                                    extension_function_name(
                                        module_name,
                                        item.span.start,
                                        interface,
                                        &fact.source_name,
                                    )
                                },
                            );
                            let name =
                                fact.specialization_key.as_ref().map_or(name.clone(), |_| {
                                    format!("{name}$specialization${}", fact.id.0)
                                });
                            (
                                name,
                                body,
                                methods
                                    .iter()
                                    .find(|m| m.span == fact.span)
                                    .unwrap()
                                    .parameters
                                    .len()
                                    + 1,
                                false,
                            )
                        })
                });
                let Some(extension) = extension else {
                    return Err(vec![error(
                        fact.span,
                        "typed fact has no source function body",
                    )]);
                };
                extension
            };
        let (module_path, ir_name) = if external {
            let Some(import) = project
                .manifest
                .host
                .as_ref()
                .and_then(|host| host.imports.iter().find(|import| import.name == ir_name))
            else {
                return Err(vec![error(
                    fact.span,
                    format!(
                        "external function '{ir_name}' has no matching [host.imports] declaration"
                    ),
                )]);
            };
            if module_name
                != project
                    .manifest
                    .package
                    .entry
                    .as_deref()
                    .unwrap_or("")
                    .split("::")
                    .next()
                    .unwrap_or("")
            {
                // External declarations are project-level ABI names, so only
                // the target root may bind the manifest capability.
                return Err(vec![error(
                    fact.span,
                    "host imports must be declared in the application entry module",
                )]);
            }
            (
                vec![
                    memobits_ir::HOST_IMPORT_MODULE.to_owned(),
                    import.module.clone(),
                ],
                import.name.clone(),
            )
        } else {
            (module_path, ir_name)
        };
        let function = Function {
            path: CanonicalFunction {
                package: project.manifest.package.name.clone(),
                module: module_path,
                name: ir_name,
            },
            span: fact.span,
            signature: fact.signature.clone(),
            parameter_locals: fact
                .locals
                .iter()
                .take(parameter_count)
                .map(|local| local.id)
                .collect(),
            locals: fact
                .locals
                .iter()
                .map(|local| Local {
                    name: local.name.clone(),
                    ty: local.ty.clone(),
                    mutable: local.mutable,
                    span: local.span,
                })
                .collect(),
            values: Vec::new(),
            blocks: vec![IrBlock {
                parameters: Vec::new(),
                instructions: Vec::new(),
                terminator: Terminator {
                    span: None,
                    kind: TerminatorKind::Unreachable,
                },
            }],
            entry: BlockId(0),
        };
        let mut builder = Builder::new(function, fact, &typed.types);
        if !external {
            builder.lower_body(body);
        } else {
            builder.set_terminator(BlockId(0), TerminatorKind::Return(None), Some(fact.span));
        }
        functions.push(builder.function);
    }
    let program = Program {
        functions,
        types: program_types(&typed.types, &project.manifest.package.name, |module| {
            module.split("::").map(str::to_owned).collect()
        }),
    };
    if let Err(errors) = program.validate() {
        let fallback = program
            .functions
            .first()
            .map(|function| function.span)
            .unwrap_or(Span {
                source: memobits_diagnostics::SourceId(0),
                start: 0,
                end: 0,
            });
        return Err(errors
            .into_iter()
            .map(|failure| {
                error(
                    failure
                        .function
                        .and_then(|id| program.functions.get(id.0 as usize))
                        .map_or(fallback, |f| f.span),
                    format!("IR lowering failed validation: {}", failure.message),
                )
            })
            .collect());
    }
    Ok(program)
}

fn consume(mut operand: Operand) -> Operand {
    if !matches!(operand.source, Source::Function(_)) {
        operand.mode = UseMode::Consume;
    }
    operand
}
fn extension_function_name(
    _module: &str,
    declaration_start: usize,
    interface: &memobits_syntax::Type,
    method: &str,
) -> String {
    format!(
        "__extension_{}_{}_{}",
        interface.path.join("_"),
        method,
        declaration_start
    )
}
fn inherent_function_name(declaration_start: usize, method: &str) -> String {
    format!("__inherent_{method}_{declaration_start}")
}
fn read(mut operand: Operand) -> Operand {
    operand.mode = UseMode::Read;
    operand
}
fn op(source: Source, span: Span) -> Operand {
    Operand {
        source,
        mode: UseMode::Read,
        span: Some(span),
    }
}
/// One step of a place: an indexed element (its position already evaluated and
/// captured) or a named field.
enum Projection {
    Index(Operand, bool),
    Field(String),
    FieldSlot(u32),
}
/// A pattern that tests nothing: `_`, a binding, or a tuple of such.
fn irrefutable_pattern(pattern: &MatchPattern) -> bool {
    match pattern {
        MatchPattern::Wildcard | MatchPattern::Bind(_) => true,
        // A tuple has one constructor: it tests nothing by itself.
        MatchPattern::Tuple(args) => args.iter().all(irrefutable_pattern),
        MatchPattern::Variant { .. } => false,
    }
}
static MATCH_WILDCARD: MatchPattern = MatchPattern::Wildcard;
/// One row of the match pattern matrix: the arm and its remaining patterns,
/// one per occurrence still to inspect.
#[derive(Clone)]
struct MatchRow<'p> {
    arm: usize,
    patterns: Vec<&'p MatchPattern>,
}
impl<'p> MatchRow<'p> {
    /// The row with its pattern at `column` replaced by `replacement`.
    fn replacing(&self, column: usize, replacement: Vec<&'p MatchPattern>) -> Self {
        let mut patterns = self.patterns.clone();
        patterns.splice(column..=column, replacement);
        Self {
            arm: self.arm,
            patterns,
        }
    }
}
/// What the leaves of one match's decision tree need.
struct MatchPlan<'p> {
    arms: &'p [crate::types::MatchArmFact],
    /// The block of each arm's body, entered from its leaves.
    bodies: Vec<BlockId>,
    /// The hidden owner of a consuming match.
    owner: Option<LocalId>,
    /// The local the decision phase reads: the owner, or a reference.
    root: LocalId,
    root_ty: Type,
}
/// A value a match still inspects: a local holding a reference to it.
#[derive(Clone)]
struct MatchOccurrence {
    reference: LocalId,
    ty: Type,
    /// `reference` is the consuming match's owner itself, not a reference to
    /// it: its tag is read in place, as the ownership validator expects.
    direct_owner: bool,
}
struct LoopTargets {
    header: BlockId,
    exit: BlockId,
    had_break: bool,
    scope_start: usize,
    iterable_loan: Option<Operand>,
}
struct Builder<'a> {
    function: Function,
    facts: &'a FunctionFacts,
    types: &'a [TypeFact],
    expression_ids: HashMap<usize, ExprId>,
    expressions: HashMap<ExprId, Option<Type>>,
    paths: HashMap<ExprId, PathTarget>,
    variants: HashMap<ExprId, VariantUse>,
    explicit_drops: HashSet<ExprId>,
    explicit_asserts: HashSet<ExprId>,
    explicit_replaces: HashSet<ExprId>,
    explicit_swaps: HashSet<ExprId>,
    selected_calls: HashMap<ExprId, SelectedCall>,
    selected_operators: HashMap<ExprId, SelectedCall>,
    selected_assignments: HashMap<ExprId, SelectedCall>,
    matches: HashMap<ExprId, &'a MatchFact>,
    tuple_projections: HashMap<usize, u32>,
    tuple_initializers: HashMap<usize, Vec<u32>>,
    current: Option<BlockId>,
    owned_locals: Vec<LocalId>,
    loops: Vec<LoopTargets>,
    next_loan: u32,
    /// Values produced by `Load`: read-only provenance that must be copied
    /// before it can be used as an owned value.
    loaded: HashSet<u32>,
}

fn is_string_tuple_type(types: &[TypeFact], ty: &Type) -> bool {
    fn contains_owned_string(types: &[TypeFact], ty: &Type, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Type::String => true,
            Type::Struct(id) => {
                let Some(info) = types.get(id.0 as usize) else {
                    return false;
                };
                if info.module != "\0tuple" || !visited.insert(id.0) {
                    return false;
                }
                let owns = info
                    .fields
                    .iter()
                    .any(|field| contains_owned_string(types, &field.ty, visited));
                visited.remove(&id.0);
                owns
            }
            _ => false,
        }
    }
    matches!(ty, Type::Struct(id)
        if types.get(id.0 as usize).is_some_and(|info| info.module == "\0tuple")
            && contains_owned_string(types, ty, &mut HashSet::new()))
}

/// Nominal String-owning struct (flat or nested), classified by the shared
/// memobits-ir rule; the recursion and visited set live here because
/// `TypeFact` is this crate's type model.
fn is_flat_string_owner_struct_type(types: &[TypeFact], ty: &Type) -> bool {
    fn admitted(types: &[TypeFact], id: u32, visited: &mut HashSet<u32>) -> bool {
        use memobits_ir::OwnerFieldShape as Shape;
        let Some(info) = types.get(id as usize) else {
            return false;
        };
        if info.module == "\0tuple" || info.is_enum || !visited.insert(id) {
            return false;
        }
        fn shape(types: &[TypeFact], ty: &Type, visited: &mut HashSet<u32>) -> Shape {
            match ty {
                Type::String => Shape::String,
                Type::Primitive(_) => Shape::Primitive,
                Type::Struct(child) if admitted(types, child.0, visited) => Shape::Owner,
                Type::Array { element, len } if *len != 0 => match shape(types, element, visited) {
                    Shape::Owner => Shape::Owner,
                    _ => Shape::Other,
                },
                _ => Shape::Other,
            }
        }
        let fields: Vec<Shape> = info
            .fields
            .iter()
            .map(|field| shape(types, &field.ty, visited))
            .collect();
        visited.remove(&id);
        memobits_ir::is_string_owner_struct(info.error_ancestry.is_some(), fields)
    }
    let Type::Struct(id) = ty else {
        return false;
    };
    admitted(types, id.0, &mut HashSet::new())
}

fn is_string_owner_aggregate_type(types: &[TypeFact], ty: &Type) -> bool {
    fn owns(types: &[TypeFact], ty: &Type, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Type::String => true,
            Type::Array { element, len } => *len != 0 && owns(types, element, visited),
            Type::Struct(id) | Type::Enum(id) => {
                let Some(info) = types.get(id.0 as usize) else {
                    return false;
                };
                if !visited.insert(id.0) {
                    return false;
                }
                let result = info
                    .fields
                    .iter()
                    .any(|field| owns(types, &field.ty, visited))
                    || info
                        .variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|field| owns(types, field, visited));
                visited.remove(&id.0);
                result
            }
            _ => false,
        }
    }
    matches!(ty, Type::Array { .. } | Type::Struct(_) | Type::Enum(_))
        && owns(types, ty, &mut HashSet::new())
}

impl<'a> Builder<'a> {
    fn new(function: Function, facts: &'a FunctionFacts, types: &'a [TypeFact]) -> Self {
        let expression_ids = facts
            .expressions
            .iter()
            .map(|f| (f.node_addr, f.id))
            .collect();
        let expressions = facts
            .expressions
            .iter()
            .map(|f| (f.id, f.ty.clone()))
            .collect();
        let paths = facts
            .path_uses
            .iter()
            .map(|u| (u.expression, u.target))
            .collect();
        let variants = facts
            .variant_uses
            .iter()
            .map(|u| (u.expression, *u))
            .collect();
        let matches = facts.matches.iter().map(|m| (m.expression, m)).collect();
        let tuple_projections = facts
            .tuple_projections
            .iter()
            .map(|fact| (fact.node_addr, fact.slot))
            .collect();
        let tuple_initializers = facts
            .tuple_initializers
            .iter()
            .map(|fact| (fact.node_addr, fact.slots.clone()))
            .collect();
        let selected_calls = facts
            .selected_calls
            .iter()
            .cloned()
            .map(|call| (call.expression, call))
            .collect();
        let selected_operators = facts
            .selected_operators
            .iter()
            .cloned()
            .map(|operator| (operator.expression, operator))
            .collect();
        let selected_assignments = facts
            .selected_assignments
            .iter()
            .cloned()
            .map(|assignment| (assignment.expression, assignment))
            .collect();
        let owned_locals = function
            .parameter_locals
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(position, local)| {
                let parameter = function.signature.parameters.get(position)?;
                let ty = &function.locals[local.0 as usize].ty;
                (parameter.access == Access::Owned
                    && (matches!(ty, Type::String | Type::List(_))
                        || is_string_owner_aggregate_type(types, ty)))
                .then_some(local)
            })
            .collect();
        Self {
            function,
            facts,
            types,
            expression_ids,
            expressions,
            paths,
            variants,
            explicit_drops: facts.explicit_drops.iter().copied().collect(),
            explicit_asserts: facts.explicit_asserts.iter().copied().collect(),
            explicit_replaces: facts.explicit_replaces.iter().copied().collect(),
            explicit_swaps: facts.explicit_swaps.iter().copied().collect(),
            selected_calls,
            selected_operators,
            selected_assignments,
            matches,
            tuple_projections,
            tuple_initializers,
            current: Some(BlockId(0)),
            owned_locals,
            loops: Vec::new(),
            next_loan: 0,
            loaded: HashSet::new(),
        }
    }
    fn id(&self, expr: &Expr) -> ExprId {
        self.expression_ids[&(expr as *const Expr as usize)]
    }
    fn ty(&self, expr: &Expr) -> Option<Type> {
        self.expressions[&self.id(expr)].clone()
    }
    fn path(&self, expr: &Expr) -> PathTarget {
        self.paths[&self.id(expr)]
    }
    /// Whole-value destructuring. The initialiser is lowered once. Every field
    /// is then read out of that value with `Extract` (a primitive is copied, an
    /// aggregate field is moved by a bitwise copy) and assigned to its own
    /// local, in pattern order. The last extraction takes the whole value with
    /// `Consume`, so the ownership pass sees the source consumed exactly once
    /// (a source local becomes unavailable, BE001 on later use). A struct with no
    /// fields is consumed by a capture instead.
    fn lower_destructure(&mut self, fields: &[FieldPattern], value: &Expr) {
        let Some(source) = self.lower_expr(value) else {
            return;
        };
        let Some(Type::Struct(id)) = self.operand_type(source) else {
            unreachable!("checked destructuring source");
        };
        let types = self.types;
        let definition = &types[id.0 as usize];
        if fields.is_empty() {
            self.capture_consumed(source);
            return;
        }
        for (position, pattern) in fields.iter().enumerate() {
            let index = definition
                .fields
                .iter()
                .position(|field| field.name == pattern.field)
                .expect("checked destructuring field");
            let field_ty = definition.fields[index].ty.clone();
            let mut base = source;
            base.mode = if position + 1 == fields.len() {
                UseMode::Consume
            } else {
                UseMode::Read
            };
            let Some(extracted) = self.emit(
                pattern.span,
                InstructionKind::Extract {
                    base,
                    field: index as u32,
                },
                Some(field_ty),
            ) else {
                return;
            };
            let target = self.local_at(pattern as *const FieldPattern as usize);
            self.initialize_local(target, consume(extracted), pattern.span);
        }
    }
    /// Tuple patterns bind or discard every slot, then recursively destructure
    /// staged nested tuple locals. This keeps each source extraction ordered
    /// and gives owning discard slots an ordinary local cleanup path.
    fn lower_tuple_destructure(&mut self, elements: &[TupleBinding], value: &Expr) {
        let Some(source) = self.lower_expr(value) else {
            return;
        };
        let Some(ty @ Type::Struct(_)) = self.operand_type(source) else {
            unreachable!("checked tuple destructuring source");
        };
        self.lower_tuple_patterns(elements, source, ty);
    }
    fn lower_tuple_patterns(&mut self, elements: &[TupleBinding], source: Operand, ty: Type) {
        let Type::Struct(id) = ty else {
            unreachable!("checked nested tuple pattern");
        };
        let moved_string_tuple = self
            .is_string_tuple(&Type::Struct(id))
            .then_some(source.source)
            .and_then(|source| match source {
                Source::Local(local) => Some(local),
                _ => None,
            });
        if elements.is_empty() {
            self.capture_consumed(source);
            if let Some(local) = moved_string_tuple {
                self.owned_locals.retain(|owned| *owned != local);
            }
            return;
        }
        let definition = &self.types[id.0 as usize];
        let mut nested = Vec::new();
        for (index, element) in elements.iter().enumerate() {
            let field_ty = definition.fields[index].ty.clone();
            let mut base = source;
            base.mode = if index + 1 == elements.len() {
                UseMode::Consume
            } else {
                UseMode::Read
            };
            let Some(extracted) = self.emit(
                element.span,
                InstructionKind::Extract {
                    base,
                    field: index as u32,
                },
                Some(field_ty.clone()),
            ) else {
                return;
            };
            let target = self.local_at(element as *const TupleBinding as usize);
            self.initialize_local(target, consume(extracted), element.span);
            if let Some(pattern) = &element.nested {
                nested.push((pattern.as_slice(), target, field_ty));
            }
        }
        for (pattern, source, ty) in nested {
            self.lower_tuple_patterns(pattern, op(Source::Local(source), self.function.span), ty);
        }
        if let Some(local) = moved_string_tuple {
            self.owned_locals.retain(|owned| *owned != local);
        }
    }
    fn capture_consumed(&mut self, source: Operand) {
        if matches!(source.source, Source::Local(_)) {
            self.emit(
                source.span.unwrap_or(self.function.span),
                InstructionKind::Capture(consume(source)),
                self.operand_type(source),
            );
        }
    }
    fn local_at(&self, addr: usize) -> LocalId {
        self.facts
            .locals
            .iter()
            .find(|l| l.node_addr == addr)
            .expect("checked binding fact")
            .id
    }
    fn local(&self, statement: &Statement) -> LocalId {
        self.facts
            .locals
            .iter()
            .find(|l| l.node_addr == statement as *const Statement as usize)
            .expect("checked binding fact")
            .id
    }
    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.function.blocks.len() as u32);
        self.function.blocks.push(IrBlock {
            parameters: Vec::new(),
            instructions: Vec::new(),
            terminator: Terminator {
                span: None,
                kind: TerminatorKind::Unreachable,
            },
        });
        id
    }
    fn new_value(&mut self, ty: Type) -> ValueId {
        let id = ValueId(self.function.values.len() as u32);
        self.function.values.push(ty);
        id
    }
    fn emit(&mut self, span: Span, kind: InstructionKind, ty: Option<Type>) -> Option<Operand> {
        let current = self.current?;
        let output = ty.map(|ty| self.new_value(ty));
        self.function.blocks[current.0 as usize]
            .instructions
            .push(Instruction {
                span: Some(span),
                output,
                kind,
            });
        output.map(|id| op(Source::Value(id), span))
    }
    fn constant(&mut self, span: Span, value: Constant, ty: Type) -> Option<Operand> {
        self.emit(span, InstructionKind::Constant(value), Some(ty))
    }
    fn unit(&mut self, span: Span) -> Option<Operand> {
        self.constant(span, Constant::Unit, Type::Primitive(Primitive::Unit))
    }
    fn operand_type(&self, operand: Operand) -> Option<Type> {
        match operand.source {
            Source::Local(id) => Some(self.function.locals[id.0 as usize].ty.clone()),
            Source::Value(id) => Some(self.function.values[id.0 as usize].clone()),
            Source::Function(_) => None,
        }
    }
    fn scalar(&mut self, mut operand: Operand) -> Option<Operand> {
        if let Some(Type::Reference { access, inner }) = self.operand_type(operand) {
            operand.mode = access_mode(access);
            let span = operand.span.unwrap_or(self.function.span);
            self.load(operand, *inner, span)
        } else {
            Some(operand)
        }
    }
    fn load(&mut self, reference: Operand, inner: Type, span: Span) -> Option<Operand> {
        let value = self.emit(span, InstructionKind::Load { reference }, Some(inner))?;
        if let Source::Value(id) = value.source {
            self.loaded.insert(id.0);
        }
        Some(value)
    }
    /// Operand for an owned position. Primitive locals and loaded primitives
    /// (read-only provenance) are copied implicitly into a fresh owned value
    /// with an IR `Copy`, which only reads its source. Other temporaries and
    /// aggregates are consumed (moved).
    fn owned(&mut self, operand: Operand) -> Option<Operand> {
        let primitive = matches!(
            self.operand_type(operand),
            Some(Type::Primitive(kind)) if kind != Primitive::Unit
        );
        match operand.source {
            Source::Local(_) if primitive => self.copy_of(operand),
            Source::Value(id) if primitive && self.loaded.contains(&id.0) => self.copy_of(operand),
            _ => Some(consume(operand)),
        }
    }
    fn copy_of(&mut self, operand: Operand) -> Option<Operand> {
        let ty = self.operand_type(operand);
        let span = operand.span.unwrap_or(self.function.span);
        let copy = self.emit(
            span,
            InstructionKind::Copy {
                source: read(operand),
            },
            ty,
        )?;
        Some(consume(copy))
    }
    /// `owned` for a destination of type `target`: a reference read into a
    /// non-reference destination is loaded first (the checker only allows this
    /// for primitive referents).
    fn owned_to(&mut self, operand: Operand, target: &Type) -> Option<Operand> {
        let operand = if matches!(target, Type::Reference { .. }) {
            operand
        } else {
            self.scalar(operand)?
        };
        self.owned(operand)
    }
    /// `owned_to` followed by a capture, so locals are read in source order.
    fn owned_captured(&mut self, operand: Operand, target: &Type) -> Option<Operand> {
        let operand = self.owned_to(operand, target)?;
        Some(consume(self.capture(operand)?))
    }
    fn is_string_tuple(&self, ty: &Type) -> bool {
        is_string_tuple_type(self.types, ty)
    }
    /// Aggregates admitted for by-value transport (tuples and flat nominal structs).
    fn is_string_transport_owner(&self, ty: &Type) -> bool {
        is_string_tuple_type(self.types, ty) || is_flat_string_owner_struct_type(self.types, ty)
    }
    /// Evaluate one element expression that moves into an array or List.
    fn owned_element(&mut self, element: &Expr, element_ty: &Type) -> Option<Operand> {
        let value = self.lower_expr(element)?;
        if self.is_string_transport_owner(element_ty)
            || (matches!(element_ty, Type::Enum(_))
                && self.is_string_owner_struct(element_ty)
                && !matches!(value.source, Source::Local(_)))
        {
            // An owner element (literal or call result) is staged in a hidden
            // local first, as for tuple elements, so its construction has a
            // direct binding.
            let value = self.owned_to(value, element_ty)?;
            let staged = self.hidden_local("owner element", element_ty.clone(), element.span);
            self.initialize_local(staged, value, element.span);
            return Some(consume(op(Source::Local(staged), element.span)));
        }
        // Capture locals now so every element is read in source order.
        self.owned_captured(value, element_ty)
    }

    /// `[a, b, c]` with an expected `List<T>`: a hidden List local that starts
    /// empty and takes each element in written order.
    fn lower_list_literal(
        &mut self,
        expr: &Expr,
        elements: &[Expr],
        list_ty: Type,
    ) -> Option<Operand> {
        let Type::List(element_ty) = &list_ty else {
            unreachable!("checked List literal type")
        };
        let element_ty = element_ty.as_ref().clone();
        let empty = self.emit(expr.span, InstructionKind::EmptyList, Some(list_ty.clone()))?;
        if elements.is_empty() {
            return Some(empty);
        }
        let list = self.hidden_local("list literal", list_ty, expr.span);
        self.initialize_local(list, consume(empty), expr.span);
        for element in elements {
            let value = if matches!(element_ty, Type::Primitive(_)) {
                let value = self.lower_expr(element)?;
                read(self.scalar(value)?)
            } else {
                self.owned_element(element, &element_ty)?
            };
            self.emit(
                element.span,
                InstructionKind::ListPush {
                    target: list,
                    value,
                },
                None,
            );
        }
        Some(consume(op(Source::Local(list), expr.span)))
    }

    fn is_string_owner_struct(&self, ty: &Type) -> bool {
        is_string_owner_aggregate_type(self.types, ty)
    }
    fn borrow(&mut self, mut owner: Operand, access: Access) -> Option<Operand> {
        let ty = self.operand_type(owner).expect("checked borrow source");
        let inner = match ty {
            Type::Reference { inner, .. } => inner,
            ty => Box::new(ty),
        };
        owner.mode = access_mode(access);
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        self.emit(
            owner.span.unwrap_or(self.function.span),
            InstructionKind::Borrow {
                loan,
                owner,
                access,
            },
            Some(Type::Reference { access, inner }),
        )
    }
    fn capture(&mut self, operand: Operand) -> Option<Operand> {
        if !matches!(operand.source, Source::Local(_)) {
            return Some(operand);
        }
        let ty = match operand.source {
            Source::Local(local) => self.function.locals[local.0 as usize].ty.clone(),
            _ => unreachable!(),
        };
        let span = operand.span.unwrap_or(self.function.span);
        self.emit(
            span,
            InstructionKind::Capture(if matches!(ty, Type::Reference { .. }) {
                consume(operand)
            } else {
                operand
            }),
            Some(ty),
        )
    }
    fn use_iteration_loans(&mut self) {
        // An iteration loan is lexical. Give it a use at every body block's
        // end, including paths that break, return, or never reach a backedge.
        for index in 0..self.loops.len() {
            if let Some(receiver) = self.loops[index].iterable_loan {
                self.borrow(receiver, Access::Borrow);
            }
        }
    }

    fn finish(&mut self, block: BlockId, kind: TerminatorKind, span: Option<Span>) {
        self.use_iteration_loans();
        self.set_terminator(block, kind, span);
    }

    fn set_terminator(&mut self, block: BlockId, kind: TerminatorKind, span: Option<Span>) {
        self.function.blocks[block.0 as usize].terminator = Terminator { span, kind };
        if self.current == Some(block) {
            self.current = None;
        }
    }
    fn goto(&mut self, target: BlockId, arguments: Vec<Operand>, span: Span) {
        if let Some(current) = self.current {
            self.finish(
                current,
                TerminatorKind::Goto(Edge { target, arguments }),
                Some(span),
            );
        }
    }
    fn initialize_local(&mut self, local: LocalId, value: Operand, span: Span) {
        self.emit(
            span,
            InstructionKind::Assign {
                target: local,
                value,
                initialize: true,
            },
            None,
        );
        let ty = &self.function.locals[local.0 as usize].ty;
        if matches!(ty, Type::String | Type::List(_)) || self.is_string_owner_struct(ty) {
            self.owned_locals.push(local);
        }
    }

    fn replace_local(&mut self, local: LocalId, value: Operand, target_span: Span, span: Span) {
        let kind = if matches!(
            self.function.locals[local.0 as usize].ty,
            Type::Reference { .. }
        ) {
            let mut reference = op(Source::Local(local), target_span);
            reference.mode = UseMode::Share;
            InstructionKind::Store { reference, value }
        } else {
            InstructionKind::Assign {
                target: local,
                value,
                initialize: false,
            }
        };
        self.emit(span, kind, None);
    }

    fn lower_concat_initializer(
        &mut self,
        target: LocalId,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> Option<()> {
        let left = self.lower_concat_operand(left)?;
        let right = self.lower_concat_operand(right)?;
        self.initialize_concat(target, left, right, span);
        Some(())
    }

    fn lower_concat_operand(&mut self, expr: &Expr) -> Option<Operand> {
        if matches!(expr.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
            self.lower_read_receiver(expr)
        } else {
            let owner = self.lower_expr(expr)?;
            self.borrow(owner, Access::Borrow)
        }
    }

    fn initialize_concat(&mut self, target: LocalId, left: Operand, right: Operand, span: Span) {
        self.emit(
            span,
            InstructionKind::InitConcatString {
                target,
                strings: [read(left), read(right)],
            },
            None,
        );
        self.owned_locals.push(target);
    }

    fn lower_string_push_str(
        &mut self,
        expr: &Expr,
        base: &Expr,
        suffix: &Expr,
    ) -> Option<Operand> {
        let PathTarget::Local(target) = self.path(base) else {
            unreachable!("checked push_str receiver")
        };
        let receiver = self.lower_expr(base)?;
        // Keep the exclusive loan live across suffix evaluation. Reborrow
        // read-only for concat, then end both loans before replacing the slot.
        let exclusive = self.borrow(receiver, Access::Share)?;
        let suffix = self.lower_expr(suffix)?;
        let right = self.borrow(suffix, Access::Borrow)?;
        let left = self.borrow(exclusive, Access::Borrow)?;
        let scope_start = self.owned_locals.len();
        let staged = self.hidden_local("String append result", Type::String, expr.span);
        self.initialize_concat(staged, left, right, expr.span);
        self.replace_local(
            target,
            consume(op(Source::Local(staged), expr.span)),
            base.span,
            expr.span,
        );
        self.end_owned_locals(scope_start, expr.span);
        self.owned_locals.truncate(scope_start);
        self.unit(expr.span)
    }

    fn lower_expression_statement(&mut self, expr: &Expr) {
        if let ExprKind::Call {
            callee, arguments, ..
        } = &expr.kind
        {
            let scope_start = self.owned_locals.len();
            if let ExprKind::Field { base, name } = &callee.kind {
                if name == "concat" {
                    let owner = self.hidden_local("discarded String", Type::String, expr.span);
                    self.lower_concat_initializer(owner, base, &arguments[0], expr.span);
                    self.end_owned_locals(scope_start, expr.span);
                    self.owned_locals.truncate(scope_start);
                    return;
                }
            }
            if let Some(ty @ (Type::String | Type::List(_))) = self.ty(expr) {
                if let Some(result) = self.lower_expr(expr) {
                    let owner = self.hidden_local("discarded call result", ty, expr.span);
                    self.initialize_local(owner, consume(result), expr.span);
                    self.end_owned_locals(scope_start, expr.span);
                    self.owned_locals.truncate(scope_start);
                }
                return;
            }
        }
        self.lower_expr(expr);
    }

    fn is_direct_string_call(&self, expr: &Expr) -> bool {
        let ExprKind::Call { callee, .. } = &expr.kind else {
            return false;
        };
        match &callee.kind {
            ExprKind::Field { name, .. } => name == "concat",
            ExprKind::Path(_) => {
                self.ty(expr) == Some(Type::String)
                    && matches!(self.path(callee), PathTarget::Function(_))
            }
            _ => false,
        }
    }

    fn lower_with_temporary_owner(&mut self, base: &Expr) -> Option<Operand> {
        if let ExprKind::Call {
            callee, arguments, ..
        } = &base.kind
        {
            if let ExprKind::Field { base: left, name } = &callee.kind {
                if name == "concat" {
                    let owner = self.hidden_local("String temporary", Type::String, base.span);
                    self.lower_concat_initializer(owner, left, &arguments[0], base.span)?;
                    return Some(op(Source::Local(owner), base.span));
                }
            }
            if let Some(ty @ (Type::String | Type::List(_))) = self.ty(base) {
                let result = self.lower_expr(base)?;
                let owner = self.hidden_local("temporary owner", ty, base.span);
                self.initialize_local(owner, consume(result), base.span);
                return Some(op(Source::Local(owner), base.span));
            }
        }
        self.lower_expr(base)
    }

    fn lower_read_receiver(&mut self, base: &Expr) -> Option<Operand> {
        if matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
            let (root, projections) = self.lower_place(base)?;
            self.address_chain(root, &projections, Access::Borrow, base.span)
        } else {
            let owner = self.lower_with_temporary_owner(base)?;
            self.borrow(owner, Access::Borrow)
        }
    }

    fn lower_collection_read(
        &mut self,
        expr: &Expr,
        base: &Expr,
        method: &str,
        arguments: &[Expr],
    ) -> Option<Operand> {
        let scope_start = self.owned_locals.len();
        let result = (|| {
            let search = matches!(method, "contains" | "index_of");
            let string_field = matches!(base.kind, ExprKind::Field { .. } | ExprKind::Index { .. })
                && self.ty(base) == Some(Type::String);
            let receiver = if search || string_field {
                // Keep the receiver loan live across value evaluation.
                self.lower_read_receiver(base)?
            } else {
                self.lower_with_temporary_owner(base)?
            };
            let instruction = if search {
                let value = self.lower_expr(&arguments[0])?;
                InstructionKind::CollectionSearch {
                    return_index: method == "index_of",
                    source: read(receiver),
                    value: read(self.scalar(value)?),
                }
            } else if method == "len" {
                let receiver_type = self.operand_type(receiver);
                if matches!(receiver_type, Some(Type::List(_)))
                    || matches!(receiver_type, Some(Type::Reference { inner, .. }) if matches!(*inner, Type::List(_)))
                {
                    InstructionKind::ListLen {
                        source: read(receiver),
                    }
                } else {
                    InstructionKind::StringLen {
                        source: read(receiver),
                    }
                }
            } else if method == "get" {
                let index = self.lower_expr(&arguments[0])?;
                InstructionKind::ListGet {
                    source: read(receiver),
                    index: read(self.scalar(index)?),
                }
            } else {
                // Keep the receiver loan live while evaluating the offset.
                let source = read(self.borrow(receiver, Access::Borrow)?);
                let offset = self.lower_expr(&arguments[0])?;
                let offset = read(self.scalar(offset)?);
                match method {
                    "byte_at" => InstructionKind::StringByteAt { source, offset },
                    "scalar_at" => InstructionKind::StringScalarAt { source, offset },
                    _ => InstructionKind::StringIsCharBoundary { source, offset },
                }
            };
            self.emit(expr.span, instruction, self.ty(expr))
        })();
        if result.is_some() {
            self.end_owned_locals(scope_start, expr.span);
        }
        self.owned_locals.truncate(scope_start);
        result
    }

    fn end_owned_locals(&mut self, from: usize, span: Span) {
        for index in (from..self.owned_locals.len()).rev() {
            let local = self.owned_locals[index];
            let end = match self.function.locals[local.0 as usize].ty {
                Type::List(_) => InstructionKind::EndListLocal { local },
                Type::Struct(_) | Type::Enum(_) | Type::Array { .. } => {
                    InstructionKind::EndStructLocal { local }
                }
                _ => InstructionKind::EndStringLocal { local },
            };
            self.emit(span, end, None);
        }
    }

    fn preserve_scope_result(&mut self, value: Operand, from: usize) -> Option<Operand> {
        if matches!(value.source, Source::Local(local) if self.owned_locals[from..].contains(&local))
        {
            self.capture(consume(value))
        } else {
            Some(value)
        }
    }

    fn return_from_body(&mut self, returned: Option<Operand>, span: Span) {
        if let Some(current) = self.current {
            let returned = returned
                .and_then(|value| self.preserve_scope_result(value, 0))
                .map(consume);
            // Stage the return operand before the lexical loans' final uses
            // so the ownership checker sees any move of an iterated collection.
            let returned = if self
                .loops
                .iter()
                .any(|targets| targets.iterable_loan.is_some())
            {
                returned.and_then(|value| self.capture(value)).map(consume)
            } else {
                returned
            };
            self.use_iteration_loans();
            self.end_owned_locals(0, span);
            self.set_terminator(current, TerminatorKind::Return(returned), Some(span));
        }
    }

    fn lower_body(&mut self, body: &Block) {
        let value = self.lower_block(body);
        let result = self.function.signature.result.as_ref().clone();
        let returned = if result == Type::Primitive(Primitive::Unit) {
            None
        } else {
            value.and_then(|value| self.owned_to(value, &result))
        };
        self.return_from_body(returned, body.span);
    }

    fn lower_block(&mut self, block: &Block) -> Option<Operand> {
        let scope_start = self.owned_locals.len();
        for statement in &block.statements {
            if self.current.is_none() {
                break;
            }
            match &statement.kind {
                StatementKind::Binding { value, .. } => {
                    if let ExprKind::Call {
                        callee, arguments, ..
                    } = &value.kind
                    {
                        if let ExprKind::Field { base, name } = &callee.kind {
                            if name == "concat" {
                                self.lower_concat_initializer(
                                    self.local(statement),
                                    base,
                                    &arguments[0],
                                    value.span,
                                );
                                continue;
                            }
                        }
                    }
                    let rhs = self.lower_expr(value);
                    if let Some(rhs) = rhs {
                        let target = self.local(statement);
                        let ty = self.function.locals[target.0 as usize].ty.clone();
                        if let Some(rhs) = self.owned_to(rhs, &ty) {
                            self.initialize_local(target, rhs, statement.span);
                        }
                    }
                }
                StatementKind::Destructure { fields, value, .. } => {
                    self.lower_destructure(fields, value);
                }
                StatementKind::TupleDestructure {
                    elements, value, ..
                } => self.lower_tuple_destructure(elements, value),
                StatementKind::Assign {
                    target,
                    operator,
                    value,
                } => {
                    if matches!(target.kind, ExprKind::Index { .. } | ExprKind::Field { .. })
                        || (matches!(
                            operator.as_str(),
                            "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
                        ) && self.selected_assignments.contains_key(&self.id(target)))
                    {
                        self.lower_place_assign(statement.span, target, operator, value);
                        continue;
                    }
                    let PathTarget::Local(local) = self.path(target) else {
                        unreachable!("checked assignment")
                    };
                    if let ExprKind::Call {
                        callee, arguments, ..
                    } = &value.kind
                    {
                        if let ExprKind::Field { base, name } = &callee.kind {
                            if name == "concat" {
                                let staged = self.hidden_local(
                                    "String replacement",
                                    Type::String,
                                    value.span,
                                );
                                let scope_start = self.owned_locals.len();
                                if self
                                    .lower_concat_initializer(
                                        staged,
                                        base,
                                        &arguments[0],
                                        value.span,
                                    )
                                    .is_some()
                                {
                                    self.replace_local(
                                        local,
                                        consume(op(Source::Local(staged), value.span)),
                                        target.span,
                                        statement.span,
                                    );
                                    self.end_owned_locals(scope_start, statement.span);
                                    self.owned_locals.truncate(scope_start);
                                }
                                continue;
                            }
                        }
                    }
                    let previous = (operator != "=").then(|| op(Source::Local(local), target.span));
                    let previous = previous
                        .and_then(|operand| self.scalar(operand))
                        .and_then(|operand| self.capture(operand));
                    let rhs = self
                        .lower_expr(value)
                        .and_then(|operand| self.scalar(operand));
                    if let Some(rhs) = rhs {
                        let assigned = if operator == "=" {
                            rhs
                        } else {
                            let ty = match self.function.locals[local.0 as usize].ty.clone() {
                                Type::Reference { inner, .. } => *inner,
                                ty => ty,
                            };
                            self.emit(
                                statement.span,
                                InstructionKind::Binary {
                                    op: binary_op(operator),
                                    left: read(previous.expect("compound old value captured")),
                                    right: read(rhs),
                                },
                                Some(ty),
                            )
                            .expect("live compound result")
                        };
                        let Some(assigned) = self.owned(assigned) else {
                            continue;
                        };
                        self.replace_local(local, assigned, target.span, statement.span);
                    }
                }
                StatementKind::Expression(expr) => {
                    self.lower_expression_statement(expr);
                }
                StatementKind::Return(value) => {
                    let returned = match value {
                        Some(expr) => {
                            let result = self.function.signature.result.as_ref().clone();
                            self.lower_expr(expr)
                                .and_then(|value| self.owned_to(value, &result))
                        }
                        None => None,
                    };
                    self.return_from_body(returned, statement.span);
                }
                StatementKind::Loop(body) => self.lower_loop(body, statement.span),
                StatementKind::ForEach { items, body, .. } => {
                    self.lower_for_each(statement, items, body);
                }
                StatementKind::Break => {
                    let loop_targets = self.loops.last_mut().expect("checked break");
                    loop_targets.had_break = true;
                    let (target, start) = (loop_targets.exit, loop_targets.scope_start);
                    self.end_owned_locals(start, statement.span);
                    self.goto(target, Vec::new(), statement.span);
                }
                StatementKind::Continue => {
                    let loop_targets = self.loops.last().expect("checked continue");
                    let (target, start) = (loop_targets.header, loop_targets.scope_start);
                    self.end_owned_locals(start, statement.span);
                    self.goto(target, Vec::new(), statement.span);
                }
            }
        }
        let value = if self.current.is_some() {
            match block.tail.as_deref() {
                Some(tail) => self.lower_expr(tail),
                None => self.unit(block.span),
            }
        } else {
            None
        };
        let value = value.and_then(|value| self.preserve_scope_result(value, scope_start));
        if self.current.is_some() {
            self.end_owned_locals(scope_start, block.span);
        }
        self.owned_locals.truncate(scope_start);
        value
    }
    /// Address one element of an array operand. The bounds check is part of the
    /// instruction; the result is a reference with the requested access.
    fn element_addr(
        &mut self,
        mut array: Operand,
        position: Operand,
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let element = self.array_element(array);
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        array.mode = access_mode(access);
        let mut reference = self.emit(
            span,
            InstructionKind::ElementAddr {
                loan,
                base: array,
                index: read(position),
                access,
            },
            Some(Type::Reference {
                access,
                inner: element,
            }),
        )?;
        reference.mode = access_mode(access);
        Some(reference)
    }
    /// Element type of an array owner or of a reference to an array.
    fn array_element(&self, array: Operand) -> Box<Type> {
        match self.operand_type(array) {
            Some(Type::Array { element, .. } | Type::List(element)) => element,
            Some(Type::Reference { inner, .. }) => match *inner {
                Type::Array { element, .. } | Type::List(element) => element,
                _ => unreachable!("checked array index base"),
            },
            _ => unreachable!("checked array index base"),
        }
    }
    /// Evaluate the root and every index of a projection chain such as
    /// `a[i].pts[j].x` left to right, each index captured at its evaluation
    /// point. No address is formed yet, so index effects precede any bounds
    /// check and the right-hand side of a write.
    fn lower_place(&mut self, expr: &Expr) -> Option<(Operand, Vec<Projection>)> {
        if matches!(expr.kind, ExprKind::Path(_)) {
            return Some((self.lower_expr(expr)?, Vec::new()));
        }
        let (base, step) = match &expr.kind {
            ExprKind::Index { base, .. } => (base, None),
            ExprKind::Field { base, name } => (base, Some(name)),
            _ => unreachable!("checked projection place"),
        };
        let (root, mut projections) =
            if matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
                self.lower_place(base)?
            } else {
                (self.lower_expr(base)?, Vec::new())
            };
        match (&expr.kind, step) {
            (ExprKind::Index { index, .. }, _) => {
                let position = self.lower_expr(index)?;
                let position = self.scalar(position)?;
                let statically_known = matches!(index.kind, ExprKind::Number(_));
                projections.push(Projection::Index(self.capture(position)?, statically_known));
            }
            (_, Some(name)) => {
                if let Some(slot) = self.tuple_projections.get(&(expr as *const Expr as usize)) {
                    projections.push(Projection::FieldSlot(*slot));
                } else {
                    projections.push(Projection::Field(name.clone()));
                }
            }
            _ => unreachable!(),
        }
        Some((root, projections))
    }
    /// Chain of checked element and field addresses from `root` through
    /// `projections`. Every level carries `access`, so a write needs `Share`
    /// references down to the target.
    fn address_chain(
        &mut self,
        root: Operand,
        projections: &[Projection],
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let mut current = root;
        for projection in projections {
            current = match projection {
                Projection::Index(position, _) => {
                    self.element_addr(current, *position, access, span)?
                }
                Projection::Field(name) => self.field_addr(current, name, access, span)?,
                Projection::FieldSlot(slot) => {
                    self.field_addr_slot(current, *slot, access, span)?
                }
            };
        }
        Some(current)
    }
    fn load_element(&mut self, reference: Operand, span: Span) -> Option<Operand> {
        let Some(Type::Reference { inner, .. }) = self.operand_type(reference) else {
            unreachable!("element address is a reference")
        };
        self.load(reference, *inner, span)
    }
    /// `a[i] = v`, `p.x = v`, `a[i].pts[j] += v` and every other projection
    /// chain, plain or compound. The root and every index are evaluated and
    /// captured first, then the right-hand side; the checked address chain and
    /// the store are adjacent, so a bounds trap fires after the right-hand
    /// side's effects. A compound write reads the place first. A
    /// whole-aggregate target (`l.a = P { .. }`, `m[i] = [..]`) stores the
    /// consumed aggregate with a memory copy.
    fn lower_place_assign(
        &mut self,
        span: Span,
        target: &Expr,
        operator: &str,
        value: &Expr,
    ) -> Option<()> {
        let (root, positions) = self.lower_place(target)?;
        if matches!(
            operator,
            "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
        ) {
            if let Some(selected) = self.selected_assignments.get(&self.id(target)).cloned() {
                let scope_start = self.owned_locals.len();
                let result = (|| {
                    // Capture the narrowest safely addressable owner before RHS.
                    // Field projections do not trap; the first index does.
                    let first_index = positions
                        .iter()
                        .position(|projection| matches!(projection, Projection::Index(_, false)));
                    let (receiver, delayed_index) = if let Some(index) = first_index {
                        let prefix = &positions[..index];
                        let array_owner = if prefix.is_empty() {
                            self.borrow(root, Access::Share)?
                        } else {
                            self.address_chain(root, prefix, Access::Share, target.span)?
                        };
                        (array_owner, Some(index))
                    } else if positions.is_empty() {
                        (self.borrow(root, Access::Share)?, None)
                    } else {
                        (
                            self.address_chain(root, &positions, Access::Share, target.span)?,
                            None,
                        )
                    };
                    let rhs = self.lower_expr(value)?;
                    // Forming the indexed address after RHS keeps bounds traps
                    // after RHS effects and lets early return skip the access.
                    let receiver = if let Some(index) = delayed_index {
                        self.address_chain(
                            receiver,
                            &positions[index..],
                            Access::Share,
                            target.span,
                        )?
                    } else {
                        receiver
                    };
                    let receiver =
                        self.lower_selected_argument(receiver, &selected.signature.parameters[0])?;
                    let rhs =
                        self.lower_selected_argument(rhs, &selected.signature.parameters[1])?;
                    self.emit(
                        span,
                        InstructionKind::Call {
                            callee: read(op(Source::Function(selected.function), span)),
                            arguments: vec![receiver, rhs],
                        },
                        Some(selected.signature.result.as_ref().clone()),
                    )?;
                    Some(())
                })();
                if result.is_some() {
                    self.end_owned_locals(scope_start, span);
                }
                self.owned_locals.truncate(scope_start);
                return result;
            }
        }
        if operator == "=" {
            if let Some((local, field)) = self.local_string_field(target, root) {
                if matches!(value.kind, ExprKind::Path(_) | ExprKind::StringLiteral(_))
                    || self.is_direct_string_call(value)
                {
                    // Stage the RHS before the write so it can borrow the old field.
                    let scope_start = self.owned_locals.len();
                    let Some(rhs) = self.lower_with_temporary_owner(value) else {
                        self.owned_locals.truncate(scope_start);
                        return None;
                    };
                    let rhs = if matches!(value.kind, ExprKind::StringLiteral(_)) {
                        let staged =
                            self.hidden_local("String field replacement", Type::String, value.span);
                        self.initialize_local(staged, consume(rhs), value.span);
                        op(Source::Local(staged), value.span)
                    } else {
                        rhs
                    };
                    self.emit(
                        span,
                        InstructionKind::ReplaceStringField {
                            target: local,
                            field,
                            value: consume(rhs),
                        },
                        None,
                    );
                    self.end_owned_locals(scope_start, span);
                    self.owned_locals.truncate(scope_start);
                    return Some(());
                }
            }
        }
        if operator == "=" {
            if let Some(place_ty) = self.ty(target) {
                if matches!(place_ty, Type::String | Type::List(_))
                    || self.is_string_owner_struct(&place_ty)
                {
                    // Owning overwrite: stage the value first (it may read the
                    // old one), exchange it into the place, then release what
                    // came out exactly once.
                    let scope_start = self.owned_locals.len();
                    let result = (|| {
                        let staged = self.stage_replacement(value, &place_ty)?;
                        self.swap_into_place(root, &positions, staged, span)
                    })();
                    if result.is_some() {
                        self.end_owned_locals(scope_start, span);
                    }
                    self.owned_locals.truncate(scope_start);
                    return result;
                }
            }
        }
        let previous = if operator == "=" {
            None
        } else {
            let reference = self.address_chain(root, &positions, Access::Borrow, span)?;
            Some(self.load_element(reference, span)?)
        };
        let rhs = self.lower_expr(value)?;
        let rhs = self.scalar(rhs)?;
        let assigned = match previous {
            None => rhs,
            Some(previous) => {
                let element = self
                    .operand_type(previous)
                    .expect("compound element read is a value");
                self.emit(
                    span,
                    InstructionKind::Binary {
                        op: binary_op(operator),
                        left: read(previous),
                        right: read(rhs),
                    },
                    Some(element),
                )?
            }
        };
        let assigned = self.owned(assigned)?;
        let reference = self.address_chain(root, &positions, Access::Share, span)?;
        self.emit(
            span,
            InstructionKind::Store {
                reference,
                value: assigned,
            },
            None,
        );
        Some(())
    }
    /// Reference to a place: the projection chain's checked address, or a
    /// whole-local borrow when the place is a bare local.
    fn place_reference(
        &mut self,
        root: Operand,
        positions: &[Projection],
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let mut reference = if positions.is_empty() {
            self.borrow(root, access)?
        } else {
            self.address_chain(root, positions, access, span)?
        };
        reference.mode = access_mode(access);
        Some(reference)
    }
    /// Evaluate the replacement value into a fresh hidden owner local that the
    /// place will exchange with. The local is registered for cleanup.
    fn stage_replacement(&mut self, value: &Expr, place_ty: &Type) -> Option<LocalId> {
        let scope_start = self.owned_locals.len();
        let span = value.span;
        let rhs = if matches!(place_ty, Type::Primitive(_)) {
            let rhs = self.lower_expr(value)?;
            let rhs = self.scalar(rhs)?;
            self.owned(rhs)?
        } else if *place_ty == Type::String && self.is_direct_string_call(value) {
            self.lower_with_temporary_owner(value)?
        } else if !matches!(value.kind, ExprKind::Path(_))
            && (self.is_string_transport_owner(place_ty)
                || (matches!(place_ty, Type::Enum(_)) && self.is_string_owner_struct(place_ty)))
        {
            self.owned_element(value, place_ty)?
        } else {
            let rhs = self.lower_expr(value)?;
            self.owned_to(rhs, place_ty)?
        };
        if let Source::Local(local) = rhs.source {
            if self.owned_locals[scope_start..].contains(&local) {
                return Some(local);
            }
        }
        let staged = self.hidden_local("replacement value", place_ty.clone(), span);
        self.initialize_local(staged, consume(rhs), span);
        Some(staged)
    }
    /// Exchange the place with the staged local. Index paths were evaluated
    /// and captured earlier; the checked address is formed last, after the
    /// right-hand side.
    fn swap_into_place(
        &mut self,
        root: Operand,
        positions: &[Projection],
        staged: LocalId,
        span: Span,
    ) -> Option<()> {
        let place = self.place_reference(root, positions, Access::Share, span)?;
        let other = self.borrow(op(Source::Local(staged), span), Access::Share)?;
        let mut other = other;
        other.mode = UseMode::Share;
        self.emit(
            span,
            InstructionKind::SwapPlaces {
                left: place,
                right: other,
            },
            None,
        );
        Some(())
    }
    /// `replace(place, value)`: value first, then the checked address, then a
    /// bitwise exchange; the old value is the result and is not released.
    fn lower_replace(&mut self, expr: &Expr, arguments: &[Expr]) -> Option<Operand> {
        let place_ty = self.ty(expr)?;
        let (root, positions) = self.lower_place(&arguments[0])?;
        let staged = self.stage_replacement(&arguments[1], &place_ty)?;
        self.swap_into_place(root, &positions, staged, expr.span)?;
        let old = op(Source::Local(staged), expr.span);
        if matches!(place_ty, Type::Primitive(_)) {
            self.owned(old)
        } else {
            Some(consume(old))
        }
    }
    /// `swap(a, b)`: both place paths are evaluated left to right, then both
    /// checked addresses are formed and their values exchanged.
    fn lower_swap(&mut self, expr: &Expr, arguments: &[Expr]) -> Option<Operand> {
        let (left_root, left_positions) = self.lower_place(&arguments[0])?;
        let (right_root, right_positions) = self.lower_place(&arguments[1])?;
        let left = self.place_reference(left_root, &left_positions, Access::Share, expr.span)?;
        let right = self.place_reference(right_root, &right_positions, Access::Share, expr.span)?;
        self.emit(expr.span, InstructionKind::SwapPlaces { left, right }, None);
        self.unit(expr.span)
    }
    fn local_string_field(&self, target: &Expr, root: Operand) -> Option<(LocalId, u32)> {
        let (ExprKind::Field { base, name }, Source::Local(local)) = (&target.kind, root.source)
        else {
            return None;
        };
        let binding = &self.function.locals[local.0 as usize];
        let id = match &binding.ty {
            Type::Struct(id)
                if binding.mutable && !self.function.parameter_locals.contains(&local) =>
            {
                *id
            }
            Type::Reference {
                access: Access::Share,
                inner,
            } if self.function.parameter_locals.contains(&local) => {
                let Type::Struct(id) = inner.as_ref() else {
                    return None;
                };
                let position = self
                    .function
                    .parameter_locals
                    .iter()
                    .position(|parameter| *parameter == local)?;
                if self.function.signature.parameters[position].access != Access::Share {
                    return None;
                }
                *id
            }
            _ => return None,
        };
        if !matches!(base.kind, ExprKind::Path(_)) {
            return None;
        }
        let definition = &self.types[id.0 as usize];
        struct_field_index(definition, name)
            .filter(|field| definition.fields[*field].ty == Type::String)
            .map(|field| (local, field as u32))
    }

    /// Address one field of a struct owner or of a reference to a struct. The
    /// result is a reference with the requested access.
    fn field_addr(
        &mut self,
        owner: Operand,
        field_name: &str,
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let id = match self.operand_type(owner) {
            Some(Type::Struct(id)) => id,
            Some(Type::Reference { inner, .. }) => match *inner {
                Type::Struct(id) => id,
                _ => unreachable!("checked struct field base"),
            },
            _ => unreachable!("checked struct field base"),
        };
        let definition = &self.types[id.0 as usize];
        let index = struct_field_index(definition, field_name).expect("checked struct field");
        self.field_addr_index(owner, index, access, span)
    }
    fn field_addr_slot(
        &mut self,
        owner: Operand,
        slot: u32,
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        self.field_addr_index(owner, slot as usize, access, span)
    }
    fn field_addr_index(
        &mut self,
        mut owner: Operand,
        index: usize,
        access: Access,
        span: Span,
    ) -> Option<Operand> {
        let id = match self.operand_type(owner) {
            Some(Type::Struct(id)) => id,
            Some(Type::Reference { inner, .. }) => match *inner {
                Type::Struct(id) => id,
                _ => unreachable!("checked struct field base"),
            },
            _ => unreachable!("checked struct field base"),
        };
        let definition = &self.types[id.0 as usize];
        let field_type = definition.fields[index].ty.clone();
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        owner.mode = access_mode(access);
        let mut reference = self.emit(
            span,
            InstructionKind::FieldAddr {
                loan,
                base: owner,
                field: index as u32,
                access,
            },
            Some(Type::Reference {
                access,
                inner: Box::new(field_type),
            }),
        )?;
        reference.mode = access_mode(access);
        Some(reference)
    }
    fn hidden_local(&mut self, name: &str, ty: Type, span: Span) -> LocalId {
        let id = LocalId(self.function.locals.len() as u32);
        self.function.locals.push(Local {
            name: name.into(),
            ty,
            mutable: true,
            span,
        });
        id
    }
    /// `[expr; N]`. Zero evaluates nothing and one evaluates once without a
    /// loop. Larger counts always lower to a loop over a hidden zeroed
    /// accumulator and a hidden counter, so the IR size does not depend on N and
    /// an owned element expression is a repeated move that ownership rejects.
    fn lower_loop(&mut self, body: &Block, span: Span) {
        let header = self.new_block();
        let exit = self.new_block();
        self.goto(header, Vec::new(), span);
        self.current = Some(header);
        let had_break = self.lower_loop_body(body, header, exit, None);
        self.current = had_break.then_some(exit);
    }

    fn lower_loop_body(
        &mut self,
        body: &Block,
        header: BlockId,
        exit: BlockId,
        iterable_loan: Option<Operand>,
    ) -> bool {
        self.loops.push(LoopTargets {
            header,
            exit,
            had_break: false,
            scope_start: self.owned_locals.len(),
            iterable_loan,
        });
        self.lower_block(body);
        self.goto(header, Vec::new(), body.span);
        self.loops.pop().unwrap().had_break
    }

    fn lower_for_each(&mut self, statement: &Statement, items: &Expr, body: &Block) -> Option<()> {
        let scope_start = self.owned_locals.len();
        let receiver = self.lower_read_receiver(items)?;
        let Some(Type::Reference { inner, .. }) = self.operand_type(receiver) else {
            unreachable!("checked iteration receiver")
        };
        let span = statement.span;
        let u32_ty = Type::Primitive(Primitive::U32);
        let limit = match *inner {
            Type::Array { len: 0, .. } => return Some(()),
            Type::Array { len, .. } => {
                self.constant(span, Constant::Integer(len.to_string()), u32_ty.clone())?
            }
            Type::List(_) => self.emit(
                span,
                InstructionKind::ListLen {
                    source: read(receiver),
                },
                Some(u32_ty.clone()),
            )?,
            Type::String => self.emit(
                span,
                InstructionKind::StringLen {
                    source: read(receiver),
                },
                Some(u32_ty.clone()),
            )?,
            _ => unreachable!("checked iteration collection"),
        };
        let counter = self.hidden_local("iteration index", u32_ty.clone(), span);
        let start = self.constant(span, Constant::Integer("0".into()), u32_ty.clone())?;
        self.initialize_local(counter, consume(start), span);

        let header = self.new_block();
        let entry = self.new_block();
        let exit = self.new_block();
        self.goto(header, Vec::new(), span);
        self.current = Some(header);
        let position = self.capture(op(Source::Local(counter), span))?;
        let more = self.emit(
            span,
            InstructionKind::Binary {
                op: BinaryOp::Less,
                left: read(position),
                right: read(limit),
            },
            Some(Type::Primitive(Primitive::Bool)),
        )?;
        self.finish(
            header,
            TerminatorKind::Branch {
                condition: read(more),
                then_edge: Edge {
                    target: entry,
                    arguments: Vec::new(),
                },
                else_edge: Edge {
                    target: exit,
                    arguments: Vec::new(),
                },
            },
            Some(span),
        );
        self.current = Some(entry);
        let copy = match *inner {
            // The counter is a byte offset that always sits on a scalar start.
            Type::String => consume(self.emit(
                items.span,
                InstructionKind::StringScalarRead {
                    source: read(receiver),
                    offset: read(position),
                    width: false,
                },
                Some(Type::Primitive(Primitive::Char)),
            )?),
            Type::List(ref element) if matches!(**element, Type::Primitive(_)) => {
                consume(self.emit(
                    items.span,
                    InstructionKind::ListRead {
                        source: read(receiver),
                        index: read(position),
                    },
                    Some(element.as_ref().clone()),
                )?)
            }
            Type::List(_) => {
                // A non-copyable element is lent: the binding is a read-only
                // reference into the list, which stays loaned for the loop.
                consume(self.element_addr(receiver, position, Access::Borrow, items.span)?)
            }
            Type::Array { ref element, .. } if !matches!(**element, Type::Primitive(_)) => {
                consume(self.element_addr(receiver, position, Access::Borrow, items.span)?)
            }
            _ => {
                let element = self.element_addr(receiver, position, Access::Borrow, items.span)?;
                let loaded = self.load_element(element, items.span)?;
                self.owned(loaded)?
            }
        };
        self.initialize_local(self.local(statement), copy, span);

        // Advance before user code so continue uses the same header as a bare loop.
        let step = if *inner == Type::String {
            self.emit(
                span,
                InstructionKind::StringScalarRead {
                    source: read(receiver),
                    offset: read(position),
                    width: true,
                },
                Some(u32_ty.clone()),
            )?
        } else {
            self.constant(span, Constant::Integer("1".into()), u32_ty.clone())?
        };
        let next = self.emit(
            span,
            InstructionKind::Binary {
                op: BinaryOp::Add,
                left: read(position),
                right: read(step),
            },
            Some(u32_ty),
        )?;
        self.replace_local(counter, consume(next), span, span);
        self.lower_loop_body(body, header, exit, Some(receiver));
        self.current = Some(exit);
        self.end_owned_locals(scope_start, span);
        self.owned_locals.truncate(scope_start);
        Some(())
    }

    fn lower_expr(&mut self, expr: &Expr) -> Option<Operand> {
        self.current?;
        match &expr.kind {
            ExprKind::Tuple(elements) => {
                let Some(Type::Struct(id)) = self.ty(expr) else {
                    unreachable!("checked tuple type")
                };
                let fields_def = self.types[id.0 as usize]
                    .fields
                    .iter()
                    .map(|field| (field.name.clone(), field.ty.clone()))
                    .collect::<Vec<_>>();
                let scope_start = self.owned_locals.len();
                let mut slots: Vec<Option<Operand>> = vec![None; fields_def.len()];
                let resolved_slots = self
                    .tuple_initializers
                    .get(&(expr as *const Expr as usize))
                    .cloned();
                for (position, element) in elements.iter().enumerate() {
                    let index = resolved_slots
                        .as_ref()
                        .and_then(|indices| indices.get(position).copied())
                        .map(|index| index as usize)
                        .unwrap_or(position);
                    let field_ty = &fields_def[index].1;
                    let Some(value) = self.lower_expr(&element.value) else {
                        self.owned_locals.truncate(scope_start);
                        return None;
                    };
                    let Some(mut value) = (if *field_ty == Type::String {
                        self.owned_to(value, field_ty)
                    } else if self.is_string_transport_owner(field_ty) {
                        let Some(value) = self.owned_to(value, field_ty) else {
                            self.owned_locals.truncate(scope_start);
                            return None;
                        };
                        let staged = self.hidden_local(
                            "nested String owner element",
                            field_ty.clone(),
                            element.span,
                        );
                        self.initialize_local(staged, value, element.span);
                        Some(consume(op(Source::Local(staged), element.span)))
                    } else {
                        self.owned_captured(value, field_ty)
                    }) else {
                        self.owned_locals.truncate(scope_start);
                        return None;
                    };
                    if *field_ty == Type::String
                        && position + 1 < elements.len()
                        && matches!(value.source, Source::Local(_))
                    {
                        let staged =
                            self.hidden_local("tuple String element", Type::String, element.span);
                        self.initialize_local(staged, value, element.span);
                        value = consume(op(Source::Local(staged), element.span));
                    }
                    slots[index] = Some(value);
                }
                let result = self.emit(
                    expr.span,
                    InstructionKind::StructNew {
                        ty: id,
                        fields: slots
                            .into_iter()
                            .map(|slot| slot.expect("checked complete tuple initializer"))
                            .collect(),
                    },
                    Some(Type::Struct(id)),
                );
                if result.is_some() {
                    self.end_owned_locals(scope_start, expr.span);
                }
                self.owned_locals.truncate(scope_start);
                result
            }
            ExprKind::Array(elements) => {
                if let Some(list_ty @ Type::List(_)) = self.ty(expr) {
                    return self.lower_list_literal(expr, elements, list_ty);
                }
                let Some(Type::Array {
                    element: element_ty,
                    ..
                }) = self.ty(expr)
                else {
                    unreachable!("checked array literal type")
                };
                let mut operands = Vec::with_capacity(elements.len());
                for element in elements {
                    operands.push(self.owned_element(element, &element_ty)?);
                }
                self.emit(
                    expr.span,
                    InstructionKind::ArrayNew {
                        init: ArrayInit::Elements(operands),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Index { .. } | ExprKind::Field { .. } => {
                let (root, projections) = self.lower_place(expr)?;
                let reference =
                    self.address_chain(root, &projections, Access::Borrow, expr.span)?;
                self.load_element(reference, expr.span)
            }
            ExprKind::RepeatArray { value, .. } => self.lower_repeat(expr, value),
            ExprKind::Number(raw) => {
                let ty = self.ty(expr).expect("checked number type");
                let value = if raw.contains(['.', 'e', 'E']) {
                    Constant::Float(raw.clone())
                } else {
                    Constant::Integer(raw.clone())
                };
                self.constant(expr.span, value, ty)
            }
            ExprKind::CharLiteral(value) => self.constant(
                expr.span,
                Constant::Integer((*value as u32).to_string()),
                Type::Primitive(Primitive::Char),
            ),
            ExprKind::StringLiteral(text) => {
                self.constant(expr.span, Constant::String(text.clone()), Type::String)
            }
            ExprKind::Bool(value) => self.constant(
                expr.span,
                Constant::Bool(*value),
                Type::Primitive(Primitive::Bool),
            ),
            ExprKind::Path(_) if self.variants.contains_key(&self.id(expr)) => {
                self.lower_variant(expr, &[])
            }
            ExprKind::Path(_) => {
                let source = match self.path(expr) {
                    PathTarget::Local(id) => Source::Local(id),
                    PathTarget::Function(id) => Source::Function(id),
                };
                Some(op(source, expr.span))
            }
            ExprKind::Unary { operator, operand } => {
                if operator == "-" && self.selected_operators.contains_key(&self.id(expr)) {
                    return self.lower_selected_unary_operator(expr, operand);
                }
                // Signed minimum is a single negative constant: its positive
                // literal cannot be represented in the target signed type.
                if operator == "-"
                    && self
                        .facts
                        .expressions
                        .iter()
                        .all(|f| f.node_addr != operand.as_ref() as *const Expr as usize)
                {
                    if let ExprKind::Number(raw) = &operand.kind {
                        return self.constant(
                            expr.span,
                            Constant::Integer(format!("-{raw}")),
                            self.ty(expr).expect("checked negative type"),
                        );
                    }
                }
                let input = self.lower_expr(operand)?;
                let input = self.scalar(input)?;
                self.emit(
                    expr.span,
                    InstructionKind::Unary {
                        op: unary_op(operator),
                        operand: read(input),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Cast { value, .. } => {
                let source = self.lower_expr(value)?;
                let source = self.scalar(source)?;
                let source_ty = self.ty(value).expect("checked cast source type");
                let target_ty = self.ty(expr).expect("checked cast target type");
                self.emit(
                    expr.span,
                    InstructionKind::Cast {
                        value: read(source),
                        source: primitive_type(&source_ty).expect("checked numeric source"),
                        target: primitive_type(&target_ty).expect("checked numeric target"),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if self.selected_operators.contains_key(&self.id(expr)) => {
                self.lower_selected_operator(expr, left, right)
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "&&" || operator == "||" => {
                self.lower_short_circuit(expr, operator, left, right)
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                let lhs = self.lower_expr(left)?;
                let lhs = self.scalar(lhs)?;
                let lhs = self.capture(lhs)?;
                let rhs = self.lower_expr(right)?;
                let rhs = self.scalar(rhs)?;
                self.emit(
                    expr.span,
                    InstructionKind::Binary {
                        op: binary_op(operator),
                        left: read(lhs),
                        right: read(rhs),
                    },
                    self.ty(expr),
                )
            }
            ExprKind::Call { arguments, .. } if self.variants.contains_key(&self.id(expr)) => {
                self.lower_variant(expr, arguments)
            }
            ExprKind::Call { arguments, .. } if self.explicit_asserts.contains(&self.id(expr)) => {
                let condition = self.lower_expr(&arguments[0])?;
                let condition = self.scalar(condition)?;
                self.emit(
                    expr.span,
                    InstructionKind::Assert {
                        condition: read(condition),
                    },
                    None,
                );
                self.unit(expr.span)
            }
            ExprKind::Call { arguments, .. } if self.explicit_replaces.contains(&self.id(expr)) => {
                self.lower_replace(expr, arguments)
            }
            ExprKind::Call { arguments, .. } if self.explicit_swaps.contains(&self.id(expr)) => {
                self.lower_swap(expr, arguments)
            }
            ExprKind::Call { arguments, .. } if self.explicit_drops.contains(&self.id(expr)) => {
                let value = consume(self.lower_expr(&arguments[0])?);
                self.emit(expr.span, InstructionKind::DropLocal { value }, None);
                self.unit(expr.span)
            }
            ExprKind::Call {
                callee, arguments, ..
            } if self.selected_calls.contains_key(&self.id(expr)) => {
                self.lower_selected_call(expr, callee, arguments)
            }
            ExprKind::Call {
                callee, arguments, ..
            } => {
                if let ExprKind::Field { base, name } = &callee.kind {
                    if name == "to_u32" {
                        let source = self.lower_expr(base)?;
                        let source = self.scalar(source)?;
                        return self.emit(
                            expr.span,
                            InstructionKind::Cast {
                                value: read(source),
                                source: Primitive::U8,
                                target: Primitive::U32,
                            },
                            self.ty(expr),
                        );
                    }
                    if matches!(name.as_str(), "wrapping_add" | "wrapping_mul") {
                        let left = self.lower_expr(base)?;
                        let left = self.scalar(left)?;
                        let right = self.lower_expr(&arguments[0])?;
                        let right = self.scalar(right)?;
                        return self.emit(
                            expr.span,
                            InstructionKind::Binary {
                                op: if name == "wrapping_add" {
                                    BinaryOp::WrappingAdd
                                } else {
                                    BinaryOp::WrappingMultiply
                                },
                                left: read(left),
                                right: read(right),
                            },
                            self.ty(expr),
                        );
                    }
                    if matches!(name.as_str(), "bit_and" | "bit_xor" | "bit_or") {
                        let left = self.lower_expr(base)?;
                        let left = self.scalar(left)?;
                        let right = self.lower_expr(&arguments[0])?;
                        let right = self.scalar(right)?;
                        return self.emit(
                            expr.span,
                            InstructionKind::Binary {
                                op: match name.as_str() {
                                    "bit_and" => BinaryOp::BitwiseAnd,
                                    "bit_xor" => BinaryOp::BitwiseXor,
                                    _ => BinaryOp::BitwiseOr,
                                },
                                left: read(left),
                                right: read(right),
                            },
                            self.ty(expr),
                        );
                    }
                    if name == "copy" {
                        // Read the receiver (loading through a reference or
                        // element address) and produce a fresh owned value.
                        let source = self.lower_expr(base)?;
                        let source = self.scalar(source)?;
                        return self.emit(
                            expr.span,
                            InstructionKind::Copy {
                                source: read(source),
                            },
                            self.ty(expr),
                        );
                    }
                    if matches!(name.as_str(), "validate_utf8" | "to_utf8_string") {
                        let source = self.lower_expr(base)?;
                        let source = read(self.borrow(source, Access::Borrow)?);
                        let length = self.lower_expr(&arguments[0])?;
                        let length = read(self.scalar(length)?);
                        return self.emit(
                            expr.span,
                            InstructionKind::ValidateUtf8 {
                                source,
                                length,
                                construct_string: name == "to_utf8_string",
                            },
                            self.ty(expr),
                        );
                    }
                    if name == "clear" {
                        let PathTarget::Local(target) = self.path(base) else {
                            unreachable!("checked List clear receiver")
                        };
                        self.emit(expr.span, InstructionKind::ListClear { target }, None);
                        return self.unit(expr.span);
                    }
                    if name == "pop" {
                        let PathTarget::Local(target) = self.path(base) else {
                            unreachable!("checked List pop receiver")
                        };
                        return self.emit(
                            expr.span,
                            InstructionKind::ListPop { target },
                            self.ty(expr),
                        );
                    }
                    if name == "push" {
                        let PathTarget::Local(target) = self.path(base) else {
                            unreachable!("checked List push receiver")
                        };
                        let element_ty = match &self.function.locals[target.0 as usize].ty {
                            Type::List(element) => element.as_ref().clone(),
                            Type::Reference { inner, .. } => match inner.as_ref() {
                                Type::List(element) => element.as_ref().clone(),
                                _ => unreachable!("checked List push receiver"),
                            },
                            _ => unreachable!("checked List push receiver"),
                        };
                        let value = if matches!(element_ty, Type::Primitive(_)) {
                            let value = self.lower_expr(&arguments[0])?;
                            read(self.scalar(value)?)
                        } else {
                            self.owned_element(&arguments[0], &element_ty)?
                        };
                        self.emit(expr.span, InstructionKind::ListPush { target, value }, None);
                        return self.unit(expr.span);
                    }
                    if name == "push_str" {
                        return self.lower_string_push_str(expr, base, &arguments[0]);
                    }
                    if matches!(
                        name.as_str(),
                        "len"
                            | "get"
                            | "contains"
                            | "index_of"
                            | "is_char_boundary"
                            | "byte_at"
                            | "scalar_at"
                    ) {
                        return self.lower_collection_read(expr, base, name, arguments);
                    }
                    let access = match name.as_str() {
                        "borrow" => Access::Borrow,
                        "share" => Access::Share,
                        _ => unreachable!("checked conversion"),
                    };
                    if matches!(base.kind, ExprKind::Index { .. } | ExprKind::Field { .. }) {
                        // A row, element or field that is itself an aggregate: the
                        // chain of addresses is the reference, with `access` on
                        // every level.
                        let (root, projections) = self.lower_place(base)?;
                        return self.address_chain(root, &projections, access, expr.span);
                    }
                    let owner = self.lower_expr(base)?;
                    return self.borrow(owner, access);
                }
                self.lower_call(expr, callee, arguments)
            }
            ExprKind::Struct { fields, .. } => {
                let Some(Type::Struct(id)) = self.ty(expr) else {
                    unreachable!("checked struct literal type")
                };
                let types = self.types;
                let definition = &types[id.0 as usize];
                // Evaluate and capture every initialiser in source order, then
                // hand them to StructNew in declaration order.
                let scope_start = self.owned_locals.len();
                let mut slots: Vec<Option<Operand>> = vec![None; definition.fields.len()];
                for init in fields {
                    let index = definition
                        .fields
                        .iter()
                        .position(|field| field.name == init.name)
                        .expect("checked struct field");
                    let ty = &definition.fields[index].ty;
                    if *ty == Type::String && self.is_direct_string_call(&init.value) {
                        // Keep each finished temporary live while later fields evaluate.
                        let Some(staged) = self.lower_with_temporary_owner(&init.value) else {
                            self.owned_locals.truncate(scope_start);
                            return None;
                        };
                        slots[index] = Some(consume(staged));
                        continue;
                    }
                    let Some(value) = self.lower_expr(&init.value) else {
                        self.owned_locals.truncate(scope_start);
                        return None;
                    };
                    let operand = if *ty == Type::String
                        && matches!(init.value.kind, ExprKind::Path(_))
                        && matches!(value.source, Source::Local(id)
                            if self.function.locals[id.0 as usize].ty == Type::String)
                    {
                        // A later initializer can return or leave the loop.
                        // Register the move as a lexical owner before evaluating it.
                        let staged = self.hidden_local(
                            "String field initializer",
                            Type::String,
                            init.value.span,
                        );
                        self.initialize_local(staged, consume(value), init.value.span);
                        consume(op(Source::Local(staged), init.value.span))
                    } else if self.is_string_tuple(ty)
                        || self.is_string_transport_owner(ty)
                        || (matches!(ty, Type::Array { .. }) && self.is_string_owner_struct(ty))
                    {
                        let Some(owned) = self.owned_to(value, ty) else {
                            self.owned_locals.truncate(scope_start);
                            return None;
                        };
                        let staged = self.hidden_local(
                            "nested String tuple field",
                            ty.clone(),
                            init.value.span,
                        );
                        self.initialize_local(staged, owned, init.value.span);
                        consume(op(Source::Local(staged), init.value.span))
                    } else if let Some(operand) = self.owned_captured(value, ty) {
                        operand
                    } else {
                        self.owned_locals.truncate(scope_start);
                        return None;
                    };
                    slots[index] = Some(operand);
                }
                let result = self.emit(
                    expr.span,
                    InstructionKind::StructNew {
                        ty: id,
                        fields: slots
                            .into_iter()
                            .map(|slot| slot.expect("checked complete struct literal"))
                            .collect(),
                    },
                    Some(Type::Struct(id)),
                );
                self.end_owned_locals(scope_start, expr.span);
                self.owned_locals.truncate(scope_start);
                result
            }
            ExprKind::Block(block) => self.lower_block(block),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.lower_if(expr, condition, then_branch, else_branch.as_deref()),
            ExprKind::Match { scrutinee, arms } => self.lower_match(expr, scrutinee, arms),
        }
    }
    /// `match` over an enum or tuple, with patterns nested to any depth.
    ///
    /// The scrutinee lives in one place for the whole match: a hidden owner
    /// local (consuming match) or a reference to the matched place (in-place
    /// match). The decision phase only reads: it compiles the pattern matrix
    /// into a tree of `EnumTag` / `Switch` blocks, deriving a reference to
    /// each nested payload it must test with `VariantAddr` / `FieldAddr`.
    /// Each leaf binds for the arm it selected, then jumps to that arm's body
    /// block, which is lowered exactly once. A consuming match moves each
    /// bound payload out of the scrutinee (the last extraction from a value
    /// consumes it) and releases every unbound owned part exactly once; an
    /// in-place match copies primitive payloads and lends aggregates.
    fn lower_match(&mut self, expr: &Expr, scrutinee: &Expr, arms: &[MatchArm]) -> Option<Operand> {
        let fact = self.matches[&self.id(expr)];
        let span = scrutinee.span;
        // `owner` is the hidden owner of a consuming match; `root` is the
        // local the decision phase reads (the owner, or the reference to the
        // matched place of an in-place match).
        let (owner, root, root_ty) = if fact.borrowed {
            let reference = if matches!(
                scrutinee.kind,
                ExprKind::Index { .. } | ExprKind::Field { .. }
            ) {
                let (root, projections) = self.lower_place(scrutinee)?;
                self.address_chain(root, &projections, Access::Borrow, span)?
            } else {
                self.lower_expr(scrutinee)?
            };
            let Some(Type::Reference { inner, .. }) = self.operand_type(reference) else {
                unreachable!("checked borrowing match scrutinee")
            };
            let root = match reference.source {
                Source::Local(local) => local,
                _ => {
                    let local = self.hidden_local(
                        "match scrutinee",
                        self.operand_type(reference)
                            .expect("typed match scrutinee reference"),
                        span,
                    );
                    self.emit(
                        span,
                        InstructionKind::Assign {
                            target: local,
                            value: consume(reference),
                            initialize: true,
                        },
                        None,
                    );
                    local
                }
            };
            (None, root, *inner)
        } else {
            let source = self.lower_expr(scrutinee)?;
            let Some(ty @ (Type::Enum(_) | Type::Struct(_))) = self.operand_type(source) else {
                unreachable!("checked match scrutinee")
            };
            let cell = self.hidden_local("match scrutinee", ty.clone(), span);
            let moved = self.owned(source)?;
            self.emit(
                span,
                InstructionKind::Assign {
                    target: cell,
                    value: moved,
                    initialize: true,
                },
                None,
            );
            (Some(cell), cell, ty)
        };
        let join_id = self.new_block();
        let parameter = self.ty(expr).map(|ty| {
            let id = self.new_value(ty);
            self.function.blocks[join_id.0 as usize].parameters.push(id);
            id
        });
        let plan = MatchPlan {
            arms: &fact.arms,
            bodies: arms.iter().map(|_| self.new_block()).collect(),
            owner,
            root,
            root_ty: root_ty.clone(),
        };
        let rows = fact
            .arms
            .iter()
            .enumerate()
            .map(|(arm, fact)| MatchRow {
                arm,
                patterns: vec![&fact.pattern],
            })
            .collect();
        self.decide_match(
            &plan,
            rows,
            vec![MatchOccurrence {
                reference: root,
                ty: root_ty,
                direct_owner: owner.is_some(),
            }],
            true,
            arms,
            span,
        )?;
        let mut reaches = false;
        for ((arm, arm_fact), body) in arms.iter().zip(&fact.arms).zip(&plan.bodies) {
            let scope_start = self.owned_locals.len();
            self.current = Some(*body);
            // The leaves bound this arm's locals; the body owns their cleanup.
            let mut bindings = Vec::new();
            arm_fact.pattern.collect_bindings(&mut bindings);
            for local in bindings {
                let ty = &self.function.locals[local.0 as usize].ty;
                if matches!(ty, Type::String | Type::List(_)) || self.is_string_owner_struct(ty) {
                    self.owned_locals.push(local);
                }
            }
            if let Some(value) = self.lower_expr(&arm.body) {
                if let Some(value) = self.preserve_scope_result(value, scope_start) {
                    self.end_owned_locals(scope_start, arm.body.span);
                    self.join(join_id, value, arm.body.span);
                    reaches = true;
                }
            }
            self.owned_locals.truncate(scope_start);
        }
        self.current = reaches.then_some(join_id);
        parameter.map(|id| op(Source::Value(id), expr.span))
    }
    /// Compile the pattern matrix `rows` over the `occurrences` (the values
    /// still to inspect) into decision blocks; every leaf binds for the first
    /// row that matches and jumps to that arm's body. `owner_in_scope` says
    /// whether the consuming match's owner is still a live owner at this
    /// point: a `Switch` on the owner drops it on edges whose variant owns
    /// no heap storage, which the ownership validator mirrors.
    #[allow(clippy::too_many_arguments)]
    fn decide_match(
        &mut self,
        plan: &MatchPlan<'a>,
        rows: Vec<MatchRow<'a>>,
        occurrences: Vec<MatchOccurrence>,
        owner_in_scope: bool,
        arms: &[MatchArm],
        span: Span,
    ) -> Option<()> {
        let current = self.current.expect("match decision block");
        let Some(first) = rows.first() else {
            // Exhaustiveness is proven before lowering; no value reaches here.
            self.finish(current, TerminatorKind::Unreachable, Some(span));
            return Some(());
        };
        let Some(column) = first
            .patterns
            .iter()
            .position(|pattern| !irrefutable_pattern(pattern))
        else {
            let arm = first.arm;
            let pattern_span = arms[arm].pattern.span;
            let pattern = &plan.arms[arm].pattern;
            if plan.owner.is_none() {
                let mut reference = op(Source::Local(plan.root), pattern_span);
                reference.mode = UseMode::Borrow;
                self.bind_in_place(pattern, reference, &plan.root_ty, pattern_span)?;
            } else {
                let cell = plan.owner.expect("consuming match owner");
                self.move_out_of(pattern, cell, &plan.root_ty, owner_in_scope, pattern_span)?;
            }
            self.goto(plan.bodies[arm], Vec::new(), pattern_span);
            return Some(());
        };
        let occurrence = occurrences[column].clone();
        let types = self.types;
        let mut rest_occurrences = occurrences;
        rest_occurrences.remove(column);
        let reference = || {
            let mut base = op(Source::Local(occurrence.reference), span);
            base.mode = UseMode::Borrow;
            base
        };
        match &occurrence.ty {
            Type::Enum(enum_id) => {
                let definition = &types[enum_id.0 as usize];
                let mut present: Vec<u32> = rows
                    .iter()
                    .filter_map(|row| match row.patterns[column] {
                        MatchPattern::Variant { variant, .. } => Some(*variant),
                        _ => None,
                    })
                    .collect();
                present.sort_unstable();
                present.dedup();
                let mut tag_base = reference();
                if occurrence.direct_owner {
                    tag_base.mode = UseMode::Read;
                }
                let tag = self.emit(
                    span,
                    InstructionKind::EnumTag { base: tag_base },
                    Some(Type::Primitive(Primitive::U32)),
                )?;
                let variant_blocks: Vec<(u32, BlockId)> = present
                    .iter()
                    .map(|variant| (*variant, self.new_block()))
                    .collect();
                let default_block =
                    (present.len() < definition.variants.len()).then(|| self.new_block());
                let edge = |target| Edge {
                    target,
                    arguments: Vec::new(),
                };
                self.finish(
                    current,
                    TerminatorKind::Switch {
                        tag: read(tag),
                        ty: *enum_id,
                        targets: variant_blocks
                            .iter()
                            .map(|(variant, block)| (*variant, edge(*block)))
                            .collect(),
                        default: default_block.map(edge),
                    },
                    Some(span),
                );
                for (variant, block) in variant_blocks {
                    self.current = Some(block);
                    let payload = &definition.variants[variant as usize].payload;
                    let needed: Vec<usize> = (0..payload.len())
                        .filter(|field| {
                            rows.iter().any(|row| {
                                matches!(row.patterns[column], MatchPattern::Variant { variant: found, args }
                                    if *found == variant && !irrefutable_pattern(&args[*field]))
                            })
                        })
                        .collect();
                    let mut children = Vec::new();
                    for field in &needed {
                        let child = self.variant_reference(
                            reference(),
                            variant,
                            *field as u32,
                            payload[*field].clone(),
                            span,
                        )?;
                        children.push(MatchOccurrence {
                            reference: child,
                            ty: payload[*field].clone(),
                            direct_owner: false,
                        });
                    }
                    let specialized = rows
                        .iter()
                        .filter_map(|row| {
                            let replacement: Vec<&MatchPattern> = match row.patterns[column] {
                                MatchPattern::Variant {
                                    variant: found,
                                    args,
                                } => {
                                    if *found != variant {
                                        return None;
                                    }
                                    needed.iter().map(|field| &args[*field]).collect()
                                }
                                _ => needed.iter().map(|_| &MATCH_WILDCARD).collect(),
                            };
                            Some(row.replacing(column, replacement))
                        })
                        .collect();
                    let mut next = rest_occurrences.clone();
                    next.splice(column..column, children);
                    // The validator drops the owner on an edge to a variant
                    // that owns no storage.
                    let in_scope = if occurrence.direct_owner {
                        owner_in_scope && payload.iter().any(|ty| self.owns_storage(ty))
                    } else {
                        owner_in_scope
                    };
                    self.decide_match(plan, specialized, next, in_scope, arms, span)?;
                }
                if let Some(block) = default_block {
                    self.current = Some(block);
                    let defaults = rows
                        .iter()
                        .filter(|row| irrefutable_pattern(row.patterns[column]))
                        .map(|row| row.replacing(column, Vec::new()))
                        .collect();
                    self.decide_match(
                        plan,
                        defaults,
                        rest_occurrences,
                        owner_in_scope,
                        arms,
                        span,
                    )?;
                }
            }
            Type::Struct(struct_id) => {
                let definition = &types[struct_id.0 as usize];
                let fields: Vec<Type> = definition.fields.iter().map(|f| f.ty.clone()).collect();
                let needed: Vec<usize> = (0..fields.len())
                    .filter(|field| {
                        rows.iter().any(|row| {
                            matches!(row.patterns[column], MatchPattern::Tuple(args)
                                if !irrefutable_pattern(&args[*field]))
                        })
                    })
                    .collect();
                let mut children = Vec::new();
                for field in &needed {
                    let child = self.field_addr_index(reference(), *field, Access::Borrow, span)?;
                    let local = self.hidden_local(
                        "match payload reference",
                        self.operand_type(child).expect("typed field address"),
                        span,
                    );
                    self.emit(
                        span,
                        InstructionKind::Assign {
                            target: local,
                            value: consume(child),
                            initialize: true,
                        },
                        None,
                    );
                    children.push(MatchOccurrence {
                        reference: local,
                        ty: fields[*field].clone(),
                        direct_owner: false,
                    });
                }
                let specialized = rows
                    .iter()
                    .map(|row| {
                        let replacement: Vec<&MatchPattern> = match row.patterns[column] {
                            MatchPattern::Tuple(args) => {
                                needed.iter().map(|field| &args[*field]).collect()
                            }
                            _ => needed.iter().map(|_| &MATCH_WILDCARD).collect(),
                        };
                        row.replacing(column, replacement)
                    })
                    .collect();
                let mut next = rest_occurrences;
                next.splice(column..column, children);
                self.decide_match(plan, specialized, next, owner_in_scope, arms, span)?;
            }
            _ => unreachable!("checked match column type"),
        }
        Some(())
    }
    /// A reference local to payload `field` of `variant`, derived from the
    /// reference `base` (valid on the edge where `variant` is the tag).
    fn variant_reference_operand(
        &mut self,
        mut base: Operand,
        variant: u32,
        field: u32,
        ty: Type,
        span: Span,
    ) -> Option<Operand> {
        base.mode = UseMode::Borrow;
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        let mut reference = self.emit(
            span,
            InstructionKind::VariantAddr {
                loan,
                base,
                variant,
                field,
                access: Access::Borrow,
            },
            Some(Type::Reference {
                access: Access::Borrow,
                inner: Box::new(ty),
            }),
        )?;
        reference.mode = UseMode::Borrow;
        Some(reference)
    }
    /// `variant_reference_operand`, held in a hidden reference local so the
    /// decision tree can use it in later blocks.
    fn variant_reference(
        &mut self,
        base: Operand,
        variant: u32,
        field: u32,
        ty: Type,
        span: Span,
    ) -> Option<LocalId> {
        let reference = self.variant_reference_operand(base, variant, field, ty, span)?;
        let local = self.hidden_local(
            "match payload reference",
            self.operand_type(reference).expect("typed variant address"),
            span,
        );
        self.emit(
            span,
            InstructionKind::Assign {
                target: local,
                value: consume(reference),
                initialize: true,
            },
            None,
        );
        Some(local)
    }
    /// Bind an in-place match arm: primitives are copied, aggregates are
    /// lent as read-only references into the matched place.
    fn bind_in_place(
        &mut self,
        pattern: &MatchPattern,
        reference: Operand,
        ty: &Type,
        span: Span,
    ) -> Option<()> {
        match pattern {
            MatchPattern::Wildcard => {}
            MatchPattern::Bind(local) => {
                let local = local.expect("lowered match binding");
                let value = if matches!(ty, Type::Primitive(_)) {
                    let loaded = self.load_element(reference, span)?;
                    self.owned(loaded)?
                } else {
                    consume(reference)
                };
                self.emit(
                    span,
                    InstructionKind::Assign {
                        target: local,
                        value,
                        initialize: true,
                    },
                    None,
                );
            }
            MatchPattern::Variant { variant, args } => {
                let Type::Enum(id) = ty else {
                    unreachable!("checked variant pattern")
                };
                let payload = &self.types[id.0 as usize].variants[*variant as usize].payload;
                for (field, arg) in args.iter().enumerate() {
                    if matches!(arg, MatchPattern::Wildcard) {
                        continue;
                    }
                    let child = self.variant_reference_operand(
                        reference,
                        *variant,
                        field as u32,
                        payload[field].clone(),
                        span,
                    )?;
                    self.bind_in_place(arg, child, &payload[field], span)?;
                }
            }
            MatchPattern::Tuple(args) => {
                let Type::Struct(id) = ty else {
                    unreachable!("checked tuple pattern")
                };
                let fields = &self.types[id.0 as usize].fields;
                for (field, arg) in args.iter().enumerate() {
                    if matches!(arg, MatchPattern::Wildcard) {
                        continue;
                    }
                    let field_ty = fields[field].ty.clone();
                    let child = self.field_addr_index(reference, field, Access::Borrow, span)?;
                    self.bind_in_place(arg, child, &field_ty, span)?;
                }
            }
        }
        Some(())
    }
    /// Bind a consuming match arm out of the owner local `cell`: bound
    /// payloads move into their binding locals and every other owned part is
    /// released. The last extraction from a value consumes it. `in_scope` is
    /// false when the validator already dropped `cell` because its variant
    /// owns no storage, so there is nothing to end.
    fn move_out_of(
        &mut self,
        pattern: &MatchPattern,
        cell: LocalId,
        ty: &Type,
        in_scope: bool,
        span: Span,
    ) -> Option<()> {
        let types = self.types;
        match pattern {
            MatchPattern::Wildcard => {
                if in_scope {
                    self.release_owned(cell, ty, span);
                }
            }
            MatchPattern::Bind(local) => {
                let local = local.expect("lowered match binding");
                self.bind_local(local, consume(op(Source::Local(cell), span)), span);
            }
            MatchPattern::Variant { variant, args } => {
                let Type::Enum(id) = ty else {
                    unreachable!("checked variant pattern")
                };
                let payload = &types[id.0 as usize].variants[*variant as usize].payload;
                // Unbound owned payloads are extracted too: a consuming
                // extraction clears the whole cell, so each must be released
                // through its own local.
                let needed: Vec<usize> = (0..args.len())
                    .filter(|field| {
                        !matches!(args[*field], MatchPattern::Wildcard)
                            || self.owns_storage(&payload[*field])
                    })
                    .collect();
                let mut children = Vec::new();
                for (position, field) in needed.iter().enumerate() {
                    let mut base = op(Source::Local(cell), span);
                    base.mode = if position + 1 == needed.len() {
                        UseMode::Consume
                    } else {
                        UseMode::Read
                    };
                    let extracted = self.emit(
                        span,
                        InstructionKind::VariantExtract {
                            base,
                            variant: *variant,
                            field: *field as u32,
                        },
                        Some(payload[*field].clone()),
                    )?;
                    self.bind_extracted(
                        &args[*field],
                        extracted,
                        &payload[*field],
                        span,
                        &mut children,
                    );
                }
                if needed.is_empty() && in_scope {
                    self.release_owned(cell, ty, span);
                }
                for (arg, child, child_ty) in children {
                    self.move_out_of(arg, child, &child_ty, true, span)?;
                }
            }
            MatchPattern::Tuple(args) => {
                let Type::Struct(id) = ty else {
                    unreachable!("checked tuple pattern")
                };
                let fields: Vec<Type> = types[id.0 as usize]
                    .fields
                    .iter()
                    .map(|field| field.ty.clone())
                    .collect();
                if args.iter().all(|arg| matches!(arg, MatchPattern::Wildcard)) {
                    if in_scope {
                        self.release_owned(cell, ty, span);
                    }
                    return Some(());
                }
                // A tuple that owns Strings is destructured by extracting
                // every field in order, each straight into its local.
                let mut children = Vec::new();
                for (field, field_ty) in fields.iter().enumerate() {
                    let mut base = op(Source::Local(cell), span);
                    base.mode = if field + 1 == fields.len() {
                        UseMode::Consume
                    } else {
                        UseMode::Read
                    };
                    let extracted = self.emit(
                        span,
                        InstructionKind::Extract {
                            base,
                            field: field as u32,
                        },
                        Some(field_ty.clone()),
                    )?;
                    self.bind_extracted(&args[field], extracted, field_ty, span, &mut children);
                }
                for (arg, child, child_ty) in children {
                    self.move_out_of(arg, child, &child_ty, true, span)?;
                }
            }
        }
        Some(())
    }
    /// Initialize an arm's binding local. The arm body registers the local's
    /// cleanup once, however many leaves reach the arm.
    fn bind_local(&mut self, local: LocalId, value: Operand, span: Span) {
        self.emit(
            span,
            InstructionKind::Assign {
                target: local,
                value,
                initialize: true,
            },
            None,
        );
    }
    /// Put an extracted payload into its local: the binding itself, or a
    /// hidden local that still has sub-patterns or owned parts to settle.
    fn bind_extracted<'p>(
        &mut self,
        pattern: &'p MatchPattern,
        extracted: Operand,
        ty: &Type,
        span: Span,
        children: &mut Vec<(&'p MatchPattern, LocalId, Type)>,
    ) {
        match pattern {
            MatchPattern::Bind(local) => {
                let local = local.expect("lowered match binding");
                self.bind_local(local, consume(extracted), span);
            }
            _ => {
                // The ownership validator recognizes this name: an ignored
                // heap `Ok` payload of a `string ! E` is not an accepted
                // immediate consuming match.
                let name = if matches!(pattern, MatchPattern::Wildcard) {
                    "discarded match payload"
                } else {
                    "match payload"
                };
                let child = self.hidden_local(name, ty.clone(), span);
                self.bind_local(child, consume(extracted), span);
                children.push((pattern, child, ty.clone()));
            }
        }
    }
    fn owns_storage(&self, ty: &Type) -> bool {
        matches!(ty, Type::String) || is_string_owner_aggregate_type(self.types, ty)
    }
    /// End a hidden owner local that no binding takes over. Cleanup is
    /// directed by the type and the active variant, so it releases exactly
    /// the owned parts the value holds.
    fn release_owned(&mut self, local: LocalId, ty: &Type, span: Span) {
        let end = match ty {
            Type::String => InstructionKind::EndStringLocal { local },
            Type::List(_) => InstructionKind::EndListLocal { local },
            _ if self.owns_storage(ty) => InstructionKind::EndStructLocal { local },
            _ => return,
        };
        self.emit(span, end, None);
    }
    /// An enum variant construction. Payload arguments are evaluated and
    /// captured left to right, then handed to `EnumNew` in declaration order.
    fn lower_variant(&mut self, expr: &Expr, arguments: &[Expr]) -> Option<Operand> {
        let VariantUse {
            enum_id, variant, ..
        } = self.variants[&self.id(expr)];
        let Some(id) = enum_id else {
            // Inference stopped at a diverging payload, so there is no enum to build.
            for argument in arguments {
                self.lower_expr(argument)?;
            }
            unreachable!("variant without an inferred type must diverge");
        };
        let types = self.types;
        let declared = &types[id.0 as usize].variants[variant as usize];
        let mut payload = Vec::with_capacity(arguments.len());
        for (argument, ty) in arguments.iter().zip(&declared.payload) {
            let value = self.lower_expr(argument)?;
            // String is the only Ok payload, so it can move at construction
            // without an intervening capture for argument evaluation order.
            let value = if ty == &Type::String
                && types[id.0 as usize].entry_outcome == Some(memobits_ir::EntryOutcome::Result)
                && variant == 0
            {
                self.owned_to(value, ty)?
            } else if self.is_string_tuple(ty) {
                let owned = self.owned_to(value, ty)?;
                let staged =
                    self.hidden_local("enum String tuple payload", ty.clone(), argument.span);
                self.initialize_local(staged, owned, argument.span);
                consume(op(Source::Local(staged), argument.span))
            } else {
                self.owned_captured(value, ty)?
            };
            payload.push(value);
        }
        self.emit(
            expr.span,
            InstructionKind::EnumNew {
                ty: id,
                variant,
                payload,
            },
            Some(Type::Enum(id)),
        )
    }
    fn join(&mut self, target: BlockId, value: Operand, span: Span) {
        let Some(value) = self.owned(value) else {
            return;
        };
        self.goto(target, vec![value], span);
    }
    fn lower_if(
        &mut self,
        expr: &Expr,
        condition: &Expr,
        then_branch: &Block,
        else_branch: Option<&Expr>,
    ) -> Option<Operand> {
        let condition_value = self.lower_expr(condition)?;
        let condition_value = self.scalar(condition_value)?;
        let then_id = self.new_block();
        let else_id = self.new_block();
        let join_id = self.new_block();
        let result_ty = self.ty(expr);
        let parameter = result_ty.map(|ty| {
            let id = self.new_value(ty);
            self.function.blocks[join_id.0 as usize].parameters.push(id);
            id
        });
        let current = self.current.expect("condition completed");
        self.finish(
            current,
            TerminatorKind::Branch {
                condition: read(condition_value),
                then_edge: Edge {
                    target: then_id,
                    arguments: Vec::new(),
                },
                else_edge: Edge {
                    target: else_id,
                    arguments: Vec::new(),
                },
            },
            Some(condition.span),
        );
        self.current = Some(then_id);
        let then_value = self.lower_block(then_branch);
        let mut reaches = false;
        if let Some(value) = then_value {
            self.join(join_id, value, then_branch.span);
            reaches = true;
        }
        self.current = Some(else_id);
        let else_value = match else_branch {
            Some(other) => self.lower_expr(other),
            None => self.unit(expr.span),
        };
        if let Some(value) = else_value {
            self.join(join_id, value, expr.span);
            reaches = true;
        }
        self.current = reaches.then_some(join_id);
        parameter.map(|id| op(Source::Value(id), expr.span))
    }
    fn lower_short_circuit(
        &mut self,
        expr: &Expr,
        operator: &str,
        left: &Expr,
        right: &Expr,
    ) -> Option<Operand> {
        let lhs = self.lower_expr(left)?;
        let lhs = self.scalar(lhs)?;
        let rhs_id = self.new_block();
        let bypass_id = self.new_block();
        let join_id = self.new_block();
        let result = self.new_value(Type::Primitive(Primitive::Bool));
        self.function.blocks[join_id.0 as usize]
            .parameters
            .push(result);
        let current = self.current.expect("left operand completed");
        let (then_id, else_id) = if operator == "&&" {
            (rhs_id, bypass_id)
        } else {
            (bypass_id, rhs_id)
        };
        self.finish(
            current,
            TerminatorKind::Branch {
                condition: read(lhs),
                then_edge: Edge {
                    target: then_id,
                    arguments: Vec::new(),
                },
                else_edge: Edge {
                    target: else_id,
                    arguments: Vec::new(),
                },
            },
            Some(left.span),
        );
        self.current = Some(rhs_id);
        let rhs = self
            .lower_expr(right)
            .and_then(|operand| self.scalar(operand));
        if let Some(rhs) = rhs {
            // A logical operator produces an owned Bool, even when its RHS
            // reads a reference. Do not forward the read-only Load result
            // into the join as an owned value.
            let rhs = if matches!(self.ty(right), Some(Type::Reference { .. }))
                || matches!(right.kind, ExprKind::Index { .. } | ExprKind::Field { .. })
            {
                let neutral = self.constant(
                    right.span,
                    Constant::Bool(true),
                    Type::Primitive(Primitive::Bool),
                )?;
                self.emit(
                    right.span,
                    InstructionKind::Binary {
                        op: BinaryOp::Equal,
                        left: read(neutral),
                        right: read(rhs),
                    },
                    Some(Type::Primitive(Primitive::Bool)),
                )?
            } else {
                rhs
            };
            self.join(join_id, rhs, right.span);
        }
        self.current = Some(bypass_id);
        let bypass = self
            .constant(
                expr.span,
                Constant::Bool(operator == "||"),
                Type::Primitive(Primitive::Bool),
            )
            .expect("live bypass");
        self.join(join_id, bypass, expr.span);
        self.current = Some(join_id);
        Some(op(Source::Value(result), expr.span))
    }
}

fn access_mode(access: Access) -> UseMode {
    match access {
        Access::Owned => UseMode::Consume,
        Access::Borrow => UseMode::Borrow,
        Access::Share => UseMode::Share,
    }
}
