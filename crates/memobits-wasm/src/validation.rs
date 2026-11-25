//! Pre-encoding validation of IR programs for the Wasm backend.
use super::*;

pub(super) fn validate_string_struct_borrows(
    program: &Program,
    function: &Function,
    structs: &[StructLayout],
    uses: &[u32],
    errors: &mut Vec<Diagnostic>,
) {
    use memobits_ir::Access;

    let is_string_struct =
        |ty: &Type| matches!(ty, Type::Struct(id) if structs[id.0 as usize].has_string_fields());
    // One shared predicate (memobits-ir) for String-owning aggregates admitted
    // for by-value transport: String-owning tuples and flat nominal structs.
    let is_string_owner = |ty: &Type| memobits_ir::is_string_owner_transport(&program.types, ty);
    let is_string_struct_ref =
        |ty: &Type| matches!(ty, Type::Reference { inner, .. } if is_string_struct(inner));

    if function.signature.parameters.iter().any(|p| {
        (is_string_struct(&p.ty)
            && !matches!(p.access, Access::Borrow | Access::Share)
            && !is_string_owner(&p.ty))
            || is_string_struct_ref(&p.ty)
    }) || (is_string_struct(&function.signature.result)
        && !is_string_owner(&function.signature.result))
        || is_string_struct_ref(&function.signature.result)
    {
        errors.push(diagnostic(
            "structs with String fields can cross internal calls only as borrow or share parameters",
            Some(function.span),
        ));
    }

    // A read-only reference local that is only ever initialized from an element,
    // field or variant-payload address (the binding of `loop x in items` over
    // non-copyable List elements, a decision-tree reference into a matched
    // owner, a guard's read-only view of a payload) is a lent place: it
    // behaves like a borrowed parameter.
    let element_producers: HashMap<_, _> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| instruction.output.map(|output| (output, instruction)))
        .collect();
    let lent_elements: HashSet<LocalId> = function
        .locals
        .iter()
        .enumerate()
        .map(|(index, _)| LocalId(index as u32))
        .filter(|local| {
            let assignments: Vec<_> = function
                .blocks
                .iter()
                .flat_map(|block| &block.instructions)
                .filter_map(|instruction| match &instruction.kind {
                    InstructionKind::Assign { target, value, .. } if target == local => Some(value),
                    _ => None,
                })
                .collect();
            matches!(
                function.locals[local.0 as usize].ty,
                Type::Reference {
                    access: Access::Borrow,
                    ..
                }
            ) && !function.parameter_locals.contains(local)
                && !assignments.is_empty()
                && assignments.iter().all(|value| {
                    matches!(value.source, Source::Value(id)
                    if element_producers.get(&id).is_some_and(|producer| matches!(
                        producer.kind,
                        InstructionKind::ElementAddr { access: Access::Borrow, .. }
                            | InstructionKind::FieldAddr { access: Access::Borrow, .. }
                            | InstructionKind::VariantAddr { access: Access::Borrow, .. }
                    )))
                })
        })
        .collect();

    if function.locals.iter().enumerate().any(|(index, local)| {
        is_string_struct_ref(&local.ty)
            && !lent_elements.contains(&LocalId(index as u32))
            && !(function.parameter_locals.contains(&LocalId(index as u32))
                && matches!(
                    local.ty,
                    Type::Reference {
                        access: Access::Borrow | Access::Share,
                        ..
                    }
                ))
    }) {
        errors.push(diagnostic(
            "whole borrows of structs with String fields cannot be stored in local bindings",
            Some(function.span),
        ));
    }

    for instruction in function.blocks.iter().flat_map(|block| &block.instructions) {
        let InstructionKind::Call {
            callee:
                Operand {
                    source: Source::Function(target),
                    ..
                },
            arguments,
        } = &instruction.kind
        else {
            continue;
        };
        let Some(callee) = program.functions.get(target.0 as usize) else {
            continue;
        };
        for (parameter, argument) in callee.signature.parameters.iter().zip(arguments) {
            if parameter.access == Access::Owned
                && is_string_owner(&parameter.ty)
                && !matches!(argument.source, Source::Local(local)
                    if function.locals.get(local.0 as usize).is_some_and(|value| value.ty == parameter.ty)
                        && argument.mode == memobits_ir::UseMode::Consume)
            {
                errors.push(diagnostic(
                    "an owned String struct or tuple argument must move directly from a named local of the same type",
                    argument.span,
                ));
            }
        }
    }

    if !function.values.iter().any(is_string_struct_ref)
        && !function
            .locals
            .iter()
            .any(|local| is_string_struct_ref(&local.ty))
    {
        return;
    }
    let instructions = || function.blocks.iter().flat_map(|block| &block.instructions);
    let producers: HashMap<_, _> = instructions()
        .filter_map(|instruction| instruction.output.map(|output| (output, instruction)))
        .collect();
    fn type_owns_string_storage(program: &Program, ty: &Type, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Type::String => true,
            Type::Struct(id) => {
                let Some(TypeDef {
                    path,
                    kind: TypeDefKind::Struct { fields },
                    ..
                }) = program.types.get(id.0 as usize)
                else {
                    return false;
                };
                if !visited.insert(id.0) {
                    return false;
                }
                let _ = path;
                let owns = fields.iter().any(|field| {
                    field.ty == Type::String
                        || type_owns_string_storage(program, &field.ty, visited)
                });
                visited.remove(&id.0);
                owns
            }
            Type::Enum(id) => {
                let Some(TypeDef {
                    kind: TypeDefKind::Enum { variants },
                    ..
                }) = program.types.get(id.0 as usize)
                else {
                    return false;
                };
                if !visited.insert(id.0) {
                    return false;
                }
                let owns = variants
                    .iter()
                    .flat_map(|variant| &variant.payload)
                    .any(|payload| type_owns_string_storage(program, payload, visited));
                visited.remove(&id.0);
                owns
            }
            Type::Array { element, len } => {
                *len != 0 && type_owns_string_storage(program, element, visited)
            }
            // A List is heap storage whatever it holds, like a String.
            Type::List(_) | Type::Box(_) => true,
            _ => false,
        }
    }
    fn rooted_at_named_owner(
        program: &Program,
        function: &Function,
        structs: &[StructLayout],
        lent_elements: &HashSet<LocalId>,
        source: Source,
        producers: &HashMap<memobits_ir::ValueId, &Instruction>,
        visited: &mut HashSet<memobits_ir::ValueId>,
    ) -> bool {
        let owns_string = |ty: &Type| type_owns_string_storage(program, ty, &mut HashSet::new());
        match source {
            Source::Local(local) => {
                let Some(binding) = function.locals.get(local.0 as usize) else {
                    return false;
                };
                if owns_string(&binding.ty) {
                    return true;
                }
                let Type::Reference { access, inner } = &binding.ty else {
                    return false;
                };
                // A lent place (element, field or payload address held in a
                // local) roots a chain like a borrowed parameter does.
                if lent_elements.contains(&local) && owns_string(inner) {
                    return true;
                }
                function.parameter_locals.contains(&local)
                    && matches!(access, Access::Borrow | Access::Share)
                    && owns_string(inner)
                    && function
                        .parameter_locals
                        .iter()
                        .position(|parameter| *parameter == local)
                        .and_then(|position| function.signature.parameters.get(position))
                        .is_some_and(|parameter| parameter.access == *access)
            }
            Source::Value(value) if visited.insert(value) => {
                let Some(instruction) = producers.get(&value) else {
                    return false;
                };
                let base = match &instruction.kind {
                    InstructionKind::FieldAddr {
                        base,
                        access: Access::Borrow | Access::Share,
                        ..
                    }
                    | InstructionKind::ElementAddr {
                        base,
                        access: Access::Borrow | Access::Share,
                        ..
                    }
                    | InstructionKind::VariantAddr {
                        base,
                        access: Access::Borrow | Access::Share,
                        ..
                    }
                    | InstructionKind::Borrow {
                        owner: base,
                        access: Access::Borrow | Access::Share,
                        ..
                    } => base.source,
                    _ => return false,
                };
                rooted_at_named_owner(
                    program,
                    function,
                    structs,
                    lent_elements,
                    base,
                    producers,
                    visited,
                )
            }
            _ => false,
        }
    }
    let mut projection_fields = HashMap::<memobits_ir::ValueId, u32>::new();
    let mut projection_reborrows =
        HashMap::<memobits_ir::ValueId, Vec<memobits_ir::ValueId>>::new();
    for instruction in instructions() {
        match &instruction.kind {
            InstructionKind::FieldAddr {
                base,
                access: Access::Borrow | Access::Share,
                ..
            } => {
                if let Source::Value(value) = base.source {
                    *projection_fields.entry(value).or_default() += 1;
                }
            }
            InstructionKind::ElementAddr {
                base,
                access: Access::Borrow | Access::Share,
                ..
            } => {
                if let Source::Value(value) = base.source {
                    *projection_fields.entry(value).or_default() += 1;
                }
            }
            InstructionKind::Borrow {
                owner:
                    Operand {
                        source: Source::Value(value),
                        ..
                    },
                access: Access::Borrow | Access::Share,
                ..
            } => {
                if let Some(output) = instruction.output {
                    projection_reborrows.entry(*value).or_default().push(output);
                }
            }
            InstructionKind::SwapPlaces { left, right } => {
                for operand in [left, right] {
                    if let Source::Value(value) = operand.source {
                        *projection_fields.entry(value).or_default() += 1;
                    }
                }
            }
            _ => {}
        }
    }
    fn is_projection_chain(
        value: memobits_ir::ValueId,
        uses: &[u32],
        projection_fields: &HashMap<memobits_ir::ValueId, u32>,
        projection_reborrows: &HashMap<memobits_ir::ValueId, Vec<memobits_ir::ValueId>>,
        visited: &mut HashSet<memobits_ir::ValueId>,
    ) -> bool {
        if !visited.insert(value) {
            return false;
        }
        let fields = projection_fields.get(&value).copied().unwrap_or_default();
        let reborrows = projection_reborrows
            .get(&value)
            .map_or(&[][..], Vec::as_slice);
        let recognized_uses = fields.saturating_add(reborrows.len() as u32);
        let valid = recognized_uses != 0
            && uses.get(value.0 as usize) == Some(&recognized_uses)
            && reborrows.iter().all(|child| {
                is_projection_chain(
                    *child,
                    uses,
                    projection_fields,
                    projection_reborrows,
                    visited,
                )
            });
        visited.remove(&value);
        valid
    }
    let projected_struct_refs: HashSet<_> = function
        .values
        .iter()
        .enumerate()
        .filter_map(|(index, ty)| {
            let value = memobits_ir::ValueId(index as u32);
            (is_string_struct_ref(ty)
                && is_projection_chain(
                    value,
                    uses,
                    &projection_fields,
                    &projection_reborrows,
                    &mut HashSet::new(),
                )
                && rooted_at_named_owner(
                    program,
                    function,
                    structs,
                    &lent_elements,
                    Source::Value(value),
                    &producers,
                    &mut HashSet::new(),
                ))
            .then_some(value)
        })
        .collect();
    // A call argument that is a reference produced by a single-use chain of
    // `borrow`/`share` reborrows and field or element projections is allowed
    // when the chain is rooted at a named owner (or a borrowed parameter) that
    // holds String storage: `grid[i][j].borrow()`, `bag.items[0].borrow()`,
    // `d.title.size()`.
    let single_use_chain = |value: ValueId| -> Option<(Vec<ValueId>, Source)> {
        let mut current = value;
        let mut chain = Vec::new();
        loop {
            if uses.get(current.0 as usize) != Some(&1) || chain.len() > function.values.len() {
                return None;
            }
            let producer = producers.get(&current)?;
            let base = match &producer.kind {
                InstructionKind::Borrow {
                    owner: base,
                    access: Access::Borrow | Access::Share,
                    ..
                }
                | InstructionKind::ElementAddr {
                    base,
                    access: Access::Borrow | Access::Share,
                    ..
                }
                | InstructionKind::FieldAddr {
                    base,
                    access: Access::Borrow | Access::Share,
                    ..
                } => base,
                _ => return None,
            };
            chain.push(current);
            match base.source {
                Source::Value(next) => current = next,
                root => return Some((chain, root)),
            }
        }
    };
    let mut allowed = HashSet::new();
    for instruction in instructions() {
        if let InstructionKind::Assign {
            target,
            value:
                Operand {
                    source: Source::Value(value),
                    ..
                },
            ..
        } = &instruction.kind
        {
            if lent_elements.contains(target) {
                allowed.insert(*value);
            }
        }
    }
    let mut forwarded_parameter = false;
    for instruction in instructions() {
        // A closure's captures are passed to its lifted function like call arguments.
        let arguments = match &instruction.kind {
            InstructionKind::Call {
                callee:
                    Operand {
                        source: Source::Function(_),
                        ..
                    },
                arguments,
            } => arguments,
            InstructionKind::ClosureNew { captures, .. } => captures,
            _ => continue,
        };
        for argument in arguments {
            let value = match argument.source {
                Source::Local(local)
                    if is_string_struct_ref(&function.locals[local.0 as usize].ty) =>
                {
                    forwarded_parameter = true;
                    continue;
                }
                Source::Value(value) => value,
                _ => continue,
            };
            let Some((chain, root @ Source::Local(_))) = single_use_chain(value) else {
                continue;
            };
            // The root stays a named owner local (a borrowed parameter cannot
            // be forwarded as a whole struct; see `forwarded_parameter`).
            // A lent place (a payload or content reference held in a local,
            // such as a box's value) roots the chain like a named owner does.
            if matches!(root, Source::Local(local)
            if function.locals.get(local.0 as usize).is_some_and(|binding| {
                type_owns_string_storage(program, &binding.ty, &mut HashSet::new())
            })) || matches!(root, Source::Local(local)
                    if lent_elements.contains(&local)
                        && matches!(&function.locals[local.0 as usize].ty,
                            Type::Reference { inner, .. }
                                if type_owns_string_storage(program, inner, &mut HashSet::new())))
            {
                allowed.extend(chain);
            }
        }
    }
    if forwarded_parameter
        || function.values.iter().enumerate().any(|(index, ty)| {
            is_string_struct_ref(ty)
                && !allowed.contains(&ValueId(index as u32))
                && !projected_struct_refs.contains(&ValueId(index as u32))
        })
    {
        errors.push(diagnostic(
            "a whole borrow or share of a struct with String fields requires a named owner and direct use as an internal call argument",
            Some(function.span),
        ));
    }
}

pub(super) fn unsupported_instruction(instruction: &Instruction) -> Option<String> {
    match &instruction.kind {
        InstructionKind::Constant(_)
        | InstructionKind::EndStructLocal { .. }
        | InstructionKind::EndStringLocal { .. }
        | InstructionKind::DropLocal { .. }
        | InstructionKind::Assert { .. }
        | InstructionKind::Capture(_)
        | InstructionKind::Copy { .. }
        | InstructionKind::StringLen { .. }
        | InstructionKind::ListGet { .. }
        | InstructionKind::ListRead { .. }
        | InstructionKind::CollectionSearch { .. }
        | InstructionKind::ListLen { .. }
        | InstructionKind::ListPush { .. }
        | InstructionKind::ListPop { .. }
        | InstructionKind::ListClear { .. }
        | InstructionKind::EndListLocal { .. }
        | InstructionKind::EmptyList
        | InstructionKind::InitConcatString { .. }
        | InstructionKind::StringEquals { .. }
        | InstructionKind::InitInterpolatedString { .. }
        | InstructionKind::StringIsCharBoundary { .. }
        | InstructionKind::StringByteAt { .. }
        | InstructionKind::StringScalarAt { .. }
        | InstructionKind::StringScalarRead { .. }
        | InstructionKind::ValidateUtf8 { .. }
        | InstructionKind::Assign { .. } => None,
        InstructionKind::Cast { .. } => None,
        InstructionKind::Borrow { .. }
        | InstructionKind::Load { .. }
        | InstructionKind::Store { .. }
        | InstructionKind::SwapPlaces { .. }
        | InstructionKind::ReplaceStringField { .. } => None,
        InstructionKind::ArrayNew { .. } | InstructionKind::ElementAddr { .. } => None,
        InstructionKind::StructNew { .. }
        | InstructionKind::EnumNew { .. }
        | InstructionKind::FieldAddr { .. }
        | InstructionKind::VariantAddr { .. }
        | InstructionKind::Extract { .. }
        | InstructionKind::EnumTag { .. }
        | InstructionKind::VariantExtract { .. } => None,
        // Calls through function values are erased to `call_indirect`.
        InstructionKind::Call { .. } => None,
        InstructionKind::ClosureNew { .. } => None,
        InstructionKind::Unary { .. } => None,
        InstructionKind::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            ..
        } => Some(
            "logical and/or must be lowered to control flow before Wasm code generation".into(),
        ),
        InstructionKind::Binary { .. } => None,
    }
}

pub(super) fn primitive_signature<'a>(
    mut parameters: impl Iterator<Item = &'a memobits_ir::ParameterType>,
    result: &Type,
) -> bool {
    parameters.all(|p| match p.access {
        memobits_ir::Access::Owned => {
            matches!(
                p.ty,
                Type::Primitive(_)
                    | Type::String
                    | Type::List(_)
                    | Type::Box(_)
                    | Type::Array { .. }
                    | Type::Struct(_)
                    | Type::Enum(_)
            )
        }
        memobits_ir::Access::Borrow | memobits_ir::Access::Share => {
            matches!(p.ty, Type::List(_) | Type::Box(_))
                || matches!(p.ty, Type::Primitive(kind) if kind != Primitive::Unit)
                || matches!(
                    p.ty,
                    Type::String | Type::Array { .. } | Type::Struct(_) | Type::Enum(_)
                )
        }
    }) && matches!(
        result,
        Type::Primitive(_)
            | Type::String
            | Type::List(_)
            | Type::Box(_)
            | Type::Array { .. }
            | Type::Struct(_)
            | Type::Enum(_)
    )
}

pub(super) fn supported_type(ty: &Type) -> bool {
    match ty {
        Type::Primitive(_) => true,
        // A struct or enum is an inline frame-cell value, passed internally by address.
        Type::String | Type::Struct(_) | Type::Enum(_) => true,
        Type::List(element) | Type::Box(element) => supported_type(element),
        Type::Reference {
            access: memobits_ir::Access::Borrow | memobits_ir::Access::Share,
            inner,
        } if matches!(inner.as_ref(), Type::List(_) | Type::Box(_)) => supported_type(inner),
        Type::Reference {
            access: memobits_ir::Access::Borrow | memobits_ir::Access::Share,
            inner,
        } => match inner.as_ref() {
            Type::Primitive(kind) => *kind != Primitive::Unit,
            array @ Type::Array { .. } => supported_type(array),
            Type::String | Type::Struct(_) | Type::Enum(_) => true,
            _ => false,
        },
        Type::Array { element, .. } => match element.as_ref() {
            Type::Primitive(kind) => *kind != Primitive::Unit,
            nested @ (Type::Array { .. } | Type::List(_) | Type::Box(_)) => supported_type(nested),
            Type::String | Type::Struct(_) | Type::Enum(_) => true,
            _ => false,
        },
        _ => false,
    }
}
