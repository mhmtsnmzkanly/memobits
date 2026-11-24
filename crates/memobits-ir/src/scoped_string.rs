//! Validate lexical heap String ownership and cleanup across CFG edges.

use super::{
    outgoing_edges, push, Access, ArrayInit, Block, EntryOutcome, Function, FunctionId,
    Instruction, InstructionKind, LocalId, Operand, Source, TerminatorKind, Type, UseMode,
    ValidationError, ValueId,
};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Default, Clone)]
pub struct HeapStrings {
    pub locals: HashSet<LocalId>,
    /// Direct call result bindings, including calls that only return static text.
    pub string_call_bindings: HashSet<LocalId>,
    pub(super) returns_heap: bool,
    pub returns_heap_ok: bool,
    pub(super) writes_heap: HashSet<usize>,
    pub(super) approved_ok: HashSet<ValueId>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Slot {
    Local(usize, LocalId),
    Return(usize),
    ResultReturn(usize),
    ShareWrite(usize, usize),
}

impl super::Program {
    /// Heap ownership propagated through bounded local, call and return edges.
    pub fn heap_strings(&self) -> Vec<HeapStrings> {
        let mut facts = vec![HeapStrings::default(); self.functions.len()];
        let mut moves: HashMap<Slot, Vec<Slot>> = HashMap::new();
        let mut pending = Vec::new();
        for (index, function) in self.functions.iter().enumerate() {
            for (position, local) in function.parameter_locals.iter().copied().enumerate() {
                if function
                    .signature
                    .parameters
                    .get(position)
                    .is_some_and(|parameter| parameter.access == Access::Owned)
                    && function
                        .locals
                        .get(local.0 as usize)
                        .is_some_and(|local| owns_string_aggregate(self, &local.ty))
                {
                    pending.push(Slot::Local(index, local));
                }
            }
            let shares = share_borrows(function);
            for block in &function.blocks {
                let tuple_extractions = tuple_destructure_extractions(self, function, block);
                if let Some((_, source)) = return_capture(block) {
                    moves
                        .entry(Slot::Local(index, source))
                        .or_default()
                        .push(Slot::Return(index));
                } else if let Some(source) = direct_string_tuple_return(self, function, block) {
                    moves
                        .entry(Slot::Local(index, source))
                        .or_default()
                        .push(Slot::Return(index));
                }
                for (position, instruction) in block.instructions.iter().enumerate() {
                    match &instruction.kind {
                        InstructionKind::InitConcatString { target, .. } => {
                            pending.push(Slot::Local(index, *target));
                        }
                        InstructionKind::StructNew { fields, .. } => {
                            if let Some(target) =
                                struct_binding(function, &block.instructions[position..])
                            {
                                for field in fields {
                                    if let Source::Local(source) = field.source {
                                        moves
                                            .entry(Slot::Local(index, source))
                                            .or_default()
                                            .push(Slot::Local(index, target));
                                    }
                                }
                            }
                        }
                        InstructionKind::ArrayNew {
                            init: ArrayInit::Elements(elements),
                        } => {
                            let destination =
                                array_binding(function, &block.instructions[position..])
                                    .map(|target| Slot::Local(index, target))
                                    .or_else(|| {
                                        let output = instruction.output?;
                                        matches!(&block.terminator.kind,
                                    TerminatorKind::Return(Some(Operand {
                                        source: Source::Value(returned),
                                        mode: UseMode::Consume,
                                        ..
                                    })) if *returned == output)
                                        .then_some(Slot::Return(index))
                                    });
                            if let (Some(destination), Some(Type::Array { element, .. })) = (
                                destination,
                                instruction
                                    .output
                                    .and_then(|output| function.values.get(output.0 as usize)),
                            ) {
                                for operand in elements {
                                    for source in owned_storage_sources(
                                        self,
                                        function,
                                        block,
                                        operand.source,
                                        element,
                                        &mut HashSet::new(),
                                    ) {
                                        moves
                                            .entry(Slot::Local(index, source))
                                            .or_default()
                                            .push(destination);
                                    }
                                }
                            }
                        }
                        InstructionKind::ListPop { .. } => {
                            // A popped owner moves into the binding that takes the Option.
                            if let (Some(output), Some(next)) = (
                                instruction.output,
                                block.instructions[position + 1..]
                                    .iter()
                                    .find(|inst| !is_cleanup(inst)),
                            ) {
                                if let InstructionKind::Assign {
                                    target,
                                    value,
                                    initialize: true,
                                } = &next.kind
                                {
                                    if value.source == Source::Value(output)
                                        && value.mode == UseMode::Consume
                                        && function
                                            .values
                                            .get(output.0 as usize)
                                            .is_some_and(|ty| owns_string_aggregate(self, ty))
                                    {
                                        pending.push(Slot::Local(index, *target));
                                    }
                                }
                            }
                        }
                        InstructionKind::Extract { .. } => {
                            if let Some((source, target, _)) = tuple_extractions.get(&position) {
                                let field_type = instruction
                                    .output
                                    .and_then(|value| function.values.get(value.0 as usize));
                                if field_type == Some(&Type::String)
                                    || field_type.is_some_and(|ty| owns_string_aggregate(self, ty))
                                {
                                    moves
                                        .entry(Slot::Local(index, *source))
                                        .or_default()
                                        .push(Slot::Local(index, *target));
                                }
                            }
                        }
                        InstructionKind::VariantExtract { base, .. } => {
                            if let (Source::Local(source), Some(output)) =
                                (base.source, instruction.output)
                            {
                                let final_extract_consumes_owner = base.mode == UseMode::Consume
                                    || block.instructions[position + 1..].iter().any(|later| {
                                        matches!(&later.kind,
                                            InstructionKind::VariantExtract { base: later_base, .. }
                                                if later_base.source == Source::Local(source)
                                                    && later_base.mode == UseMode::Consume)
                                    });
                                if final_extract_consumes_owner
                                    && function
                                        .values
                                        .get(output.0 as usize)
                                        .is_some_and(|ty| owns_string_storage(self, ty))
                                {
                                    let target = block.instructions[position + 1..]
                                        .iter()
                                        .find(|inst| !is_cleanup(inst))
                                        .and_then(|inst| match &inst.kind {
                                            InstructionKind::Assign {
                                                target,
                                                value,
                                                initialize: true,
                                            } if value.source == Source::Value(output)
                                                && value.mode == UseMode::Consume =>
                                            {
                                                Some(*target)
                                            }
                                            _ => None,
                                        });
                                    if let Some(target) = target {
                                        moves
                                            .entry(Slot::Local(index, source))
                                            .or_default()
                                            .push(Slot::Local(index, target));
                                    }
                                }
                            }
                        }
                        InstructionKind::Assign {
                            target,
                            value,
                            initialize,
                        } => {
                            if let Some(source) =
                                local_move_source(function, *target, value, *initialize)
                                    .or_else(|| {
                                        struct_move_source(function, *target, value, *initialize)
                                    })
                                    .or_else(|| {
                                        array_move_source(function, *target, value, *initialize)
                                    })
                            {
                                moves
                                    .entry(Slot::Local(index, source))
                                    .or_default()
                                    .push(Slot::Local(index, *target));
                            }
                        }
                        InstructionKind::ValidateUtf8 {
                            construct_string: true,
                            ..
                        }
                        | InstructionKind::EnumNew { .. } => {
                            if matches!(instruction.kind, InstructionKind::EnumNew { .. }) {
                                let enum_destination =
                                    enum_binding(function, &block.instructions[position..])
                                        .map(|target| Slot::Local(index, target))
                                        .or_else(|| {
                                            let output = instruction.output?;
                                            matches!(block.terminator.kind,
                                        TerminatorKind::Return(Some(Operand {
                                            source: Source::Value(value),
                                            mode: UseMode::Consume,
                                            ..
                                        })) if value == output)
                                            .then_some(Slot::Return(index))
                                        });
                                if let Some(destination) = enum_destination {
                                    if let InstructionKind::EnumNew { payload, .. } =
                                        &instruction.kind
                                    {
                                        for operand in payload {
                                            match operand.source {
                                                Source::Local(source) => {
                                                    moves
                                                        .entry(Slot::Local(index, source))
                                                        .or_default()
                                                        .push(destination);
                                                }
                                                Source::Value(value) => {
                                                    let producer = block.instructions[..position]
                                                        .iter()
                                                        .find(|candidate| {
                                                            candidate.output == Some(value)
                                                        });
                                                    match producer.map(|candidate| &candidate.kind)
                                                    {
                                                        Some(InstructionKind::Capture(
                                                            Operand {
                                                                source: Source::Local(source),
                                                                mode: UseMode::Consume,
                                                                ..
                                                            },
                                                        )) => {
                                                            moves
                                                                .entry(Slot::Local(index, *source))
                                                                .or_default()
                                                                .push(destination);
                                                        }
                                                        Some(InstructionKind::Call {
                                                            callee:
                                                                Operand {
                                                                    source: Source::Function(callee),
                                                                    ..
                                                                },
                                                            ..
                                                        }) => {
                                                            moves
                                                                .entry(Slot::Return(
                                                                    callee.0 as usize,
                                                                ))
                                                                .or_default()
                                                                .push(destination);
                                                        }
                                                        _ => {}
                                                    }
                                                }
                                                Source::Function(_) => {}
                                            }
                                        }
                                    }
                                }
                            }
                            let (value, source) = match instruction.kind {
                                InstructionKind::ValidateUtf8 { .. } => (instruction.output, None),
                                _ => match owned_ok(self, function, instruction) {
                                    Some((value, source)) => (Some(value), Some(source)),
                                    None => (None, None),
                                },
                            };
                            if let Some(value) = value {
                                let destination = if returns_ok(block, position, value) {
                                    Some(Slot::ResultReturn(index))
                                } else {
                                    immediate_result_match(self, function, block, position)
                                        .map(|target| Slot::Local(index, target))
                                };
                                if let Some(destination) = destination {
                                    facts[index].approved_ok.insert(value);
                                    if let Some(source) = source {
                                        moves
                                            .entry(Slot::Local(index, source))
                                            .or_default()
                                            .push(destination);
                                    } else {
                                        pending.push(destination);
                                    }
                                }
                            }
                        }
                        InstructionKind::ReplaceStringField { target, value, .. } => {
                            if let Source::Local(source) = value.source {
                                let parameter = function
                                    .parameter_locals
                                    .iter()
                                    .position(|local| local == target)
                                    .filter(|position| {
                                        function.signature.parameters[*position].access
                                            == Access::Share
                                    });
                                let destination = parameter
                                    .map_or(Slot::Local(index, *target), |parameter| {
                                        Slot::ShareWrite(index, parameter)
                                    });
                                moves
                                    .entry(Slot::Local(index, source))
                                    .or_default()
                                    .push(destination);
                            }
                        }
                        InstructionKind::Store { reference, value } => {
                            if let (Some(parameter), Source::Local(source)) =
                                (string_share_parameter(function, reference), value.source)
                            {
                                moves
                                    .entry(Slot::Local(index, source))
                                    .or_default()
                                    .push(Slot::ShareWrite(index, parameter));
                            }
                        }
                        InstructionKind::Call { callee, arguments } => {
                            for (position, argument) in arguments.iter().enumerate() {
                                if let Some((source, target, parameter)) =
                                    owned_call_transfer(self, callee, position, argument)
                                {
                                    moves
                                        .entry(Slot::Local(index, source))
                                        .or_default()
                                        .push(Slot::Local(target, parameter));
                                }
                                if let Source::Function(callee) = callee.source {
                                    if let Some(owner) =
                                        direct_share_owner(function, &shares, argument)
                                    {
                                        moves
                                            .entry(Slot::ShareWrite(callee.0 as usize, position))
                                            .or_default()
                                            .push(Slot::Local(index, owner));
                                    }
                                }
                            }
                            if let Source::Function(callee) = callee.source {
                                if let Some(target) =
                                    immediate_result_match(self, function, block, position)
                                {
                                    moves
                                        .entry(Slot::ResultReturn(callee.0 as usize))
                                        .or_default()
                                        .push(Slot::Local(index, target));
                                }
                            }
                            if let Some(result) = call_binding_result(
                                self,
                                function,
                                callee,
                                &block.instructions[position..],
                            ) {
                                let (callee, target) = result;
                                if function
                                    .locals
                                    .get(target.0 as usize)
                                    .is_some_and(|local| local.ty == Type::String)
                                {
                                    facts[index].string_call_bindings.insert(target);
                                }
                                moves
                                    .entry(Slot::Return(callee))
                                    .or_default()
                                    .push(Slot::Local(index, target));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        while let Some(source) = pending.pop() {
            let changed = match source {
                Slot::Local(function, local) => facts[function].locals.insert(local),
                Slot::ShareWrite(function, parameter) => {
                    facts[function].writes_heap.insert(parameter)
                }
                Slot::ResultReturn(function) => {
                    !std::mem::replace(&mut facts[function].returns_heap_ok, true)
                }
                Slot::Return(function) => {
                    !std::mem::replace(&mut facts[function].returns_heap, true)
                }
            };
            if changed {
                if let Some(targets) = moves.get(&source) {
                    pending.extend(targets);
                }
            }
        }
        facts
    }
}

fn owned_storage_sources(
    program: &super::Program,
    function: &Function,
    block: &Block,
    source: Source,
    ty: &Type,
    visited: &mut HashSet<ValueId>,
) -> Vec<LocalId> {
    if !owns_string_storage(program, ty) {
        return Vec::new();
    }
    let Source::Value(value) = source else {
        return match source {
            Source::Local(local) => vec![local],
            _ => Vec::new(),
        };
    };
    if !visited.insert(value) {
        return Vec::new();
    }
    let Some(producer) = block
        .instructions
        .iter()
        .find(|instruction| instruction.output == Some(value))
    else {
        visited.remove(&value);
        return Vec::new();
    };
    let mut sources = Vec::new();
    match &producer.kind {
        InstructionKind::Capture(operand) => {
            sources.extend(owned_storage_sources(
                program,
                function,
                block,
                operand.source,
                ty,
                visited,
            ));
        }
        InstructionKind::StructNew { ty: id, fields } => {
            if let Some(definition) = program.types.get(id.0 as usize) {
                if let super::TypeDefKind::Struct { fields: declared } = &definition.kind {
                    for (operand, field) in fields.iter().zip(declared) {
                        sources.extend(owned_storage_sources(
                            program,
                            function,
                            block,
                            operand.source,
                            &field.ty,
                            visited,
                        ));
                    }
                }
            }
        }
        InstructionKind::ArrayNew {
            init: ArrayInit::Elements(elements),
        } => {
            if let Type::Array { element, .. } = ty {
                for operand in elements {
                    sources.extend(owned_storage_sources(
                        program,
                        function,
                        block,
                        operand.source,
                        element,
                        visited,
                    ));
                }
            }
        }
        InstructionKind::EnumNew {
            ty: id,
            variant,
            payload,
        } => {
            if let Some(definition) = program.types.get(id.0 as usize) {
                if let super::TypeDefKind::Enum { variants } = &definition.kind {
                    if let Some(declared) = variants.get(*variant as usize) {
                        for (operand, field) in payload.iter().zip(&declared.payload) {
                            sources.extend(owned_storage_sources(
                                program,
                                function,
                                block,
                                operand.source,
                                field,
                                visited,
                            ));
                        }
                    }
                }
            }
        }
        _ => {}
    }
    visited.remove(&value);
    sources
}

fn owned_ok(
    program: &super::Program,
    function: &Function,
    pack: &Instruction,
) -> Option<(ValueId, LocalId)> {
    let InstructionKind::EnumNew {
        ty,
        variant: 0,
        payload,
    } = &pack.kind
    else {
        return None;
    };
    if program.types.get(ty.0 as usize)?.entry_outcome != Some(EntryOutcome::Result) {
        return None;
    }
    let [Operand {
        source: Source::Local(source),
        mode: UseMode::Consume,
        ..
    }] = payload.as_slice()
    else {
        return None;
    };
    (function.locals.get(source.0 as usize)?.ty == Type::String).then_some((pack.output?, *source))
}

fn returns_ok(block: &Block, position: usize, result: ValueId) -> bool {
    block.instructions[position + 1..].iter().all(is_cleanup)
        && matches!(block.terminator.kind, TerminatorKind::Return(Some(Operand {
            source: Source::Value(value), mode: UseMode::Consume, ..
        })) if value == result)
}

/// A heap Result may cross only argument cleanup, consuming initializations
/// for the match, and extraction of its String into the success arm's local.
pub(super) fn immediate_result_match(
    program: &super::Program,
    function: &Function,
    block: &Block,
    position: usize,
) -> Option<LocalId> {
    let producer = block.instructions.get(position)?;
    let result = producer.output?;
    let Type::Enum(ty) = function.values.get(result.0 as usize)? else {
        return None;
    };
    let definition = program.types.get(ty.0 as usize)?;
    if definition.entry_outcome != Some(EntryOutcome::Result)
        || !matches!(&definition.kind, super::TypeDefKind::Enum { variants }
            if variants.first().is_some_and(|ok| ok.payload == [Type::String]))
    {
        return None;
    }

    let mut after = block.instructions[position + 1..].iter();
    let first = if matches!(producer.kind, InstructionKind::Call { .. }) {
        after.find(|inst| !is_cleanup(inst))?
    } else {
        after.next()?
    };
    let binding = move_initialization(first, Source::Value(result))?;
    let next = after.next()?;
    let (cell, tag) = if let Some(cell) = move_initialization(next, Source::Local(binding)) {
        if binding == cell {
            return None;
        }
        (cell, after.next()?)
    } else {
        (binding, next)
    };
    if after.next().is_some()
        || !matches!(&tag.kind, InstructionKind::EnumTag { base }
        if base.source == Source::Local(cell) && base.mode == UseMode::Read)
    {
        return None;
    }
    let TerminatorKind::Switch {
        tag: selector,
        ty: switched,
        targets,
        default: None,
    } = &block.terminator.kind
    else {
        return None;
    };
    if switched != ty || selector.source != Source::Value(tag.output?) {
        return None;
    }
    let [(first, first_edge), (second, second_edge)] = targets.as_slice() else {
        return None;
    };
    if first_edge.target == second_edge.target
        || !first_edge.arguments.is_empty()
        || !second_edge.arguments.is_empty()
    {
        return None;
    }
    let success = match (*first, *second) {
        (0, 1) => first_edge,
        (1, 0) => second_edge,
        _ => return None,
    };
    let arm = function.blocks.get(success.target.0 as usize)?;
    let [extract, init, ..] = arm.instructions.as_slice() else {
        return None;
    };
    if !matches!(&extract.kind, InstructionKind::VariantExtract { base, variant: 0, field: 0 }
        if base.source == Source::Local(cell) && base.mode == UseMode::Consume)
    {
        return None;
    }
    let target = move_initialization(init, Source::Value(extract.output?))?;
    if function
        .locals
        .get(target.0 as usize)
        .is_some_and(|local| local.name == "discarded match payload")
    {
        return None;
    }
    string_destination(function, target, true).then_some(target)
}

fn move_initialization(instruction: &Instruction, source: Source) -> Option<LocalId> {
    match &instruction.kind {
        InstructionKind::Assign {
            target,
            value,
            initialize: true,
        } if value.source == source && value.mode == UseMode::Consume => Some(*target),
        _ => None,
    }
}

/// A heap replacement may write directly through an incoming String share.
pub(super) fn string_share_parameter(function: &Function, reference: &Operand) -> Option<usize> {
    let Source::Local(local) = reference.source else {
        return None;
    };
    let position = function
        .parameter_locals
        .iter()
        .position(|id| *id == local)?;
    let parameter = function.signature.parameters.get(position)?;
    (reference.mode == UseMode::Share
        && parameter.access == Access::Share
        && parameter.ty == Type::String)
        .then_some(position)
}

pub(super) fn share_borrows(function: &Function) -> HashMap<ValueId, Source> {
    function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|inst| match inst.kind {
            InstructionKind::Borrow {
                owner,
                access: Access::Share,
                ..
            } => Some((inst.output?, owner.source)),
            _ => None,
        })
        .collect()
}

/// Find the owned caller slot behind an explicit whole-local share. Lowering
/// emits the explicit share and a reborrow for the parameter.
pub(super) fn direct_share_owner(
    function: &Function,
    shares: &HashMap<ValueId, Source>,
    argument: &Operand,
) -> Option<LocalId> {
    let Source::Value(value) = argument.source else {
        return None;
    };
    if argument.mode != UseMode::Share {
        return None;
    }
    let source = shares.get(&value)?;
    let owner = match source {
        Source::Value(base) => shares.get(base)?,
        source => source,
    };
    let Source::Local(local) = owner else {
        return None;
    };
    function
        .locals
        .get(local.0 as usize)
        .is_some_and(|local| matches!(local.ty, Type::String | Type::Struct(_)) && local.mutable)
        .then_some(*local)
}

/// Capture the outgoing descriptor before any lexical cleanup runs. This
/// temporary can only feed the return at the end of the same block. Final
/// iteration-loan reads may follow the capture before cleanup.
pub(super) fn return_capture(block: &Block) -> Option<(usize, LocalId)> {
    let TerminatorKind::Return(Some(Operand {
        source: Source::Value(result),
        mode: UseMode::Consume,
        ..
    })) = block.terminator.kind
    else {
        return None;
    };
    let (position, instruction) =
        block
            .instructions
            .iter()
            .enumerate()
            .rev()
            .find(|(_, inst)| {
                !is_cleanup(inst)
                    && !matches!(
                        inst.kind,
                        InstructionKind::Borrow {
                            access: Access::Borrow,
                            ..
                        }
                    )
            })?;
    let InstructionKind::Capture(Operand {
        source: Source::Local(source),
        mode: UseMode::Consume,
        ..
    }) = instruction.kind
    else {
        return None;
    };
    (instruction.output == Some(result)).then_some((position, source))
}

/// Find a direct call result assigned to a permitted local after argument cleanup.
pub(super) fn call_binding(
    program: &super::Program,
    function: &Function,
    instructions: &[Instruction],
    result: &Type,
) -> Option<(usize, LocalId)> {
    let [call, after @ ..] = instructions else {
        return None;
    };
    let InstructionKind::Call {
        callee: Operand {
            source: Source::Function(callee),
            ..
        },
        ..
    } = call.kind
    else {
        return None;
    };
    let output = call.output?;
    let destination = &after.iter().find(|inst| !is_cleanup(inst))?.kind;
    let (target, value) = match destination {
        InstructionKind::Assign {
            target,
            value,
            initialize,
        } => {
            let permitted = match result {
                Type::String => string_destination(function, *target, *initialize),
                Type::List(_) => {
                    (!initialize || !function.parameter_locals.contains(target))
                        && function.locals.get(target.0 as usize).is_some_and(|local| {
                            &local.ty == result && (*initialize || local.mutable)
                        })
                }
                ty if owns_string_aggregate(program, ty) => {
                    *initialize
                        && value.mode == UseMode::Consume
                        && !function.parameter_locals.contains(target)
                        && function
                            .locals
                            .get(target.0 as usize)
                            .is_some_and(|local| local.ty == *result)
                }
                _ => false,
            };
            if !permitted {
                return None;
            }
            (*target, value)
        }
        InstructionKind::Store { reference, value } => {
            (list_share_destination(function, reference, result)?, value)
        }
        _ => return None,
    };
    (value.source == Source::Value(output) && value.mode == UseMode::Consume)
        .then_some((callee.0 as usize, target))
}

fn call_binding_result(
    program: &super::Program,
    function: &Function,
    callee: &Operand,
    instructions: &[Instruction],
) -> Option<(usize, LocalId)> {
    let Source::Function(callee_id) = callee.source else {
        return None;
    };
    let result = program
        .functions
        .get(callee_id.0 as usize)?
        .signature
        .result
        .as_ref();
    if !matches!(result, Type::String) && !owns_string_aggregate(program, result) {
        return None;
    }
    call_binding(program, function, instructions, result)
}

/// Field classification used by the shared transport predicate, so crates
/// that keep their own type representation can reuse the same rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnerFieldShape {
    String,
    Primitive,
    /// A nominal struct (or fixed array of them) that is itself admitted by
    /// the predicate. Callers classify it with their own recursion and a
    /// visited set, so recursive by-value types are never admitted.
    Owner,
    Other,
}

/// A String-owning nominal struct admitted for transport: no Error ancestry,
/// every field is `String`, a primitive, or a nested admitted owner, and at
/// least one field is a `String` or a nested owner.
pub fn is_string_owner_struct(
    has_error_ancestry: bool,
    fields: impl IntoIterator<Item = OwnerFieldShape>,
) -> bool {
    if has_error_ancestry {
        return false;
    }
    let mut owns = false;
    for field in fields {
        match field {
            OwnerFieldShape::String | OwnerFieldShape::Owner => owns = true,
            OwnerFieldShape::Primitive => {}
            OwnerFieldShape::Other => return false,
        }
    }
    owns
}

/// The single predicate for "String-owning aggregate admitted for by-value
/// transport": a String-owning tuple, or a nominal struct whose fields are
/// Strings, primitives, or nested admitted owners (recursively, including
/// fixed arrays of owners).
pub fn is_string_owner_transport(types: &[super::TypeDef], ty: &Type) -> bool {
    fn admitted(types: &[super::TypeDef], id: u32, visited: &mut HashSet<u32>) -> bool {
        let Some(definition) = types.get(id as usize) else {
            return false;
        };
        let super::TypeDefKind::Struct { fields } = &definition.kind else {
            return false;
        };
        if definition.path.module.as_slice() == ["\0tuple"] {
            return tuple_owns_string_in(types, id);
        }
        if !visited.insert(id) {
            return false;
        }
        let result = is_string_owner_struct(
            definition.error_ancestry.is_some(),
            fields
                .iter()
                .map(|field| field_shape(types, &field.ty, visited)),
        );
        visited.remove(&id);
        result
    }
    fn field_shape(
        types: &[super::TypeDef],
        ty: &Type,
        visited: &mut HashSet<u32>,
    ) -> OwnerFieldShape {
        match ty {
            Type::String => OwnerFieldShape::String,
            Type::Primitive(_) => OwnerFieldShape::Primitive,
            Type::Struct(child)
                if types
                    .get(child.0 as usize)
                    .is_some_and(|d| d.path.module.as_slice() != ["\0tuple"])
                    && admitted(types, child.0, visited) =>
            {
                OwnerFieldShape::Owner
            }
            Type::Array { element, len } if *len != 0 => {
                match field_shape(types, element, visited) {
                    OwnerFieldShape::Owner => OwnerFieldShape::Owner,
                    _ => OwnerFieldShape::Other,
                }
            }
            _ => OwnerFieldShape::Other,
        }
    }
    let Type::Struct(id) = ty else {
        return false;
    };
    admitted(types, id.0, &mut HashSet::new())
}

pub(super) fn tuple_owns_string(program: &super::Program, id: u32) -> bool {
    tuple_owns_string_in(&program.types, id)
}

fn tuple_owns_string_in(types: &[super::TypeDef], id: u32) -> bool {
    fn owns(types: &[super::TypeDef], id: u32, visited: &mut HashSet<u32>) -> bool {
        let Some(definition) = types.get(id as usize) else {
            return false;
        };
        let super::TypeDefKind::Struct { fields } = &definition.kind else {
            return false;
        };
        if definition.path.module.as_slice() != ["\0tuple"] || !visited.insert(id) {
            return false;
        }
        let result = fields.iter().any(|field| match &field.ty {
            Type::String => true,
            Type::Struct(child) => owns(types, child.0, visited),
            _ => false,
        });
        visited.remove(&id);
        result
    }
    owns(types, id, &mut HashSet::new())
}

pub(super) fn owns_string_aggregate(program: &super::Program, ty: &Type) -> bool {
    fn owns(program: &super::Program, ty: &Type, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Type::String => true,
            Type::Array { element, len } => *len != 0 && owns(program, element, visited),
            Type::Struct(id) | Type::Enum(id) => {
                let Some(definition) = program.types.get(id.0 as usize) else {
                    return false;
                };
                if !visited.insert(id.0) {
                    return false;
                }
                let result = match &definition.kind {
                    super::TypeDefKind::Struct { fields } => {
                        fields.iter().any(|field| owns(program, &field.ty, visited))
                    }
                    super::TypeDefKind::Enum { variants } => variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|field| owns(program, field, visited)),
                };
                visited.remove(&id.0);
                result
            }
            _ => false,
        }
    }
    matches!(ty, Type::Array { .. } | Type::Struct(_) | Type::Enum(_))
        && owns(program, ty, &mut HashSet::new())
}

pub(super) fn owns_string_storage(program: &super::Program, ty: &Type) -> bool {
    *ty == Type::String || owns_string_aggregate(program, ty)
}

pub(super) fn enum_variant_owns_string_storage(
    program: &super::Program,
    ty: &Type,
    variant: u32,
) -> bool {
    let Type::Enum(id) = ty else {
        return false;
    };
    program.types.get(id.0 as usize).is_some_and(|definition| {
        matches!(&definition.kind, super::TypeDefKind::Enum { variants }
            if variants.get(variant as usize).is_some_and(|variant|
                variant.payload.iter().any(|field| owns_string_storage(program, field))))
    })
}

pub(super) fn enum_binding(function: &Function, instructions: &[Instruction]) -> Option<LocalId> {
    let [constructor, after @ ..] = instructions else {
        return None;
    };
    let output = constructor.output?;
    if !matches!(constructor.kind, InstructionKind::EnumNew { .. }) {
        return None;
    }
    let InstructionKind::Assign {
        target,
        value,
        initialize: true,
    } = &after.iter().find(|inst| !is_cleanup(inst))?.kind
    else {
        return None;
    };
    (matches!(function.locals.get(target.0 as usize)?.ty, Type::Enum(_))
        && value.source == Source::Value(output)
        && value.mode == UseMode::Consume)
        .then_some(*target)
}

pub(super) fn array_binding(function: &Function, instructions: &[Instruction]) -> Option<LocalId> {
    let [constructor, after @ ..] = instructions else {
        return None;
    };
    let output = constructor.output?;
    if !matches!(constructor.kind, InstructionKind::ArrayNew { .. }) {
        return None;
    }
    // A mutable array local may also be reassigned from a new array value.
    let InstructionKind::Assign {
        target,
        value,
        initialize,
    } = &after.iter().find(|inst| !is_cleanup(inst))?.kind
    else {
        return None;
    };
    let binding = function.locals.get(target.0 as usize)?;
    (matches!(binding.ty, Type::Array { .. })
        && (*initialize || (binding.mutable && !function.parameter_locals.contains(target)))
        && value.source == Source::Value(output)
        && value.mode == UseMode::Consume)
        .then_some(*target)
}

pub(super) fn owned_aggregate_call_argument(
    program: &super::Program,
    block: &Block,
    producer_position: usize,
    result: &Type,
) -> bool {
    let Some(output) = block
        .instructions
        .get(producer_position)
        .and_then(|inst| inst.output)
    else {
        return false;
    };
    if !owns_string_aggregate(program, result) {
        return false;
    }
    if matches!(result, Type::Enum(id)
        if program.types.get(id.0 as usize)
            .is_some_and(|definition| definition.entry_outcome == Some(EntryOutcome::Result)))
    {
        return false;
    }
    block.instructions[producer_position + 1..]
        .iter()
        .any(|instruction| {
            let InstructionKind::Call {
                callee:
                    Operand {
                        source: Source::Function(callee),
                        ..
                    },
                arguments,
            } = &instruction.kind
            else {
                return false;
            };
            let Some(target) = program.functions.get(callee.0 as usize) else {
                return false;
            };
            arguments
                .iter()
                .zip(&target.signature.parameters)
                .any(|(argument, parameter)| {
                    argument.source == Source::Value(output)
                        && argument.mode == UseMode::Consume
                        && parameter.access == Access::Owned
                        && parameter.ty == *result
                })
        })
}

/// Recognize the exact extraction sequence emitted for positional tuple
/// destructuring of a tuple that owns String values directly or recursively. Every slot is
/// extracted once, in order, and initialized into a fresh local.
pub(super) fn tuple_destructure_extractions(
    program: &super::Program,
    function: &Function,
    block: &Block,
) -> HashMap<usize, (LocalId, LocalId, u32)> {
    let mut recognized = HashMap::new();
    let mut position = 0;
    while position < block.instructions.len() {
        let Some(Instruction {
            kind: InstructionKind::Extract { base, field: 0 },
            ..
        }) = block.instructions.get(position)
        else {
            position += 1;
            continue;
        };
        let Source::Local(source) = base.source else {
            position += 1;
            continue;
        };
        let Some(Type::Struct(type_id)) = function
            .locals
            .get(source.0 as usize)
            .map(|local| &local.ty)
        else {
            position += 1;
            continue;
        };
        if !tuple_owns_string(program, type_id.0) {
            position += 1;
            continue;
        }
        let Some(super::TypeDef {
            kind: super::TypeDefKind::Struct { fields },
            ..
        }) = program.types.get(type_id.0 as usize)
        else {
            position += 1;
            continue;
        };
        let mut bindings = Vec::with_capacity(fields.len());
        let mut cursor = position;
        let mut valid = true;
        for (slot, field_definition) in fields.iter().enumerate() {
            let Some(Instruction {
                kind:
                    InstructionKind::Extract {
                        base: extract_base,
                        field,
                    },
                output: Some(output),
                ..
            }) = block.instructions.get(cursor)
            else {
                valid = false;
                break;
            };
            let expected_mode = if slot + 1 == fields.len() {
                UseMode::Consume
            } else {
                UseMode::Read
            };
            if extract_base.source != Source::Local(source)
                || *field as usize != slot
                || extract_base.mode != expected_mode
                || function.values.get(output.0 as usize) != Some(&field_definition.ty)
            {
                valid = false;
                break;
            }
            let Some(target) = block
                .instructions
                .get(cursor + 1)
                .and_then(|instruction| move_initialization(instruction, Source::Value(*output)))
            else {
                valid = false;
                break;
            };
            if function.parameter_locals.contains(&target)
                || function
                    .locals
                    .get(target.0 as usize)
                    .map(|local| &local.ty)
                    != Some(&field_definition.ty)
            {
                valid = false;
                break;
            }
            bindings.push((cursor, target, *field));
            cursor += 2;
        }
        if valid && !fields.is_empty() {
            for (extract_position, target, field) in bindings {
                recognized.insert(extract_position, (source, target, field));
            }
            position = cursor;
        } else {
            position += 1;
        }
    }
    recognized
}

fn direct_string_tuple_return(
    program: &super::Program,
    function: &Function,
    block: &Block,
) -> Option<LocalId> {
    if !owns_string_aggregate(program, function.signature.result.as_ref()) {
        return None;
    }
    let TerminatorKind::Return(Some(Operand {
        source: Source::Local(local),
        mode: UseMode::Consume,
        ..
    })) = block.terminator.kind
    else {
        return None;
    };
    Some(local)
}

pub(super) fn list_share_destination(
    function: &Function,
    reference: &Operand,
    referent: &Type,
) -> Option<LocalId> {
    let Source::Local(local) = reference.source else {
        return None;
    };
    let binding = function.locals.get(local.0 as usize)?;
    (matches!(referent, Type::List(_))
        && reference.mode == UseMode::Share
        && (binding.mutable || function.parameter_locals.contains(&local))
        && matches!(&binding.ty,
            Type::Reference { access: Access::Share, inner } if inner.as_ref() == referent))
    .then_some(local)
}

fn struct_binding(function: &Function, instructions: &[Instruction]) -> Option<LocalId> {
    let [constructor, after @ ..] = instructions else {
        return None;
    };
    let output = constructor.output?;
    let InstructionKind::Assign {
        target,
        value,
        initialize: true,
    } = &after.iter().find(|inst| !is_cleanup(inst))?.kind
    else {
        return None;
    };
    (matches!(function.locals.get(target.0 as usize)?.ty, Type::Struct(_))
        && value.source == Source::Value(output)
        && value.mode == UseMode::Consume)
        .then_some(*target)
}

pub(super) fn struct_move_source(
    function: &Function,
    target: LocalId,
    value: &Operand,
    initialize: bool,
) -> Option<LocalId> {
    let Source::Local(source) = value.source else {
        return None;
    };
    let ty = &function.locals.get(target.0 as usize)?.ty;
    (initialize
        && value.mode == UseMode::Consume
        && matches!(ty, Type::Struct(_) | Type::Enum(_))
        && function.locals.get(source.0 as usize)?.ty == *ty
        && !function.parameter_locals.contains(&target))
    .then_some(source)
}

/// A fixed array that owns String storage may move to another whole array local.
pub(super) fn array_move_source(
    function: &Function,
    target: LocalId,
    value: &Operand,
    initialize: bool,
) -> Option<LocalId> {
    let Source::Local(source) = value.source else {
        return None;
    };
    let target_binding = function.locals.get(target.0 as usize)?;
    let source_binding = function.locals.get(source.0 as usize)?;
    (matches!(target_binding.ty, Type::Array { .. })
        && target_binding.ty == source_binding.ty
        && value.mode == UseMode::Consume
        && (initialize || target_binding.mutable)
        && (!initialize || !function.parameter_locals.contains(&target)))
    .then_some(source)
}

fn is_cleanup(instruction: &Instruction) -> bool {
    matches!(
        instruction.kind,
        InstructionKind::EndStringLocal { .. }
            | InstructionKind::EndListLocal { .. }
            | InstructionKind::EndStructLocal { .. }
    )
}

/// A direct call may move a local into an owned String parameter.
pub(super) fn owned_call_transfer(
    program: &super::Program,
    callee: &Operand,
    position: usize,
    source: &Operand,
) -> Option<(LocalId, usize, LocalId)> {
    let Source::Function(target) = callee.source else {
        return None;
    };
    let target = target.0 as usize;
    let function = program.functions.get(target)?;
    let parameter = function.signature.parameters.get(position)?;
    let Source::Local(local) = source.source else {
        return None;
    };
    let owns_string_tuple = owns_string_aggregate(program, &parameter.ty);
    if parameter.access != super::Access::Owned
        || (parameter.ty != Type::String && !owns_string_tuple)
        || source.mode != UseMode::Consume
    {
        return None;
    }
    Some((local, target, *function.parameter_locals.get(position)?))
}

/// A heap owner may move to a new local or replace a mutable local.
pub(super) fn local_move_source(
    function: &Function,
    target: LocalId,
    value: &Operand,
    initialize: bool,
) -> Option<LocalId> {
    let Source::Local(source) = value.source else {
        return None;
    };
    (value.mode == UseMode::Consume && string_destination(function, target, initialize))
        .then_some(source)
}

fn string_destination(function: &Function, target: LocalId, initialize: bool) -> bool {
    function
        .locals
        .get(target.0 as usize)
        .is_some_and(|local| local.ty == Type::String && (initialize || local.mutable))
        && (!initialize || !function.parameter_locals.contains(&target))
}

pub(super) fn validate(
    program: &super::Program,
    function: &Function,
    id: FunctionId,
    facts: &[HeapStrings],
    errors: &mut Vec<ValidationError>,
) {
    let mut locals = facts[id.0 as usize].locals.clone();
    let list_local = |id: LocalId| {
        function
            .locals
            .get(id.0 as usize)
            .is_some_and(|local| matches!(local.ty, Type::List(_)))
    };
    let struct_local = |id: LocalId| {
        function
            .locals
            .get(id.0 as usize)
            .is_some_and(|local| owns_string_aggregate(program, &local.ty))
    };
    locals.extend(
        function
            .locals
            .iter()
            .enumerate()
            .filter_map(|(index, local)| {
                matches!(local.ty, Type::List(_)).then_some(LocalId(index as u32))
            }),
    );
    if locals.is_empty() || function.entry.0 as usize >= function.blocks.len() {
        return;
    }
    let mut entries: Vec<Option<HashSet<LocalId>>> = vec![None; function.blocks.len()];
    entries[function.entry.0 as usize] = Some(
        function
            .parameter_locals
            .iter()
            .copied()
            .filter(|local| locals.contains(local))
            .collect(),
    );
    let mut pending = VecDeque::from([function.entry]);
    while let Some(block_id) = pending.pop_front() {
        let block = &function.blocks[block_id.0 as usize];
        // A moved binding remains in lexical scope. The separate move checker
        // tracks availability, and the descriptor tracks who owns the block.
        let mut in_scope = entries[block_id.0 as usize].clone().unwrap();
        let tuple_extractions = tuple_destructure_extractions(program, function, block);
        for (position, instruction) in block.instructions.iter().enumerate() {
            let initialized = match &instruction.kind {
                InstructionKind::InitConcatString { target, .. } => Some(*target),
                InstructionKind::Extract { base, .. }
                    if tuple_extractions.contains_key(&position)
                        && base.mode == UseMode::Consume =>
                {
                    if let Source::Local(source) = base.source {
                        if locals.contains(&source) && !in_scope.remove(&source) {
                            push(
                                errors,
                                id,
                                Some(block_id),
                                "tuple source owner is unavailable at final destructuring",
                            );
                        }
                    }
                    None
                }
                InstructionKind::VariantExtract { base, .. } if base.mode == UseMode::Consume => {
                    if let Source::Local(source) = base.source {
                        let owns_payload = match &instruction.kind {
                            InstructionKind::VariantExtract { variant, .. } => function
                                .locals
                                .get(source.0 as usize)
                                .is_some_and(|binding| {
                                    enum_variant_owns_string_storage(program, &binding.ty, *variant)
                                }),
                            _ => false,
                        };
                        if locals.contains(&source) && !in_scope.remove(&source) && owns_payload {
                            push(
                                errors,
                                id,
                                Some(block_id),
                                "enum source owner is unavailable at consuming extraction",
                            );
                        }
                    }
                    None
                }
                InstructionKind::Assign {
                    target,
                    value,
                    initialize,
                } if locals.contains(target) => {
                    let source_outside_scope = matches!(value.source, Source::Local(source)
                        if locals.contains(&source) && !in_scope.contains(&source));
                    if (!list_local(*target)
                        && !struct_local(*target)
                        && !string_destination(function, *target, *initialize))
                        || (struct_local(*target)
                            && !initialize
                            && !function.locals.get(target.0 as usize).is_some_and(|local| {
                                matches!(local.ty, Type::Array { .. })
                                    && local.mutable
                                    && !function.parameter_locals.contains(target)
                            }))
                        || source_outside_scope
                        || (!initialize && !in_scope.contains(target))
                    {
                        let message = if list_local(*target) {
                            "List move requires a source local in scope"
                        } else if struct_local(*target) {
                            "a struct owning a heap String requires a new local binding"
                        } else {
                            "heap String assignment requires a whole local in scope or a new binding"
                        };
                        push(errors, id, Some(block_id), message);
                    }
                    initialize.then_some(*target)
                }
                InstructionKind::ReplaceStringField { target, value, .. } => {
                    let outside_scope =
                        |local| locals.contains(&local) && !in_scope.contains(&local);
                    if outside_scope(*target)
                        || matches!(value.source, Source::Local(source) if outside_scope(source))
                    {
                        push(
                            errors,
                            id,
                            Some(block_id),
                            "String field replacement outside the local's scope",
                        );
                    }
                    None
                }
                InstructionKind::ListPush { target, .. }
                | InstructionKind::ListPop { target }
                | InstructionKind::ListClear { target }
                    if list_local(*target) && !in_scope.contains(target) =>
                {
                    push(
                        errors,
                        id,
                        Some(block_id),
                        "List mutation outside the local's scope",
                    );
                    None
                }
                InstructionKind::DropLocal { value } => {
                    if matches!(value.source, Source::Local(local)
                        if locals.contains(&local) && !in_scope.contains(&local))
                    {
                        push(errors, id, Some(block_id), "drop outside the local's scope");
                    }
                    None
                }
                InstructionKind::EndStringLocal { local }
                | InstructionKind::EndListLocal { local }
                | InstructionKind::EndStructLocal { local }
                    if locals.contains(local) =>
                {
                    if !in_scope.remove(local) {
                        push(
                            errors,
                            id,
                            Some(block_id),
                            if list_local(*local) {
                                "List local ends outside its scope"
                            } else if struct_local(*local) {
                                "struct local ends outside its scope"
                            } else {
                                "heap String local ends outside its scope"
                            },
                        );
                    }
                    None
                }
                _ => None,
            };
            if initialized.is_some_and(|target| !in_scope.insert(target)) {
                push(
                    errors,
                    id,
                    Some(block_id),
                    "owned local initialized while still in scope",
                );
            }
        }
        if matches!(block.terminator.kind, TerminatorKind::Return(_)) {
            if let Some((_, source)) = return_capture(block) {
                in_scope.remove(&source);
            }
            if let Some(source) = direct_string_tuple_return(program, function, block) {
                in_scope.remove(&source);
            }
        }
        if matches!(block.terminator.kind, TerminatorKind::Return(_)) && !in_scope.is_empty() {
            push(
                errors,
                id,
                Some(block_id),
                if in_scope.iter().any(|local| list_local(*local)) {
                    "return leaves a List local in scope"
                } else if in_scope.iter().any(|local| struct_local(*local)) {
                    "return leaves a struct owning a heap String in scope"
                } else {
                    "return leaves a heap String local in scope"
                },
            );
        }
        let switch_owner = match &block.terminator.kind {
            TerminatorKind::Switch { tag, targets, .. } => {
                let tag_value = match tag.source {
                    Source::Value(value) => Some(value),
                    _ => None,
                };
                tag_value.and_then(|tag_value| {
                    block.instructions.iter().find_map(|instruction| {
                        if instruction.output != Some(tag_value) {
                            return None;
                        }
                        let InstructionKind::EnumTag { base } = &instruction.kind else {
                            return None;
                        };
                        let Source::Local(local) = base.source else {
                            return None;
                        };
                        let Some(Type::Enum(enum_id)) = function
                            .locals
                            .get(local.0 as usize)
                            .map(|binding| &binding.ty)
                        else {
                            return None;
                        };
                        Some((local, *enum_id, targets.clone()))
                    })
                })
            }
            _ => None,
        };
        for edge in outgoing_edges(&block.terminator.kind) {
            let mut edge_scope = in_scope.clone();
            if let Some((owner, enum_id, targets)) = &switch_owner {
                if locals.contains(owner) {
                    if let Some((variant_index, _)) = targets
                        .iter()
                        .find(|(_, variant_edge)| variant_edge.target == edge.target)
                    {
                        let variant_owns_string = program
                            .types
                            .get(enum_id.0 as usize)
                            .is_some_and(|definition| {
                                matches!(&definition.kind, super::TypeDefKind::Enum { variants }
                                    if variants.get(*variant_index as usize).is_some_and(|variant|
                                        variant.payload.iter().any(|ty|
                                            owns_string_storage(program, ty))))
                            });
                        if !variant_owns_string {
                            edge_scope.remove(owner);
                        }
                    }
                }
            }
            let Some(entry) = entries.get_mut(edge.target.0 as usize) else {
                continue;
            };
            match entry {
                Some(incoming) if *incoming != edge_scope => {
                    push(
                        errors,
                        id,
                        Some(block_id),
                        "owned local scopes differ at a control-flow join",
                    );
                }
                Some(_) => {}
                None => {
                    *entry = Some(edge_scope);
                    pending.push_back(edge.target);
                }
            }
        }
    }
}
