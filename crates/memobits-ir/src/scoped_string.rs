//! Validate lexical heap String ownership and cleanup across CFG edges.

use super::{
    outgoing_edges, push, Access, Block, EntryOutcome, Function, FunctionId, Instruction,
    InstructionKind, LocalId, Operand, Source, TerminatorKind, Type, UseMode, ValidationError,
    ValueId,
};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Default, Clone)]
pub struct HeapStrings {
    pub locals: HashSet<LocalId>,
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
            let shares = share_borrows(function);
            for block in &function.blocks {
                if let Some((_, source)) = return_capture(block) {
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
                        InstructionKind::Assign {
                            target,
                            value,
                            initialize,
                        } => {
                            if let Some(source) =
                                local_move_source(function, *target, value, *initialize)
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
                            if let Some((callee, target)) =
                                call_binding(function, &block.instructions[position..])
                            {
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
        .is_some_and(|local| local.ty == Type::String && local.mutable)
        .then_some(*local)
}

/// Capture the outgoing descriptor before any lexical cleanup runs. This
/// temporary can only feed the return at the end of the same block.
pub(super) fn return_capture(block: &Block) -> Option<(usize, LocalId)> {
    let TerminatorKind::Return(Some(Operand {
        source: Source::Value(result),
        mode: UseMode::Consume,
        ..
    })) = block.terminator.kind
    else {
        return None;
    };
    let (position, instruction) = block
        .instructions
        .iter()
        .enumerate()
        .rev()
        .find(|(_, inst)| !is_cleanup(inst))?;
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

/// A heap call result must be assigned to a whole local after argument cleanup.
pub(super) fn call_binding(
    function: &Function,
    instructions: &[Instruction],
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
    let InstructionKind::Assign {
        target,
        value,
        initialize,
    } = &after.iter().find(|inst| !is_cleanup(inst))?.kind
    else {
        return None;
    };
    let output = call.output?;
    (value.source == Source::Value(output)
        && value.mode == UseMode::Consume
        && string_destination(function, *target, *initialize))
    .then_some((callee.0 as usize, *target))
}

fn is_cleanup(instruction: &Instruction) -> bool {
    matches!(
        instruction.kind,
        InstructionKind::EndStringLocal { .. } | InstructionKind::EndListLocal { .. }
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
    if parameter.access != super::Access::Owned
        || parameter.ty != Type::String
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
        for instruction in &block.instructions {
            let initialized = match &instruction.kind {
                InstructionKind::InitConcatString { target, .. } => Some(*target),
                InstructionKind::Assign {
                    target,
                    value,
                    initialize,
                } if locals.contains(target) => {
                    let source_outside_scope = matches!(value.source, Source::Local(source)
                        if locals.contains(&source) && !in_scope.contains(&source));
                    if (!list_local(*target) && !string_destination(function, *target, *initialize))
                        || source_outside_scope
                        || (!initialize && !in_scope.contains(target))
                    {
                        let message = if list_local(*target) {
                            "List move requires a source local in scope"
                        } else {
                            "heap String assignment requires a whole local in scope or a new binding"
                        };
                        push(errors, id, Some(block_id), message);
                    }
                    initialize.then_some(*target)
                }
                InstructionKind::ListPush { target, .. } if !in_scope.contains(target) => {
                    push(
                        errors,
                        id,
                        Some(block_id),
                        "List push outside the local's scope",
                    );
                    None
                }
                InstructionKind::EndStringLocal { local }
                | InstructionKind::EndListLocal { local }
                    if locals.contains(local) =>
                {
                    if !in_scope.remove(local) {
                        push(
                            errors,
                            id,
                            Some(block_id),
                            if list_local(*local) {
                                "List local ends outside its scope"
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
        if matches!(block.terminator.kind, TerminatorKind::Return(_)) && !in_scope.is_empty() {
            push(
                errors,
                id,
                Some(block_id),
                if in_scope.iter().any(|local| list_local(*local)) {
                    "return leaves a List local in scope"
                } else {
                    "return leaves a heap String local in scope"
                },
            );
        }
        for edge in outgoing_edges(&block.terminator.kind) {
            let Some(entry) = entries.get_mut(edge.target.0 as usize) else {
                continue;
            };
            match entry {
                Some(incoming) if *incoming != in_scope => {
                    push(
                        errors,
                        id,
                        Some(block_id),
                        "owned local scopes differ at a control-flow join",
                    );
                }
                Some(_) => {}
                None => {
                    *entry = Some(in_scope.clone());
                    pending.push_back(edge.target);
                }
            }
        }
    }
}
