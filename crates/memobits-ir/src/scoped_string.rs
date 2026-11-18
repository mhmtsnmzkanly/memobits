//! Validate lexical heap String ownership and cleanup across CFG edges.

use super::{
    outgoing_edges, push, Block, Function, FunctionId, Instruction, InstructionKind, LocalId,
    Operand, Source, TerminatorKind, Type, UseMode, ValidationError,
};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Default, Clone)]
pub struct HeapStrings {
    pub locals: HashSet<LocalId>,
    pub(super) returns_heap: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Slot {
    Local(usize, LocalId),
    Return(usize),
}

impl super::Program {
    /// Heap ownership propagated through bounded local, call and return edges.
    pub fn heap_strings(&self) -> Vec<HeapStrings> {
        let mut facts = vec![HeapStrings::default(); self.functions.len()];
        let mut moves: HashMap<Slot, Vec<Slot>> = HashMap::new();
        let mut pending = Vec::new();
        for (index, function) in self.functions.iter().enumerate() {
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
        .find(|(_, inst)| !matches!(inst.kind, InstructionKind::EndStringLocal { .. }))?;
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
    matches!(instruction.kind, InstructionKind::EndStringLocal { .. })
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
    let locals = &facts[id.0 as usize].locals;
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
                    if !string_destination(function, *target, *initialize)
                        || source_outside_scope
                        || (!initialize && !in_scope.contains(target))
                    {
                        push(errors, id, Some(block_id), "heap String assignment requires a whole local in scope or a new binding");
                    }
                    initialize.then_some(*target)
                }
                InstructionKind::EndStringLocal { local } if locals.contains(local) => {
                    if !in_scope.remove(local) {
                        push(
                            errors,
                            id,
                            Some(block_id),
                            "heap String local ends outside its scope",
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
                    "heap String local initialized while still in scope",
                );
            }
        }
        if matches!(block.terminator.kind, TerminatorKind::Return(_)) && !in_scope.is_empty() {
            push(
                errors,
                id,
                Some(block_id),
                "return leaves a heap String local in scope",
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
                        "heap String scopes differ at a control-flow join",
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
