//! Validate lexical heap String ownership and cleanup across CFG edges.

use super::{
    outgoing_edges, push, Function, FunctionId, InstructionKind, LocalId, Operand, Source,
    TerminatorKind, Type, UseMode, ValidationError,
};
use std::collections::{HashMap, HashSet, VecDeque};

impl super::Program {
    /// Heap-capable locals and owned parameters, propagated through immutable
    /// local moves and direct calls. Literal-only call paths need no cleanup.
    pub fn heap_string_locals(&self) -> Vec<HashSet<LocalId>> {
        let mut facts = vec![HashSet::new(); self.functions.len()];
        let mut moves: HashMap<(usize, LocalId), Vec<(usize, LocalId)>> = HashMap::new();
        let mut pending = Vec::new();
        for (index, function) in self.functions.iter().enumerate() {
            for instruction in function.blocks.iter().flat_map(|block| &block.instructions) {
                match &instruction.kind {
                    InstructionKind::InitConcatString { target, .. } => {
                        if facts[index].insert(*target) {
                            pending.push((index, *target));
                        }
                    }
                    InstructionKind::Assign {
                        target,
                        value,
                        initialize: true,
                    } => {
                        if let Some(source) = local_move_source(function, *target, value) {
                            moves
                                .entry((index, source))
                                .or_default()
                                .push((index, *target));
                        }
                    }
                    InstructionKind::Call { callee, arguments } => {
                        if let Some((source, target, parameter)) =
                            owned_call_transfer(self, callee, arguments)
                        {
                            moves
                                .entry((index, source))
                                .or_default()
                                .push((target, parameter));
                        }
                    }
                    _ => {}
                }
            }
        }
        while let Some(source) = pending.pop() {
            if let Some(targets) = moves.get(&source) {
                for &(function, local) in targets {
                    if facts[function].insert(local) {
                        pending.push((function, local));
                    }
                }
            }
        }
        facts
    }
}

/// A direct call may move a local into its final owned String parameter.
pub(super) fn owned_call_transfer(
    program: &super::Program,
    callee: &Operand,
    arguments: &[Operand],
) -> Option<(LocalId, usize, LocalId)> {
    let Source::Function(target) = callee.source else {
        return None;
    };
    let target = target.0 as usize;
    let function = program.functions.get(target)?;
    let last = arguments.len().checked_sub(1)?;
    if arguments.len() != function.signature.parameters.len() {
        return None;
    }
    let parameter = &function.signature.parameters[last];
    let source = &arguments[last];
    let Source::Local(local) = source.source else {
        return None;
    };
    if parameter.access != super::Access::Owned
        || parameter.ty != Type::String
        || source.mode != UseMode::Consume
    {
        return None;
    }
    Some((local, target, *function.parameter_locals.get(last)?))
}

/// Only a declaration of a new immutable local can receive a heap owner.
pub(super) fn local_move_source(
    function: &Function,
    target: LocalId,
    value: &Operand,
) -> Option<LocalId> {
    let Source::Local(source) = value.source else {
        return None;
    };
    let local = function.locals.get(target.0 as usize)?;
    (source != target
        && value.mode == UseMode::Consume
        && local.ty == Type::String
        && !local.mutable
        && !function.parameter_locals.contains(&target))
    .then_some(source)
}

pub(super) fn validate(
    function: &Function,
    id: FunctionId,
    locals: &HashSet<LocalId>,
    errors: &mut Vec<ValidationError>,
) {
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
                    if *initialize
                        && local_move_source(function, *target, value)
                            .is_some_and(|source| in_scope.contains(&source))
                    {
                        Some(*target)
                    } else {
                        push(errors, id, Some(block_id), "cannot replace a heap String local or initialize it from outside its scope");
                        None
                    }
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
