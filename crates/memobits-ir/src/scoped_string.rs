//! Validate lexical heap String ownership and cleanup across CFG edges.

use super::{
    outgoing_edges, push, Function, FunctionId, InstructionKind, LocalId, Operand, Source,
    TerminatorKind, Type, UseMode, ValidationError,
};
use std::collections::{HashMap, HashSet, VecDeque};

impl Function {
    /// Heap String locals introduced by concat or by a direct immutable move
    /// from a previously classified local.
    pub fn scoped_string_locals(&self) -> HashSet<LocalId> {
        let mut locals = HashSet::new();
        let mut moves: HashMap<LocalId, Vec<LocalId>> = HashMap::new();
        for instruction in self.blocks.iter().flat_map(|block| &block.instructions) {
            match &instruction.kind {
                InstructionKind::InitConcatString { target, .. } => {
                    locals.insert(*target);
                }
                InstructionKind::Assign {
                    target,
                    value,
                    initialize: true,
                } => {
                    if let Some(source) = local_move_source(self, *target, value) {
                        moves.entry(source).or_default().push(*target);
                    }
                }
                _ => {}
            }
        }
        let mut pending: Vec<_> = locals.iter().copied().collect();
        while let Some(source) = pending.pop() {
            if let Some(targets) = moves.get(&source) {
                for &target in targets {
                    if locals.insert(target) {
                        pending.push(target);
                    }
                }
            }
        }
        locals
    }
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
    errors: &mut Vec<ValidationError>,
) -> HashSet<LocalId> {
    let locals = function.scoped_string_locals();
    if locals.is_empty() || function.entry.0 as usize >= function.blocks.len() {
        return locals;
    }
    let mut entries = vec![None; function.blocks.len()];
    entries[function.entry.0 as usize] = Some(HashSet::new());
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
    locals
}
