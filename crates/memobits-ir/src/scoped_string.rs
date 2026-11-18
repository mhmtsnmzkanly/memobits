//! Validate non-escaping heap String locals and their LIFO cleanup order.

use super::{
    outgoing_edges, push, Function, FunctionId, InstructionKind, LocalId, TerminatorKind,
    ValidationError,
};
use std::collections::{HashSet, VecDeque};

pub(super) fn validate(
    function: &Function,
    id: FunctionId,
    errors: &mut Vec<ValidationError>,
) -> HashSet<LocalId> {
    let locals: HashSet<_> = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction.kind {
            InstructionKind::InitConcatString { target, .. } => Some(target),
            _ => None,
        })
        .collect();
    if locals.is_empty() || function.entry.0 as usize >= function.blocks.len() {
        return locals;
    }
    let mut entries = vec![None; function.blocks.len()];
    entries[function.entry.0 as usize] = Some(Vec::new());
    let mut pending = VecDeque::from([function.entry]);
    while let Some(block_id) = pending.pop_front() {
        let block = &function.blocks[block_id.0 as usize];
        let mut live = entries[block_id.0 as usize].clone().unwrap();
        for instruction in &block.instructions {
            match instruction.kind {
                InstructionKind::InitConcatString { target, .. } => {
                    if live.contains(&target) {
                        push(
                            errors,
                            id,
                            Some(block_id),
                            "concat local initialized while still live",
                        );
                    }
                    live.push(target);
                }
                InstructionKind::EndStringLocal { local } if locals.contains(&local) => {
                    if live.pop() != Some(local) {
                        push(
                            errors,
                            id,
                            Some(block_id),
                            "concat locals must end in reverse initialization order",
                        );
                    }
                }
                InstructionKind::Assign { target, .. } if locals.contains(&target) => {
                    push(errors, id, Some(block_id), "cannot replace a concat local");
                }
                _ => {}
            }
        }
        if matches!(block.terminator.kind, TerminatorKind::Return(_)) && !live.is_empty() {
            push(
                errors,
                id,
                Some(block_id),
                "return leaves a concat local live",
            );
        }
        for edge in outgoing_edges(&block.terminator.kind) {
            let Some(entry) = entries.get_mut(edge.target.0 as usize) else {
                continue;
            };
            match entry {
                Some(incoming) if *incoming != live => {
                    push(
                        errors,
                        id,
                        Some(block_id),
                        "concat local scopes differ at a control-flow join",
                    );
                }
                Some(_) => {}
                None => {
                    *entry = Some(live.clone());
                    pending.push_back(edge.target);
                }
            }
        }
    }
    locals
}
