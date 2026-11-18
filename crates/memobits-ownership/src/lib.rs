//! Move and reference-handle availability over typed IR control flow.
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    ArrayInit, Block, Edge, Function, Instruction, InstructionKind, LocalId, Operand, Program,
    Source, TerminatorKind, UseMode,
};
use std::collections::VecDeque;

mod loans;
pub use loans::check_loans;

/// Shared ownership gate for executable IR.
///
/// Availability and loan conflicts are checked independently. Structural failures
/// are reported only once. Source and backend reference support are separate gates.
pub fn check_ownership(program: &Program) -> Vec<Diagnostic> {
    let mut diagnostics = check_moves(program);
    if program.validate().is_ok() {
        diagnostics.extend(check_loans(program));
    }
    diagnostics
}

/// Check local availability after moves. Primitive values are copied implicitly
/// (lowering reads them), so only aggregates and handles are consumed.
/// Borrow and share check availability without consuming their source.
/// Structural IR failures are reported as BE003 before move analysis runs.
pub fn check_moves(program: &Program) -> Vec<Diagnostic> {
    if let Err(errors) = program.validate() {
        return errors
            .into_iter()
            .map(|error| {
                let span = error
                    .function
                    .and_then(|id| program.functions.get(id.0 as usize))
                    .map(|function| function.span);
                diagnostic(3, span, format!("invalid typed IR: {}", error.message))
            })
            .collect();
    }
    let mut diagnostics = Vec::new();
    for function in &program.functions {
        diagnostics.extend(check_function(function));
    }
    diagnostics
}

fn diagnostic(number: u16, span: Option<Span>, message: impl Into<String>) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(
        DiagnosticCode::new(Category::Borrow, number).expect("static BE code"),
        Severity::Error,
        message,
    );
    diagnostic.span = span;
    diagnostic
}

fn reachable(function: &Function) -> Vec<bool> {
    let mut seen = vec![false; function.blocks.len()];
    let mut queue = VecDeque::from([function.entry]);
    while let Some(block) = queue.pop_front() {
        if seen[block.0 as usize] {
            continue;
        }
        seen[block.0 as usize] = true;
        match &function.blocks[block.0 as usize].terminator.kind {
            TerminatorKind::Goto(edge) => queue.push_back(edge.target),
            TerminatorKind::Branch {
                then_edge,
                else_edge,
                ..
            } => {
                queue.push_back(then_edge.target);
                queue.push_back(else_edge.target);
            }
            TerminatorKind::Switch {
                targets, default, ..
            } => {
                for edge in targets.iter().map(|(_, edge)| edge).chain(default) {
                    queue.push_back(edge.target);
                }
            }
            TerminatorKind::Return(_) | TerminatorKind::Unreachable => {}
        }
    }
    seen
}

fn check_function(function: &Function) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for (block, state) in function
        .blocks
        .iter()
        .zip(block_entry_availability(function))
    {
        if let Some(mut state) = state {
            transfer_block(
                function,
                block,
                &mut state,
                Some(&mut diagnostics),
                |_, _| {},
            );
        }
    }
    diagnostics
}

/// Definite availability at each reachable block entry. A false slot may
/// still be initialized on some incoming paths.
fn block_entry_availability(function: &Function) -> Vec<Option<Vec<bool>>> {
    let locals = function.locals.len();
    let slots = locals + function.values.len();
    let mut initial = vec![false; slots];
    for local in &function.parameter_locals {
        initial[local.0 as usize] = true;
    }
    // Availability is a must property. Start reachable non-entry blocks at top
    // and monotonically intersect incoming states until loops settle.
    let mut states: Vec<_> = reachable(function)
        .into_iter()
        .map(|reachable| reachable.then(|| vec![true; slots]))
        .collect();
    states[function.entry.0 as usize] = Some(initial);
    let mut changed = true;
    while changed {
        changed = false;
        for (index, block) in function.blocks.iter().enumerate() {
            let Some(mut state) = states[index].clone() else {
                continue;
            };
            transfer_block(function, block, &mut state, None, |edge, after| {
                let target = states[edge.target.0 as usize]
                    .as_mut()
                    .expect("a successor of a reachable block is reachable");
                changed |= meet(target, after);
            });
        }
    }
    states
}

/// Apply the same transfers during convergence and diagnostic replay.
/// Each successor gets its own state after consuming its edge operands and
/// binding its parameters. A return consumes its result in the supplied state.
fn transfer_block(
    function: &Function,
    block: &Block,
    state: &mut [bool],
    mut diagnostics: Option<&mut Vec<Diagnostic>>,
    mut successor: impl FnMut(&Edge, &[bool]),
) {
    for instruction in &block.instructions {
        transfer_instruction(instruction, state, diagnostics.as_deref_mut(), function);
    }

    let mut transfer_successor =
        |edge, state: &mut [bool], diagnostics: &mut Option<&mut Vec<Diagnostic>>| {
            transfer_edge(edge, state, diagnostics.as_deref_mut(), function);
            successor(edge, state);
        };
    match &block.terminator.kind {
        TerminatorKind::Goto(edge) => transfer_successor(edge, state, &mut diagnostics),
        TerminatorKind::Branch {
            condition,
            then_edge,
            else_edge,
        } => {
            transfer_operand(condition, state, diagnostics.as_deref_mut(), function);
            let mut then_state = state.to_vec();
            transfer_successor(then_edge, &mut then_state, &mut diagnostics);
            transfer_successor(else_edge, state, &mut diagnostics);
        }
        TerminatorKind::Switch {
            tag,
            targets,
            default,
            ..
        } => {
            transfer_operand(tag, state, diagnostics.as_deref_mut(), function);
            for edge in targets.iter().map(|(_, edge)| edge).chain(default) {
                let mut edge_state = state.to_vec();
                transfer_successor(edge, &mut edge_state, &mut diagnostics);
            }
        }
        TerminatorKind::Return(Some(value)) => {
            transfer_operand(value, state, diagnostics, function);
        }
        TerminatorKind::Return(None) | TerminatorKind::Unreachable => {}
    }
}

fn meet(current: &mut [bool], incoming: &[bool]) -> bool {
    let mut changed = false;
    for (here, there) in current.iter_mut().zip(incoming) {
        if *here && !there {
            *here = false;
            changed = true;
        }
    }
    changed
}

fn transfer_instruction(
    instruction: &Instruction,
    state: &mut [bool],
    mut diagnostics: Option<&mut Vec<Diagnostic>>,
    function: &Function,
) {
    match &instruction.kind {
        InstructionKind::Constant(_) => {}
        InstructionKind::Capture(operand) => {
            transfer_operand(operand, state, diagnostics, function)
        }
        InstructionKind::StringIsCharBoundary { source, offset }
        | InstructionKind::StringByteAt { source, offset }
        | InstructionKind::StringScalarAt { source, offset } => {
            transfer_operand(source, state, diagnostics.as_deref_mut(), function);
            transfer_operand(offset, state, diagnostics, function);
        }
        InstructionKind::Copy { source } | InstructionKind::StringLen { source } => {
            transfer_operand(source, state, diagnostics, function);
        }
        InstructionKind::Borrow { owner, .. } => {
            transfer_operand(owner, state, diagnostics, function)
        }
        InstructionKind::ElementAddr { base, index, .. } => {
            let mut diagnostics = diagnostics;
            transfer_operand(base, state, diagnostics.as_deref_mut(), function);
            transfer_operand(index, state, diagnostics, function);
        }
        InstructionKind::FieldAddr { base, .. }
        | InstructionKind::VariantAddr { base, .. }
        | InstructionKind::Extract { base, .. }
        | InstructionKind::EnumTag { base }
        | InstructionKind::VariantExtract { base, .. } => {
            transfer_operand(base, state, diagnostics, function)
        }
        InstructionKind::StructNew { fields, .. } => {
            let mut diagnostics = diagnostics;
            for field in fields {
                transfer_operand(field, state, diagnostics.as_deref_mut(), function);
            }
        }
        InstructionKind::EnumNew { payload, .. } => {
            let mut diagnostics = diagnostics;
            for operand in payload {
                transfer_operand(operand, state, diagnostics.as_deref_mut(), function);
            }
        }
        InstructionKind::ArrayNew { init } => {
            if let ArrayInit::Elements(elements) = init {
                let mut diagnostics = diagnostics;
                for element in elements {
                    transfer_operand(element, state, diagnostics.as_deref_mut(), function);
                }
            }
        }
        InstructionKind::Load { reference } => {
            transfer_operand(reference, state, diagnostics, function)
        }
        InstructionKind::Store { reference, value } => {
            let mut diagnostics = diagnostics;
            transfer_operand(reference, state, diagnostics.as_deref_mut(), function);
            transfer_operand(value, state, diagnostics, function);
        }
        InstructionKind::Unary { operand, .. } => {
            transfer_operand(operand, state, diagnostics, function)
        }
        InstructionKind::Binary { left, right, .. } => {
            let mut diagnostics = diagnostics;
            transfer_operand(left, state, diagnostics.as_deref_mut(), function);
            transfer_operand(right, state, diagnostics, function);
        }
        InstructionKind::Assign {
            target,
            value,
            initialize,
        } => {
            if !initialize && !function.locals[target.0 as usize].mutable {
                if let Some(diagnostics) = diagnostics.as_deref_mut() {
                    diagnostics.push(diagnostic(
                        4,
                        instruction.span,
                        format!(
                            "cannot assign to immutable local '{}'",
                            function.locals[target.0 as usize].name
                        ),
                    ));
                }
            }
            transfer_operand(value, state, diagnostics, function);
            state[target.0 as usize] = true;
        }
        InstructionKind::Call { callee, arguments } => {
            let mut diagnostics = diagnostics;
            transfer_operand(callee, state, diagnostics.as_deref_mut(), function);
            for argument in arguments {
                transfer_operand(argument, state, diagnostics.as_deref_mut(), function);
            }
        }
    }
    if let Some(output) = instruction.output {
        state[function.locals.len() + output.0 as usize] = true;
    }
}

fn transfer_edge(
    edge: &Edge,
    state: &mut [bool],
    diagnostics: Option<&mut Vec<Diagnostic>>,
    function: &Function,
) {
    let mut diagnostics = diagnostics;
    // Edge arguments evaluate left to right. Preserve their availability before
    // consuming them, then bind the target parameters simultaneously (including
    // self-edges whose arguments are also target parameters).
    let mut incoming = Vec::with_capacity(edge.arguments.len());
    for argument in &edge.arguments {
        incoming.push(match argument.source {
            Source::Local(id) => state[id.0 as usize],
            Source::Value(id) => state[function.locals.len() + id.0 as usize],
            Source::Function(_) => true,
        });
        transfer_operand(argument, state, diagnostics.as_deref_mut(), function);
    }
    for (parameter, available) in function.blocks[edge.target.0 as usize]
        .parameters
        .iter()
        .zip(incoming)
    {
        state[function.locals.len() + parameter.0 as usize] = available;
    }
}

fn transfer_operand(
    operand: &Operand,
    state: &mut [bool],
    diagnostics: Option<&mut Vec<Diagnostic>>,
    function: &Function,
) {
    if let Source::Local(LocalId(index)) | Source::Value(memobits_ir::ValueId(index)) =
        operand.source
    {
        let (index, label) = match operand.source {
            Source::Local(_) => (
                index as usize,
                format!("local '{}'", function.locals[index as usize].name),
            ),
            Source::Value(_) => (
                function.locals.len() + index as usize,
                format!("temporary value {}", index),
            ),
            Source::Function(_) => unreachable!(),
        };
        if !state[index] {
            if let Some(diagnostics) = diagnostics {
                diagnostics.push(diagnostic(
                    1,
                    operand.span,
                    format!("{label} is unavailable after a move or before initialization"),
                ));
            }
        }
        if operand.mode == UseMode::Consume {
            state[index] = false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::meet;

    #[test]
    fn availability_join_is_intersection() {
        let mut current = [true, true, false];
        assert!(meet(&mut current, &[true, false, true]));
        assert_eq!(current, [true, false, false]);
        assert!(!meet(&mut current, &[true, true, true]));
    }
}
