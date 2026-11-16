//! Experimental loan liveness over validated reference IR.
use std::collections::{BTreeSet, HashMap, VecDeque};

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    Access, ArrayInit, Block, Edge, Function, Instruction, InstructionKind, LocalId, Operand,
    Program, Source, TerminatorKind, Type, UseMode, ValueId,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum LoanKey {
    Site(u32),
    Parameter(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Root {
    Local(u32),
    Value(u32),
    // Checked calls reject overlap whenever either parameter is exclusive.
    // Read-only parameters may alias, but neither can mutate their roots.
    Parameter(u32),
    External,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Provenance {
    roots: BTreeSet<Root>,
    loans: BTreeSet<LoanKey>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LoanInfo {
    roots: BTreeSet<Root>,
    parents: BTreeSet<LoanKey>,
    access: Access,
}

#[derive(Clone)]
struct Liveness {
    before: Vec<Vec<Vec<bool>>>,
    after: Vec<Vec<Vec<bool>>>,
    terminator: Vec<Vec<bool>>,
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

/// Check reference lifetimes and aliasing over valid IR.
///
/// This is a separate experimental pass from `check_moves`; callers that need
/// both availability and loan checking should run both passes.
pub fn check_loans(program: &Program) -> Vec<Diagnostic> {
    if let Err(errors) = program.validate() {
        let mut diagnostics = Vec::new();
        for error in errors {
            let function = error
                .function
                .and_then(|id| program.functions.get(id.0 as usize));
            let unsupported_result = error
                .message
                .contains("function result type cannot be a reference");
            let unsupported_call_result = function.is_some_and(|function| {
                function
                    .blocks
                    .iter()
                    .flat_map(|block| &block.instructions)
                    .any(|instruction| {
                        matches!(instruction.kind, InstructionKind::Call { .. })
                            && instruction.output.is_some_and(|output| {
                                function
                                    .values
                                    .get(output.0 as usize)
                                    .is_some_and(is_reference)
                            })
                    })
            });
            diagnostics.push(diagnostic(
                if unsupported_result || unsupported_call_result {
                    6
                } else {
                    3
                },
                function.map(|function| function.span),
                if unsupported_result || unsupported_call_result {
                    "reference returns are not supported by loan checking".to_owned()
                } else {
                    format!("invalid typed IR: {}", error.message)
                },
            ));
        }
        return diagnostics;
    }

    program
        .functions
        .iter()
        .flat_map(|function| check_function(program, function))
        .collect()
}

fn check_function(program: &Program, function: &Function) -> Vec<Diagnostic> {
    let reachable = reachable(function);
    let liveness = liveness(function, &reachable);
    let (inputs, infos) = provenance(function, &reachable);
    let mut diagnostics = Vec::new();

    for (block_index, block) in function.blocks.iter().enumerate() {
        if !reachable[block_index] {
            continue;
        }
        let mut state = inputs[block_index].clone();
        for (instruction_index, instruction) in block.instructions.iter().enumerate() {
            let before = active_loans(
                function,
                &state,
                &liveness.before[block_index][instruction_index],
                &infos,
            );
            let mut after_state = state.clone();
            transfer_provenance(function, instruction, &mut after_state, &mut infos.clone());
            let after = active_loans(
                function,
                &after_state,
                &liveness.after[block_index][instruction_index],
                &infos,
            );
            check_instruction(
                program,
                function,
                instruction,
                &state,
                &before,
                &after,
                &infos,
                &mut diagnostics,
            );
            transfer_provenance(function, instruction, &mut state, &mut infos.clone());
        }
        check_terminator(
            function,
            block,
            &state,
            &liveness.terminator[block_index],
            &infos,
            &mut diagnostics,
        );
    }
    diagnostics
}

fn reachable(function: &Function) -> Vec<bool> {
    let mut seen = vec![false; function.blocks.len()];
    let mut queue = VecDeque::from([function.entry]);
    while let Some(block) = queue.pop_front() {
        let index = block.0 as usize;
        if index >= seen.len() || seen[index] {
            continue;
        }
        seen[index] = true;
        for edge in edges(&function.blocks[index].terminator.kind) {
            queue.push_back(edge.target);
        }
    }
    seen
}

fn edges(terminator: &TerminatorKind) -> Vec<&Edge> {
    match terminator {
        TerminatorKind::Goto(edge) => vec![edge],
        TerminatorKind::Branch {
            then_edge,
            else_edge,
            ..
        } => vec![then_edge, else_edge],
        TerminatorKind::Return(_) | TerminatorKind::Unreachable => Vec::new(),
    }
}

fn slot_count(function: &Function) -> usize {
    function.locals.len() + function.values.len()
}

fn slot(source: Source, function: &Function) -> Option<usize> {
    match source {
        Source::Local(LocalId(index)) => Some(index as usize),
        Source::Value(ValueId(index)) => Some(function.locals.len() + index as usize),
        Source::Function(_) => None,
    }
}

fn type_at(function: &Function, source: Source) -> Option<&Type> {
    match source {
        Source::Local(local) => function.locals.get(local.0 as usize).map(|local| &local.ty),
        Source::Value(value) => function.values.get(value.0 as usize),
        Source::Function(_) => None,
    }
}

fn is_reference(ty: &Type) -> bool {
    matches!(ty, Type::Reference { .. })
}

fn mark_operand(live: &mut [bool], function: &Function, operand: &Operand) {
    if let Some(index) = slot(operand.source, function) {
        if let Some(mark) = live.get_mut(index) {
            *mark = true;
        }
    }
}

fn instruction_operands(kind: &InstructionKind) -> Vec<&Operand> {
    match kind {
        InstructionKind::Constant(_) => Vec::new(),
        InstructionKind::Capture(operand)
        | InstructionKind::Copy { source: operand }
        | InstructionKind::Unary { operand, .. }
        | InstructionKind::Borrow { owner: operand, .. }
        | InstructionKind::Load { reference: operand } => vec![operand],
        InstructionKind::Store { reference, value } => vec![reference, value],
        InstructionKind::ElementAddr { base, index, .. } => vec![base, index],
        InstructionKind::ArrayNew { init } => match init {
            ArrayInit::Elements(elements) => elements.iter().collect(),
            ArrayInit::Zeroed => Vec::new(),
        },
        InstructionKind::Binary { left, right, .. } => vec![left, right],
        InstructionKind::Assign { value, .. } => vec![value],
        InstructionKind::Call { callee, arguments } => {
            std::iter::once(callee).chain(arguments).collect()
        }
    }
}

fn kill_instruction_def(function: &Function, instruction: &Instruction, live: &mut [bool]) {
    if let Some(output) = instruction.output {
        if let Some(slot) = live.get_mut(function.locals.len() + output.0 as usize) {
            *slot = false;
        }
    }
    if let InstructionKind::Assign { target, .. } = instruction.kind {
        if let Some(slot) = live.get_mut(target.0 as usize) {
            *slot = false;
        }
    }
}

fn map_edge_liveness(function: &Function, edge: &Edge, entry_live: &[Vec<bool>]) -> Vec<bool> {
    let mut live = entry_live
        .get(edge.target.0 as usize)
        .cloned()
        .unwrap_or_else(|| vec![false; slot_count(function)]);
    if let Some(target) = function.blocks.get(edge.target.0 as usize) {
        for (argument, parameter) in edge.arguments.iter().zip(&target.parameters) {
            let parameter_slot = function.locals.len() + parameter.0 as usize;
            let needed = live.get(parameter_slot).copied().unwrap_or(false);
            if let Some(slot) = live.get_mut(parameter_slot) {
                *slot = false;
            }
            if needed {
                mark_operand(&mut live, function, argument);
            }
        }
    }
    live
}

fn compute_block_entry(function: &Function, block: &Block, mut live: Vec<bool>) -> Vec<bool> {
    match &block.terminator.kind {
        TerminatorKind::Goto(edge) => {
            for argument in &edge.arguments {
                mark_operand(&mut live, function, argument);
            }
        }
        TerminatorKind::Branch {
            condition,
            then_edge,
            else_edge,
        } => {
            mark_operand(&mut live, function, condition);
            for argument in then_edge.arguments.iter().chain(&else_edge.arguments) {
                mark_operand(&mut live, function, argument);
            }
        }
        TerminatorKind::Return(Some(value)) => mark_operand(&mut live, function, value),
        TerminatorKind::Return(None) | TerminatorKind::Unreachable => {}
    }
    for instruction in block.instructions.iter().rev() {
        kill_instruction_def(function, instruction, &mut live);
        for operand in instruction_operands(&instruction.kind) {
            mark_operand(&mut live, function, operand);
        }
    }
    live
}

fn liveness(function: &Function, reachable: &[bool]) -> Liveness {
    let slots = slot_count(function);
    let mut entries = vec![vec![false; slots]; function.blocks.len()];
    let mut outs = vec![vec![false; slots]; function.blocks.len()];
    loop {
        let mut changed = false;
        for (index, block) in function.blocks.iter().enumerate().rev() {
            if !reachable[index] {
                continue;
            }
            let mut out = vec![false; slots];
            for edge in edges(&block.terminator.kind) {
                let incoming = map_edge_liveness(function, edge, &entries);
                union_bits(&mut out, &incoming);
            }
            let entry = compute_block_entry(function, block, out.clone());
            if entry != entries[index] || out != outs[index] {
                entries[index] = entry;
                outs[index] = out;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut before = vec![Vec::new(); function.blocks.len()];
    let mut after = vec![Vec::new(); function.blocks.len()];
    let mut terminator = vec![vec![false; slots]; function.blocks.len()];
    for (index, block) in function.blocks.iter().enumerate() {
        before[index] = vec![vec![false; slots]; block.instructions.len()];
        after[index] = vec![vec![false; slots]; block.instructions.len()];
        if !reachable[index] {
            continue;
        }
        let mut live = outs[index].clone();
        let mut term_live = vec![false; slots];
        for edge in edges(&block.terminator.kind) {
            union_bits(&mut term_live, &map_edge_liveness(function, edge, &entries));
        }
        match &block.terminator.kind {
            TerminatorKind::Goto(edge) => {
                for argument in &edge.arguments {
                    mark_operand(&mut term_live, function, argument);
                }
                for argument in &edge.arguments {
                    mark_operand(&mut live, function, argument);
                }
            }
            TerminatorKind::Branch {
                condition,
                then_edge,
                else_edge,
            } => {
                mark_operand(&mut term_live, function, condition);
                for argument in then_edge.arguments.iter().chain(&else_edge.arguments) {
                    mark_operand(&mut term_live, function, argument);
                }
                mark_operand(&mut live, function, condition);
                for argument in then_edge.arguments.iter().chain(&else_edge.arguments) {
                    mark_operand(&mut live, function, argument);
                }
            }
            TerminatorKind::Return(Some(value)) => {
                mark_operand(&mut term_live, function, value);
                mark_operand(&mut live, function, value)
            }
            TerminatorKind::Return(None) | TerminatorKind::Unreachable => {}
        }
        terminator[index] = term_live;
        for instruction_index in (0..block.instructions.len()).rev() {
            let instruction = &block.instructions[instruction_index];
            after[index][instruction_index] = live.clone();
            kill_instruction_def(function, instruction, &mut live);
            for operand in instruction_operands(&instruction.kind) {
                mark_operand(&mut live, function, operand);
            }
            before[index][instruction_index] = live.clone();
        }
    }
    Liveness {
        before,
        after,
        terminator,
    }
}

fn union_bits(target: &mut [bool], source: &[bool]) -> bool {
    let mut changed = false;
    for (target, source) in target.iter_mut().zip(source) {
        if *source && !*target {
            *target = true;
            changed = true;
        }
    }
    changed
}

fn operand_provenance(function: &Function, state: &[Provenance], operand: &Operand) -> Provenance {
    slot(operand.source, function)
        .and_then(|slot| state.get(slot))
        .cloned()
        .unwrap_or_default()
}

fn roots_for_owner(function: &Function, state: &[Provenance], operand: &Operand) -> Provenance {
    if type_at(function, operand.source).is_some_and(is_reference) {
        let mut provenance = operand_provenance(function, state, operand);
        if provenance.roots.is_empty() {
            provenance.roots.insert(Root::External);
        }
        provenance
    } else {
        let mut provenance = Provenance::default();
        match operand.source {
            Source::Local(local) => {
                provenance.roots.insert(Root::Local(local.0));
            }
            Source::Value(value) => {
                provenance.roots.insert(Root::Value(value.0));
            }
            Source::Function(_) => {
                provenance.roots.insert(Root::External);
            }
        }
        provenance
    }
}

fn merge_info(infos: &mut HashMap<LoanKey, LoanInfo>, key: LoanKey, info: LoanInfo) -> bool {
    if let Some(existing) = infos.get_mut(&key) {
        let roots_changed = existing.roots.len() != existing.roots.union(&info.roots).count();
        let parents_changed =
            existing.parents.len() != existing.parents.union(&info.parents).count();
        existing.roots.extend(info.roots);
        existing.parents.extend(info.parents);
        roots_changed || parents_changed
    } else {
        infos.insert(key, info);
        true
    }
}

fn transfer_provenance(
    function: &Function,
    instruction: &Instruction,
    state: &mut [Provenance],
    infos: &mut HashMap<LoanKey, LoanInfo>,
) -> bool {
    let Some(output) = instruction.output else {
        if let InstructionKind::Assign { target, value, .. } = &instruction.kind {
            let target_index = target.0 as usize;
            let new = if is_reference(&function.locals[target_index].ty) {
                operand_provenance(function, state, value)
            } else {
                Provenance::default()
            };
            let changed = state[target_index] != new;
            state[target_index] = new;
            return changed;
        }
        return false;
    };
    let output_index = function.locals.len() + output.0 as usize;
    let new = match &instruction.kind {
        InstructionKind::Borrow {
            loan,
            owner,
            access,
        }
        | InstructionKind::ElementAddr {
            loan,
            base: owner,
            access,
            ..
        } => {
            let owner_provenance = roots_for_owner(function, state, owner);
            let key = LoanKey::Site(loan.0);
            let info = LoanInfo {
                roots: owner_provenance.roots.clone(),
                parents: owner_provenance.loans.clone(),
                access: *access,
            };
            let info_changed = merge_info(infos, key, info);
            let mut new = owner_provenance;
            new.loans.insert(key);
            if let Some(slot) = state.get_mut(output_index) {
                let state_changed = *slot != new;
                *slot = new;
                return state_changed || info_changed;
            }
            return info_changed;
        }
        InstructionKind::Capture(operand) if is_reference(&function.values[output.0 as usize]) => {
            operand_provenance(function, state, operand)
        }
        InstructionKind::Load { reference }
            if is_reference(&function.values[output.0 as usize]) =>
        {
            operand_provenance(function, state, reference)
        }
        InstructionKind::Call { .. } if is_reference(&function.values[output.0 as usize]) => {
            Provenance {
                roots: BTreeSet::from([Root::External]),
                loans: BTreeSet::new(),
            }
        }
        _ => Provenance::default(),
    };
    let changed = state.get(output_index).is_some_and(|old| old != &new);
    if let Some(slot) = state.get_mut(output_index) {
        *slot = new;
    }
    changed
}

fn provenance(
    function: &Function,
    reachable: &[bool],
) -> (Vec<Vec<Provenance>>, HashMap<LoanKey, LoanInfo>) {
    let slots = slot_count(function);
    let mut inputs = vec![vec![Provenance::default(); slots]; function.blocks.len()];
    let mut infos = HashMap::new();
    for (local, parameter) in function
        .parameter_locals
        .iter()
        .zip(&function.signature.parameters)
    {
        if parameter.access != Access::Owned {
            let key = LoanKey::Parameter(local.0);
            let info = LoanInfo {
                roots: BTreeSet::from([Root::Parameter(local.0)]),
                parents: BTreeSet::new(),
                access: parameter.access,
            };
            merge_info(&mut infos, key, info);
            inputs[function.entry.0 as usize][local.0 as usize] = Provenance {
                roots: BTreeSet::from([Root::Parameter(local.0)]),
                loans: BTreeSet::from([key]),
            };
        }
    }

    loop {
        let previous_inputs = inputs.clone();
        let previous_infos = infos.clone();
        for (block_index, block) in function.blocks.iter().enumerate() {
            if !reachable[block_index] {
                continue;
            }
            let mut state = inputs[block_index].clone();
            for instruction in &block.instructions {
                transfer_provenance(function, instruction, &mut state, &mut infos);
            }
            for edge in edges(&block.terminator.kind) {
                let Some(target) = function.blocks.get(edge.target.0 as usize) else {
                    continue;
                };
                let mut edge_state = state.clone();
                for (argument, parameter) in edge.arguments.iter().zip(&target.parameters) {
                    let index = function.locals.len() + parameter.0 as usize;
                    edge_state[index] = if is_reference(&function.values[parameter.0 as usize]) {
                        operand_provenance(function, &state, argument)
                    } else {
                        Provenance::default()
                    };
                }
                let target_state = &mut inputs[edge.target.0 as usize];
                for (target, incoming) in target_state.iter_mut().zip(edge_state) {
                    target.roots.extend(incoming.roots);
                    target.loans.extend(incoming.loans);
                }
            }
        }
        if inputs == previous_inputs && infos == previous_infos {
            break;
        }
    }
    (inputs, infos)
}

fn active_loans(
    function: &Function,
    state: &[Provenance],
    live: &[bool],
    infos: &HashMap<LoanKey, LoanInfo>,
) -> HashMap<LoanKey, LoanInfo> {
    let mut active = HashMap::new();
    let mut queue = VecDeque::new();
    for (index, provenance) in state.iter().enumerate() {
        let reference = if index < function.locals.len() {
            is_reference(&function.locals[index].ty)
        } else {
            function
                .values
                .get(index - function.locals.len())
                .is_some_and(is_reference)
        };
        if live.get(index).copied().unwrap_or(false) && reference {
            queue.extend(provenance.loans.iter().copied());
        }
    }
    while let Some(key) = queue.pop_front() {
        if active.contains_key(&key) {
            continue;
        }
        if let Some(info) = infos.get(&key) {
            active.insert(key, info.clone());
            queue.extend(info.parents.iter().copied());
        }
    }
    active
}

fn terminator_operands(terminator: &TerminatorKind) -> Vec<&Operand> {
    match terminator {
        TerminatorKind::Goto(edge) => edge.arguments.iter().collect(),
        TerminatorKind::Branch {
            condition,
            then_edge,
            else_edge,
        } => std::iter::once(condition)
            .chain(&then_edge.arguments)
            .chain(&else_edge.arguments)
            .collect(),
        TerminatorKind::Return(Some(value)) => vec![value],
        TerminatorKind::Return(None) | TerminatorKind::Unreachable => Vec::new(),
    }
}

fn check_terminator(
    function: &Function,
    block: &Block,
    state: &[Provenance],
    live: &[bool],
    infos: &HashMap<LoanKey, LoanInfo>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let active = active_loans(function, state, live, infos);
    for operand in terminator_operands(&block.terminator.kind) {
        if type_at(function, operand.source).is_some_and(is_reference) {
            check_transport(function, state, operand, &active, infos, diagnostics);
            continue;
        }
        let roots = roots_for_owner(function, state, operand);
        let access = if matches!(operand.mode, UseMode::Share | UseMode::Consume) {
            Access::Share
        } else {
            Access::Borrow
        };
        if let Some(conflict) = active_conflict(&roots.roots, access, &active, &BTreeSet::new()) {
            diagnostics.push(diagnostic(
                5,
                operand.span.or(block.terminator.span),
                format!("control-flow operand conflicts with active loan {conflict:?}"),
            ));
        }
    }
}

// A handle can be relocated, or explicitly reborrowed at a fresh loan site.
// Copying it would give two handles the same loan identity and bypass freezing.
fn check_transport(
    function: &Function,
    state: &[Provenance],
    operand: &Operand,
    active: &HashMap<LoanKey, LoanInfo>,
    infos: &HashMap<LoanKey, LoanInfo>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if operand.mode != UseMode::Consume {
        diagnostics.push(diagnostic(2, operand.span, "reference handle transport requires Consume; use an explicit Borrow instruction to reborrow"));
        return;
    }
    let provenance = operand_provenance(function, state, operand);
    let own = parent_closure(&provenance.loans, infos);
    let access = match type_at(function, operand.source) {
        Some(Type::Reference { access, .. }) => *access,
        _ => Access::Share,
    };
    if let Some(conflict) = active_conflict(&provenance.roots, access, active, &own) {
        diagnostics.push(diagnostic(
            5,
            operand.span,
            format!("reference handle relocation conflicts with active loan {conflict:?}"),
        ));
    }
}

fn roots_overlap(left: &BTreeSet<Root>, right: &BTreeSet<Root>) -> bool {
    left.contains(&Root::External) && right.contains(&Root::External)
        || left.iter().any(|root| right.contains(root))
}

fn loan_conflicts(new_access: Access, active_access: Access) -> bool {
    new_access == Access::Share || active_access == Access::Share
}

fn parent_closure(
    roots: &BTreeSet<LoanKey>,
    infos: &HashMap<LoanKey, LoanInfo>,
) -> BTreeSet<LoanKey> {
    let mut result = roots.clone();
    let mut queue = VecDeque::from_iter(roots.iter().copied());
    while let Some(key) = queue.pop_front() {
        if let Some(info) = infos.get(&key) {
            for parent in &info.parents {
                if result.insert(*parent) {
                    queue.push_back(*parent);
                }
            }
        }
    }
    result
}

fn immutable_root(function: &Function, roots: &BTreeSet<Root>) -> bool {
    roots.iter().any(|root| match root {
        Root::Local(local) => function
            .locals
            .get(*local as usize)
            .is_some_and(|local| !local.mutable),
        Root::Value(_) => true,
        Root::Parameter(_) | Root::External => false,
    })
}

fn active_conflict(
    roots: &BTreeSet<Root>,
    access: Access,
    active: &HashMap<LoanKey, LoanInfo>,
    exempt: &BTreeSet<LoanKey>,
) -> Option<LoanKey> {
    active.iter().find_map(|(key, info)| {
        (!exempt.contains(key)
            && roots_overlap(roots, &info.roots)
            && loan_conflicts(access, info.access))
        .then_some(*key)
    })
}

fn source_provenance(function: &Function, state: &[Provenance], operand: &Operand) -> Provenance {
    if type_at(function, operand.source).is_some_and(is_reference) {
        operand_provenance(function, state, operand)
    } else {
        roots_for_owner(function, state, operand)
    }
}

#[allow(clippy::too_many_arguments)]
fn check_instruction(
    program: &Program,
    function: &Function,
    instruction: &Instruction,
    state: &[Provenance],
    active_before: &HashMap<LoanKey, LoanInfo>,
    active_after: &HashMap<LoanKey, LoanInfo>,
    infos: &HashMap<LoanKey, LoanInfo>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match &instruction.kind {
        InstructionKind::Capture(operand) | InstructionKind::Assign { value: operand, .. }
            if type_at(function, operand.source).is_some_and(is_reference) =>
        {
            check_transport(function, state, operand, active_before, infos, diagnostics);
        }
        _ => {}
    }
    match &instruction.kind {
        InstructionKind::Borrow {
            loan,
            owner,
            access,
        }
        | InstructionKind::ElementAddr {
            loan,
            base: owner,
            access,
            ..
        } => {
            if *access == Access::Share {
                if let Source::Local(local) = owner.source {
                    if is_reference(&function.locals[local.0 as usize].ty)
                        && !function.locals[local.0 as usize].mutable
                        && !function.parameter_locals.contains(&local)
                    {
                        diagnostics.push(diagnostic(4, instruction.span, "cannot reborrow Share access through an immutable reference handle local"));
                    }
                }
            }
            let provenance = source_provenance(function, state, owner);
            let ancestors = parent_closure(&provenance.loans, infos);
            if *access == Access::Share && immutable_root(function, &provenance.roots) {
                diagnostics.push(diagnostic(
                    5,
                    instruction.span,
                    "cannot create Share access to an immutable owner",
                ));
            }
            let repeated_site =
                *access == Access::Share && active_before.contains_key(&LoanKey::Site(loan.0));
            if repeated_site {
                diagnostics.push(diagnostic(
                    5,
                    instruction.span,
                    "Share loan site is re-entered while an earlier instance remains live",
                ));
            }
            if let Some(conflict) =
                active_conflict(&provenance.roots, *access, active_before, &ancestors)
            {
                if !repeated_site {
                    diagnostics.push(diagnostic(
                        5,
                        instruction.span,
                        format!("loan conflicts with active loan {conflict:?}"),
                    ));
                }
            }
        }
        InstructionKind::Load { reference } => {
            let provenance = operand_provenance(function, state, reference);
            let own = parent_closure(&provenance.loans, infos);
            if let Some(conflict) =
                active_conflict(&provenance.roots, Access::Borrow, active_before, &own)
            {
                diagnostics.push(diagnostic(
                    5,
                    instruction.span,
                    format!("reference load conflicts with active loan {conflict:?}"),
                ));
            }
        }
        InstructionKind::Store { reference, .. } => {
            if let Source::Local(local) = reference.source {
                if !function.locals[local.0 as usize].mutable
                    && !function.parameter_locals.contains(&local)
                {
                    diagnostics.push(diagnostic(
                        4,
                        instruction.span,
                        "cannot write through an immutable reference handle local",
                    ));
                }
            }
            let provenance = operand_provenance(function, state, reference);
            if immutable_root(function, &provenance.roots) {
                diagnostics.push(diagnostic(
                    5,
                    instruction.span,
                    "cannot write through Share access to an immutable owner",
                ));
            }
            let own = parent_closure(&provenance.loans, infos);
            if let Some(conflict) =
                active_conflict(&provenance.roots, Access::Share, active_before, &own)
            {
                diagnostics.push(diagnostic(
                    5,
                    instruction.span,
                    format!("Share store conflicts with active loan {conflict:?}"),
                ));
            }
        }
        InstructionKind::Assign { target, .. } => {
            let roots = BTreeSet::from([Root::Local(target.0)]);
            if let Some(conflict) =
                active_conflict(&roots, Access::Share, active_after, &BTreeSet::new())
            {
                diagnostics.push(diagnostic(
                    5,
                    instruction.span,
                    format!("assignment conflicts with active loan {conflict:?}"),
                ));
            }
        }
        _ => {}
    }

    // Borrow creation and reference dereferences have their own access rules.
    // Every other owner operand still reads (or consumes) the owner directly.
    for operand in instruction_operands(&instruction.kind) {
        let is_borrow_owner = match &instruction.kind {
            InstructionKind::Borrow { owner, .. } => std::ptr::eq(owner, operand),
            InstructionKind::ElementAddr { base, .. } => std::ptr::eq(base, operand),
            _ => false,
        };
        if is_borrow_owner || type_at(function, operand.source).is_some_and(is_reference) {
            continue;
        }
        let provenance = roots_for_owner(function, state, operand);
        let access = if matches!(operand.mode, UseMode::Consume | UseMode::Share) {
            Access::Share
        } else {
            Access::Borrow
        };
        if let Some(conflict) =
            active_conflict(&provenance.roots, access, active_before, &BTreeSet::new())
        {
            diagnostics.push(diagnostic(
                5,
                operand.span.or(instruction.span),
                format!("owner access conflicts with active loan {conflict:?}"),
            ));
        }
    }

    if let InstructionKind::Call { callee, arguments } = &instruction.kind {
        check_call(
            program,
            function,
            callee,
            arguments,
            state,
            active_before,
            instruction,
            diagnostics,
        );
    }
}

fn function_signature(
    program: &Program,
    function: &Function,
    callee: &Operand,
) -> Option<memobits_ir::Signature> {
    match callee.source {
        Source::Function(id) => program
            .functions
            .get(id.0 as usize)
            .map(|f| f.signature.clone()),
        Source::Local(_) | Source::Value(_) => match type_at(function, callee.source) {
            Some(Type::Function(signature)) => Some(signature.clone()),
            _ => None,
        },
    }
}

#[allow(clippy::too_many_arguments)]
fn check_call(
    program: &Program,
    function: &Function,
    callee: &Operand,
    arguments: &[Operand],
    state: &[Provenance],
    active: &HashMap<LoanKey, LoanInfo>,
    instruction: &Instruction,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(signature) = function_signature(program, function, callee) else {
        return;
    };
    let mut call_loans = Vec::new();
    for (argument, parameter) in arguments.iter().zip(&signature.parameters) {
        if parameter.access == Access::Owned {
            continue;
        }
        if parameter.access == Access::Share {
            if let Source::Local(local) = argument.source {
                if is_reference(&function.locals[local.0 as usize].ty)
                    && !function.locals[local.0 as usize].mutable
                    && !function.parameter_locals.contains(&local)
                {
                    diagnostics.push(diagnostic(
                        4,
                        argument.span.or(instruction.span),
                        "cannot pass Share access through an immutable reference handle local",
                    ));
                }
            }
        }
        let provenance = source_provenance(function, state, argument);
        if parameter.access == Access::Share && immutable_root(function, &provenance.roots) {
            diagnostics.push(diagnostic(
                5,
                argument.span.or(instruction.span),
                "cannot pass an immutable owner with Share access",
            ));
        }
        call_loans.push((argument, parameter.access, provenance));
    }

    for index in 0..call_loans.len() {
        let (argument, access, provenance) = &call_loans[index];
        let own = parent_closure(&provenance.loans, active);
        if let Some(conflict) = active_conflict(&provenance.roots, *access, active, &own) {
            diagnostics.push(diagnostic(
                5,
                argument.span.or(instruction.span),
                format!("call argument conflicts with active loan {conflict:?}"),
            ));
        }
        for (other_argument, other_access, other_provenance) in call_loans.iter().skip(index + 1) {
            if roots_overlap(&provenance.roots, &other_provenance.roots)
                && loan_conflicts(*access, *other_access)
            {
                diagnostics.push(diagnostic(
                    5,
                    other_argument.span.or(instruction.span),
                    "call arguments create conflicting loans to the same owner",
                ));
            }
        }
    }
}
