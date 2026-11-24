//! Experimental loan liveness over validated reference IR.
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Label, Severity, Span};
use memobits_ir::{
    Access, ArrayInit, Block, Constant, Edge, Function, Instruction, InstructionKind, LoanId,
    LocalId, Operand, Program, Source, TerminatorKind, Type, TypeDefKind, UseMode, ValueId,
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

/// One projection step below a root: a struct field, a payload field of an
/// enum variant, an array element with a known constant index, or an array
/// element with an unknown index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Step {
    Field(u32),
    /// Payload field `.1` of variant `.0`.
    Variant(u32, u32),
    Const(u128),
    Dynamic,
}

/// A memory location: a root and the projection path from it. A path that is a
/// prefix of another names an enclosing location, which overlaps it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Place {
    root: Root,
    path: Vec<Step>,
}

impl Place {
    fn whole(root: Root) -> Self {
        Self {
            root,
            path: Vec::new(),
        }
    }
}

/// Conservative step overlap: only provably different steps are disjoint.
/// Distinct fields never overlap, distinct constant indices never overlap, and
/// a dynamic index may equal any index. Payload fields of one variant are
/// distinct storage, but different variants of an enum share the same storage,
/// so they overlap.
fn steps_may_overlap(left: Step, right: Step) -> bool {
    match (left, right) {
        (Step::Field(a), Step::Field(b)) => a == b,
        (Step::Variant(va, fa), Step::Variant(vb, fb)) => va != vb || fa == fb,
        (Step::Const(a), Step::Const(b)) => a == b,
        _ => true,
    }
}

fn places_may_overlap(left: &Place, right: &Place) -> bool {
    if left.root == Root::External && right.root == Root::External {
        return true;
    }
    left.root == right.root
        && left
            .path
            .iter()
            .zip(&right.path)
            .all(|(a, b)| steps_may_overlap(*a, *b))
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Provenance {
    roots: BTreeSet<Place>,
    /// Every loan this reference derives from, including its own.
    loans: BTreeSet<LoanKey>,
    /// The loans created for this reference itself. A loan that is only an
    /// ancestor of a live reference is an intermediate path step: it stays
    /// reachable for transport checks but does not conflict on its own, since
    /// the live descendants cover exactly the memory still reachable.
    own: BTreeSet<LoanKey>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LoanInfo {
    roots: BTreeSet<Place>,
    parents: BTreeSet<LoanKey>,
    access: Access,
    /// Only set on entries of the active set: a live reference holds this loan
    /// itself rather than through a descendant.
    direct: bool,
    /// Where the loan began: the borrowing instruction, or a parameter's
    /// declaration. Used only to explain conflicts.
    origin: Option<Span>,
}

#[derive(Clone)]
struct Liveness {
    before: Vec<Vec<Vec<bool>>>,
    after: Vec<Vec<Vec<bool>>>,
    terminator: Vec<Vec<bool>>,
}

/// A conflict between a new access and a live loan, with enough information to
/// explain both sides in source terms.
#[derive(Clone, Debug)]
struct Conflict {
    key: LoanKey,
    /// The overlapping location the loan covers.
    loan_place: Place,
    /// The overlapping location being accessed.
    access_place: Place,
    loan_access: Access,
    origin: Option<Span>,
}

/// A diagnostic whose secondary labels are attached once the position in the
/// function is known.
struct Pending {
    diagnostic: Diagnostic,
    conflict: Option<Conflict>,
    /// Wins over a plain report with the same code and location.
    preferred: bool,
}

fn diagnostic(number: u16, span: Option<Span>, message: impl Into<String>) -> Pending {
    let mut diagnostic = Diagnostic::new(
        DiagnosticCode::new(Category::Borrow, number).expect("static BE code"),
        Severity::Error,
        message,
    );
    diagnostic.span = span;
    Pending {
        diagnostic,
        conflict: None,
        preferred: false,
    }
}

fn conflict_diagnostic(
    span: Option<Span>,
    action: &str,
    names: (&Function, &Program),
    conflict: Conflict,
) -> Pending {
    let name = place_name(names.0, names.1, &conflict.access_place);
    let mut pending = diagnostic(
        5,
        span,
        format!(
            "cannot {action} {name} while it is {}",
            loan_state(conflict.loan_access)
        ),
    );
    pending.conflict = Some(conflict);
    pending
}

/// What the user is doing at an address instruction: a field or element place
/// that is only written or read reads better as "write"/"read" than as a
/// "share"/"borrow" of the place.
fn address_action(function: &Function, output: Option<ValueId>, access: Access) -> &'static str {
    let Some(output) = output else {
        return access_verb(access);
    };
    let (mut stores, mut loads) = (false, false);
    for instruction in function.blocks.iter().flat_map(|block| &block.instructions) {
        match &instruction.kind {
            InstructionKind::Store { reference, .. }
                if reference.source == Source::Value(output) =>
            {
                stores = true;
            }
            InstructionKind::Load { reference } if reference.source == Source::Value(output) => {
                loads = true;
            }
            _ => {}
        }
    }
    if stores {
        "write"
    } else if loads && access == Access::Borrow {
        "read"
    } else {
        access_verb(access)
    }
}

/// Whether the address value is one operand of a user `swap` of two places:
/// both operands are projected addresses (an overwrite or `replace` pairs one
/// address with a hidden local).
fn feeds_swap(function: &Function, output: Option<ValueId>) -> bool {
    let Some(output) = output else {
        return false;
    };
    let instructions = || function.blocks.iter().flat_map(|block| &block.instructions);
    let is_address = |operand: &Operand| match operand.source {
        Source::Value(value) => instructions().any(|instruction| {
            instruction.output == Some(value)
                && matches!(
                    instruction.kind,
                    InstructionKind::ElementAddr { .. } | InstructionKind::FieldAddr { .. }
                )
        }),
        _ => false,
    };
    instructions().any(|instruction| match &instruction.kind {
        InstructionKind::SwapPlaces { left, right } => {
            (left.source == Source::Value(output) || right.source == Source::Value(output))
                && is_address(left)
                && is_address(right)
        }
        _ => false,
    })
}

fn loan_state(access: Access) -> &'static str {
    if access == Access::Share {
        "shared"
    } else {
        "borrowed"
    }
}

fn access_verb(access: Access) -> &'static str {
    if access == Access::Share {
        "share"
    } else {
        "borrow"
    }
}

/// Render a place as `` `root.field[0]` `` using source names, or "this value"
/// when the root is a compiler temporary or the path cannot be followed.
fn place_name(function: &Function, program: &Program, place: &Place) -> String {
    let local = match place.root {
        Root::Local(index) | Root::Parameter(index) => function.locals.get(index as usize),
        Root::Value(_) | Root::External => None,
    };
    let Some(local) = local.filter(|local| {
        !local.name.is_empty() && local.name.chars().all(|c| c.is_alphanumeric() || c == '_')
    }) else {
        return "this value".to_owned();
    };
    let mut text = local.name.clone();
    let mut ty = &local.ty;
    for step in &place.path {
        while let Type::Reference { inner, .. } = ty {
            ty = inner;
        }
        match (step, ty) {
            (Step::Field(field), Type::Struct(id)) => {
                let Some(TypeDefKind::Struct { fields }) =
                    program.types.get(id.0 as usize).map(|def| &def.kind)
                else {
                    return "this value".to_owned();
                };
                let Some(field) = fields.get(*field as usize) else {
                    return "this value".to_owned();
                };
                text.push('.');
                text.push_str(&field.name);
                ty = &field.ty;
            }
            (Step::Variant(variant, field), Type::Enum(id)) => {
                let Some(TypeDefKind::Enum { variants }) =
                    program.types.get(id.0 as usize).map(|def| &def.kind)
                else {
                    return "this value".to_owned();
                };
                let Some(declared) = variants.get(*variant as usize) else {
                    return "this value".to_owned();
                };
                let Some(payload) = declared.payload.get(*field as usize) else {
                    return "this value".to_owned();
                };
                text.push_str(&format!("::{}.{field}", declared.name));
                ty = payload;
            }
            (Step::Const(index), Type::Array { element, .. }) => {
                text.push_str(&format!("[{index}]"));
                ty = element;
            }
            (Step::Dynamic, Type::Array { element, .. }) => {
                text.push_str("[_]");
                ty = element;
            }
            _ => return "this value".to_owned(),
        }
    }
    format!("`{text}`")
}

/// Per-function data needed to explain a conflict after the fact.
struct Explain<'a> {
    function: &'a Function,
    program: &'a Program,
    inputs: &'a [Vec<Provenance>],
    consts: &'a [Option<u128>],
    reachable: &'a [bool],
}

impl Explain<'_> {
    /// Add the "loan began here" and "loan is used later" labels.
    fn attach(&self, pending: &mut [Pending], block: usize, position: usize) {
        for pending in pending {
            let Some(conflict) = pending.conflict.take() else {
                continue;
            };
            let loan = place_name(self.function, self.program, &conflict.loan_place);
            let kind = loan_state(conflict.loan_access);
            let verb = access_verb(conflict.loan_access);
            if let Some(origin) = conflict.origin {
                let message = match conflict.key {
                    LoanKey::Site(_) => format!("{loan} was {kind} here"),
                    LoanKey::Parameter(_) => {
                        format!("{loan} is a {verb} parameter, declared here")
                    }
                };
                pending.diagnostic.labels.push(Label {
                    span: origin,
                    message,
                });
            }
            if let Some(span) = self.later_use(block, position, conflict.key) {
                if Some(span) != pending.diagnostic.span {
                    pending.diagnostic.labels.push(Label {
                        span,
                        message: format!("the {verb} is used later here, which keeps it alive"),
                    });
                }
            }
        }
    }

    /// The first use, after instruction `position` of `block`, of a reference
    /// derived from `key`. Positions past the last instruction mean the
    /// terminator was being checked.
    fn later_use(&self, block: usize, position: usize, key: LoanKey) -> Option<Span> {
        let mut infos = HashMap::new();
        let mut state = self.inputs[block].clone();
        let instructions = &self.function.blocks[block].instructions;
        for instruction in instructions.iter().take(position + 1) {
            transfer_provenance(
                self.function,
                instruction,
                &mut state,
                &mut infos,
                self.consts,
            );
        }
        let mut seen = vec![false; self.function.blocks.len()];
        let mut queue = VecDeque::new();
        let mut current = (block, position + 1, state);
        loop {
            let (index, start, mut state) = current;
            let target = &self.function.blocks[index];
            for instruction in target.instructions.iter().skip(start) {
                for operand in instruction_operands(&instruction.kind) {
                    if self.holds(&state, operand, key) {
                        return operand.span.or(instruction.span);
                    }
                }
                transfer_provenance(
                    self.function,
                    instruction,
                    &mut state,
                    &mut infos,
                    self.consts,
                );
            }
            for operand in terminator_operands(&target.terminator.kind) {
                if self.holds(&state, operand, key) {
                    return operand.span.or(target.terminator.span);
                }
            }
            for edge in edges(&target.terminator.kind) {
                let next = edge.target.0 as usize;
                if !seen[next] && self.reachable.get(next).copied().unwrap_or(false) {
                    seen[next] = true;
                    queue.push_back(next);
                }
            }
            let next = queue.pop_front()?;
            current = (next, 0, self.inputs[next].clone());
        }
    }

    fn holds(&self, state: &[Provenance], operand: &Operand, key: LoanKey) -> bool {
        operand_provenance(self.function, state, operand)
            .loans
            .contains(&key)
    }
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
            diagnostics.push(
                diagnostic(
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
                )
                .diagnostic,
            );
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
    let consts = constants(function);
    let intermediates = intermediate_addresses(function);
    let (inputs, infos) = provenance(function, &reachable);
    let explain = Explain {
        function,
        program,
        inputs: &inputs,
        consts: &consts,
        reachable: &reachable,
    };
    let mut diagnostics: Vec<Pending> = Vec::new();

    for (block_index, block) in function.blocks.iter().enumerate() {
        if !reachable[block_index] {
            continue;
        }
        let mut state = inputs[block_index].clone();
        for (instruction_index, instruction) in block.instructions.iter().enumerate() {
            let before = active_loans(
                &state,
                &liveness.before[block_index][instruction_index],
                &infos,
            );
            let mut after_state = state.clone();
            transfer_provenance(
                function,
                instruction,
                &mut after_state,
                &mut infos.clone(),
                &consts,
            );
            let after = active_loans(
                &after_state,
                &liveness.after[block_index][instruction_index],
                &infos,
            );
            let first = diagnostics.len();
            check_instruction(
                program,
                function,
                instruction,
                &state,
                &before,
                &after,
                &infos,
                &consts,
                &intermediates,
                &mut diagnostics,
            );
            explain.attach(&mut diagnostics[first..], block_index, instruction_index);
            transfer_provenance(
                function,
                instruction,
                &mut state,
                &mut infos.clone(),
                &consts,
            );
        }
        let first = diagnostics.len();
        check_terminator(
            program,
            function,
            block,
            &state,
            &liveness.terminator[block_index],
            &infos,
            &mut diagnostics,
        );
        explain.attach(
            &mut diagnostics[first..],
            block_index,
            block.instructions.len(),
        );
    }
    // One conflict can be reached through several operands or loan paths;
    // report each primary location once.
    let mut winner: HashMap<(u16, Option<Span>), usize> = HashMap::new();
    for (index, pending) in diagnostics.iter().enumerate() {
        let key = (pending.diagnostic.code.number(), pending.diagnostic.span);
        match winner.get(&key) {
            Some(&old) if diagnostics[old].preferred || !pending.preferred => {}
            _ => {
                winner.insert(key, index);
            }
        }
    }
    diagnostics
        .into_iter()
        .enumerate()
        .filter(|(index, pending)| {
            winner[&(pending.diagnostic.code.number(), pending.diagnostic.span)] == *index
        })
        .map(|(_, pending)| pending.diagnostic)
        .collect()
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
        TerminatorKind::Switch {
            targets, default, ..
        } => targets
            .iter()
            .map(|(_, edge)| edge)
            .chain(default.iter())
            .collect(),
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
    mark_source(live, function, operand.source);
}

fn mark_source(live: &mut [bool], function: &Function, source: Source) {
    if let Some(index) = slot(source, function) {
        if let Some(mark) = live.get_mut(index) {
            *mark = true;
        }
    }
}

fn mark_instruction_uses(live: &mut [bool], function: &Function, kind: &InstructionKind) {
    for operand in instruction_operands(kind) {
        mark_operand(live, function, operand);
    }
    // List mutations address the receiver directly by local slot.
    if let InstructionKind::ListPush { target, .. }
    | InstructionKind::ListPop { target }
    | InstructionKind::ListClear { target } = kind
    {
        mark_source(live, function, Source::Local(*target));
    }
}

fn instruction_operands(kind: &InstructionKind) -> Vec<&Operand> {
    match kind {
        InstructionKind::EmptyList
        | InstructionKind::Constant(_)
        | InstructionKind::EndStructLocal { .. }
        | InstructionKind::EndStringLocal { .. }
        | InstructionKind::EndListLocal { .. }
        | InstructionKind::ListPop { .. }
        | InstructionKind::ListClear { .. } => Vec::new(),
        InstructionKind::ListPush { value, .. } => vec![value],
        InstructionKind::Capture(operand)
        | InstructionKind::DropLocal { value: operand }
        | InstructionKind::Assert { condition: operand }
        | InstructionKind::Copy { source: operand }
        | InstructionKind::ListLen { source: operand }
        | InstructionKind::StringLen { source: operand }
        | InstructionKind::Unary { operand, .. }
        | InstructionKind::Cast { value: operand, .. }
        | InstructionKind::Borrow { owner: operand, .. }
        | InstructionKind::Load { reference: operand } => vec![operand],
        InstructionKind::ListGet {
            source,
            index: offset,
        }
        | InstructionKind::ListRead {
            source,
            index: offset,
        }
        | InstructionKind::CollectionSearch {
            source,
            value: offset,
            ..
        }
        | InstructionKind::ValidateUtf8 {
            source,
            length: offset,
            ..
        }
        | InstructionKind::StringIsCharBoundary { source, offset }
        | InstructionKind::StringByteAt { source, offset }
        | InstructionKind::StringScalarAt { source, offset }
        | InstructionKind::StringScalarRead { source, offset, .. } => vec![source, offset],
        InstructionKind::InitConcatString { strings, .. } => strings.iter().collect(),
        InstructionKind::Store { reference, value } => vec![reference, value],
        InstructionKind::SwapPlaces { left, right } => vec![left, right],
        InstructionKind::ReplaceStringField { value, .. } => vec![value],
        InstructionKind::ElementAddr { base, index, .. } => vec![base, index],
        InstructionKind::FieldAddr { base, .. }
        | InstructionKind::VariantAddr { base, .. }
        | InstructionKind::Extract { base, .. }
        | InstructionKind::EnumTag { base }
        | InstructionKind::VariantExtract { base, .. } => vec![base],
        InstructionKind::StructNew { fields, .. } => fields.iter().collect(),
        InstructionKind::EnumNew { payload, .. } => payload.iter().collect(),
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
        TerminatorKind::Switch {
            tag,
            targets,
            default,
            ..
        } => {
            mark_operand(&mut live, function, tag);
            for edge in targets.iter().map(|(_, edge)| edge).chain(default) {
                for argument in &edge.arguments {
                    mark_operand(&mut live, function, argument);
                }
            }
        }
        TerminatorKind::Return(Some(value)) => mark_operand(&mut live, function, value),
        TerminatorKind::Return(None) | TerminatorKind::Unreachable => {}
    }
    for instruction in block.instructions.iter().rev() {
        kill_instruction_def(function, instruction, &mut live);
        mark_instruction_uses(&mut live, function, &instruction.kind);
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
            TerminatorKind::Switch {
                tag,
                targets,
                default,
                ..
            } => {
                mark_operand(&mut term_live, function, tag);
                mark_operand(&mut live, function, tag);
                for edge in targets.iter().map(|(_, edge)| edge).chain(default) {
                    for argument in &edge.arguments {
                        mark_operand(&mut term_live, function, argument);
                        mark_operand(&mut live, function, argument);
                    }
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
            mark_instruction_uses(&mut live, function, &instruction.kind);
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
            provenance.roots.insert(Place::whole(Root::External));
        }
        provenance
    } else {
        let mut provenance = Provenance::default();
        match operand.source {
            Source::Local(local) => {
                provenance.roots.insert(Place::whole(Root::Local(local.0)));
            }
            Source::Value(value) => {
                provenance.roots.insert(Place::whole(Root::Value(value.0)));
            }
            Source::Function(_) => {
                provenance.roots.insert(Place::whole(Root::External));
            }
        }
        provenance
    }
}

/// The locations an address instruction (`Borrow`, `FieldAddr`, `ElementAddr`)
/// may refer to: the owner's locations extended by the instruction's step.
/// External locations carry no path, because two unknown bases cannot be
/// compared field by field.
fn address_provenance(
    function: &Function,
    state: &[Provenance],
    instruction: &Instruction,
    consts: &[Option<u128>],
) -> Option<(Provenance, Access, LoanId)> {
    let (loan, owner, access, step) = match &instruction.kind {
        InstructionKind::Borrow {
            loan,
            owner,
            access,
        } => (loan, owner, access, None),
        InstructionKind::FieldAddr {
            loan,
            base,
            field,
            access,
        } => (loan, base, access, Some(Step::Field(*field))),
        InstructionKind::VariantAddr {
            loan,
            base,
            variant,
            field,
            access,
        } => (loan, base, access, Some(Step::Variant(*variant, *field))),
        InstructionKind::ElementAddr {
            loan,
            base,
            index,
            access,
        } => {
            let step = match index.source {
                Source::Value(value) => consts
                    .get(value.0 as usize)
                    .copied()
                    .flatten()
                    .map_or(Step::Dynamic, Step::Const),
                _ => Step::Dynamic,
            };
            (loan, base, access, Some(step))
        }
        _ => return None,
    };
    let mut provenance = roots_for_owner(function, state, owner);
    if let Some(step) = step {
        provenance.roots = provenance
            .roots
            .into_iter()
            .map(|mut place| {
                if place.root != Root::External {
                    place.path.push(step);
                }
                place
            })
            .collect();
    }
    Some((provenance, *access, *loan))
}

/// Address values that exist only to be projected further (`g.rows` in
/// `g.rows[0]`): used exactly once, as the base of another address instruction.
/// Their creation is path computation, not an access of their own place; the
/// final address instruction of the chain carries the access and is checked.
fn intermediate_addresses(function: &Function) -> HashSet<u32> {
    let mut uses = vec![0u32; function.values.len()];
    let mut as_base = vec![0u32; function.values.len()];
    let mut count = |operand: &Operand, base: bool| {
        if let Source::Value(value) = operand.source {
            if let Some(slot) = uses.get_mut(value.0 as usize) {
                *slot += 1;
            }
            if base {
                if let Some(slot) = as_base.get_mut(value.0 as usize) {
                    *slot += 1;
                }
            }
        }
    };
    for block in &function.blocks {
        for instruction in &block.instructions {
            let base = match &instruction.kind {
                InstructionKind::FieldAddr { base, .. }
                | InstructionKind::VariantAddr { base, .. }
                | InstructionKind::ElementAddr { base, .. } => Some(base),
                _ => None,
            };
            for operand in instruction_operands(&instruction.kind) {
                count(
                    operand,
                    base.is_some_and(|base| std::ptr::eq(base, operand)),
                );
            }
        }
        for operand in terminator_operands(&block.terminator.kind) {
            count(operand, false);
        }
    }
    function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| {
            matches!(
                instruction.kind,
                InstructionKind::FieldAddr { .. }
                    | InstructionKind::VariantAddr { .. }
                    | InstructionKind::ElementAddr { .. }
                    | InstructionKind::Borrow { .. }
            )
        })
        .filter_map(|instruction| instruction.output)
        .filter(|output| uses[output.0 as usize] == 1 && as_base[output.0 as usize] == 1)
        .map(|output| output.0)
        .collect()
}

/// Integer constants by value id, so constant indices can be told apart.
fn constants(function: &Function) -> Vec<Option<u128>> {
    let mut result = vec![None; function.values.len()];
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let (InstructionKind::Constant(Constant::Integer(text)), Some(output)) =
                (&instruction.kind, instruction.output)
            {
                let text = text.replace('_', "");
                let parsed = match text.strip_prefix("0x") {
                    Some(hex) => u128::from_str_radix(hex, 16).ok(),
                    None => text.parse::<u128>().ok(),
                };
                if let Some(slot) = result.get_mut(output.0 as usize) {
                    *slot = parsed;
                }
            }
        }
    }
    result
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
    consts: &[Option<u128>],
) -> bool {
    let Some(output) = instruction.output else {
        if let InstructionKind::Assign { target, value, .. } = &instruction.kind {
            let target_index = target.0 as usize;
            let new = operand_provenance(function, state, value);
            let changed = state[target_index] != new;
            state[target_index] = new;
            return changed;
        }
        return false;
    };
    let output_index = function.locals.len() + output.0 as usize;
    let new = match &instruction.kind {
        InstructionKind::Borrow { .. }
        | InstructionKind::ElementAddr { .. }
        | InstructionKind::FieldAddr { .. }
        | InstructionKind::VariantAddr { .. } => {
            let (owner_provenance, access, loan) =
                address_provenance(function, state, instruction, consts)
                    .expect("address instruction");
            let key = LoanKey::Site(loan.0);
            let info = LoanInfo {
                roots: owner_provenance.roots.clone(),
                parents: owner_provenance.loans.clone(),
                access,
                direct: false,
                origin: instruction.span,
            };
            let info_changed = merge_info(infos, key, info);
            let mut new = owner_provenance;
            new.loans.insert(key);
            new.own = BTreeSet::from([key]);
            if let Some(slot) = state.get_mut(output_index) {
                let state_changed = *slot != new;
                *slot = new;
                return state_changed || info_changed;
            }
            return info_changed;
        }
        InstructionKind::Capture(operand) => operand_provenance(function, state, operand),
        // A local borrow Option is the only validated enum with a reference
        // payload. Its Some variant transports one handle; None carries none.
        InstructionKind::EnumNew { payload, .. } => payload
            .first()
            .filter(|operand| type_at(function, operand.source).is_some_and(is_reference))
            .map_or_else(Provenance::default, |operand| {
                operand_provenance(function, state, operand)
            }),
        InstructionKind::VariantExtract { base, .. }
            if is_reference(&function.values[output.0 as usize]) =>
        {
            operand_provenance(function, state, base)
        }
        InstructionKind::Load { reference }
            if is_reference(&function.values[output.0 as usize]) =>
        {
            operand_provenance(function, state, reference)
        }
        InstructionKind::Call { .. } if is_reference(&function.values[output.0 as usize]) => {
            Provenance {
                roots: BTreeSet::from([Place::whole(Root::External)]),
                loans: BTreeSet::new(),
                own: BTreeSet::new(),
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
    let consts = constants(function);
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
                roots: BTreeSet::from([Place::whole(Root::Parameter(local.0))]),
                parents: BTreeSet::new(),
                access: parameter.access,
                direct: false,
                origin: Some(function.locals[local.0 as usize].span),
            };
            merge_info(&mut infos, key, info);
            inputs[function.entry.0 as usize][local.0 as usize] = Provenance {
                roots: BTreeSet::from([Place::whole(Root::Parameter(local.0))]),
                loans: BTreeSet::from([key]),
                own: BTreeSet::from([key]),
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
                transfer_provenance(function, instruction, &mut state, &mut infos, &consts);
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
                    target.own.extend(incoming.own);
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
    state: &[Provenance],
    live: &[bool],
    infos: &HashMap<LoanKey, LoanInfo>,
) -> HashMap<LoanKey, LoanInfo> {
    let mut active = HashMap::new();
    let mut queue = VecDeque::new();
    let mut direct = BTreeSet::new();
    for (index, provenance) in state.iter().enumerate() {
        if live.get(index).copied().unwrap_or(false) {
            queue.extend(provenance.loans.iter().copied());
            direct.extend(provenance.own.iter().copied());
        }
    }
    while let Some(key) = queue.pop_front() {
        if active.contains_key(&key) {
            continue;
        }
        if let Some(info) = infos.get(&key) {
            queue.extend(info.parents.iter().copied());
            let mut info = info.clone();
            info.direct = direct.contains(&key);
            active.insert(key, info);
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
        TerminatorKind::Switch {
            tag,
            targets,
            default,
            ..
        } => std::iter::once(tag)
            .chain(
                targets
                    .iter()
                    .map(|(_, edge)| edge)
                    .chain(default)
                    .flat_map(|edge| &edge.arguments),
            )
            .collect(),
        TerminatorKind::Return(Some(value)) => vec![value],
        TerminatorKind::Return(None) | TerminatorKind::Unreachable => Vec::new(),
    }
}

fn check_terminator(
    program: &Program,
    function: &Function,
    block: &Block,
    state: &[Provenance],
    live: &[bool],
    infos: &HashMap<LoanKey, LoanInfo>,
    diagnostics: &mut Vec<Pending>,
) {
    let active = active_loans(state, live, infos);
    for operand in terminator_operands(&block.terminator.kind) {
        if type_at(function, operand.source).is_some_and(is_reference) {
            check_transport(
                program,
                function,
                state,
                operand,
                &active,
                infos,
                diagnostics,
            );
            continue;
        }
        let roots = roots_for_owner(function, state, operand);
        let access = if matches!(operand.mode, UseMode::Share | UseMode::Consume) {
            Access::Share
        } else {
            Access::Borrow
        };
        if let Some(conflict) = active_conflict(&roots.roots, access, &active, &BTreeSet::new()) {
            diagnostics.push(conflict_diagnostic(
                operand.span.or(block.terminator.span),
                "use",
                (function, program),
                conflict,
            ));
        }
    }
}

// A handle can be relocated, or explicitly reborrowed at a fresh loan site.
// Copying it would give two handles the same loan identity and bypass freezing.
fn check_transport(
    program: &Program,
    function: &Function,
    state: &[Provenance],
    operand: &Operand,
    active: &HashMap<LoanKey, LoanInfo>,
    infos: &HashMap<LoanKey, LoanInfo>,
    diagnostics: &mut Vec<Pending>,
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
        diagnostics.push(conflict_diagnostic(
            operand.span,
            "move a reference to",
            (function, program),
            conflict,
        ));
    }
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

fn immutable_root(function: &Function, roots: &BTreeSet<Place>) -> bool {
    roots.iter().any(|place| match &place.root {
        Root::Local(local) => function
            .locals
            .get(*local as usize)
            .is_some_and(|local| !local.mutable),
        Root::Value(_) => true,
        Root::Parameter(_) | Root::External => false,
    })
}

/// The first (by loan identity, so output is stable) live loan that conflicts
/// with `access` to `roots`, together with the overlapping places.
fn active_conflict(
    roots: &BTreeSet<Place>,
    access: Access,
    active: &HashMap<LoanKey, LoanInfo>,
    exempt: &BTreeSet<LoanKey>,
) -> Option<Conflict> {
    active
        .iter()
        .filter(|(key, info)| {
            info.direct && !exempt.contains(key) && loan_conflicts(access, info.access)
        })
        .filter_map(|(key, info)| {
            roots.iter().find_map(|a| {
                info.roots
                    .iter()
                    .find(|b| places_may_overlap(a, b))
                    .map(|b| Conflict {
                        key: *key,
                        loan_place: b.clone(),
                        access_place: a.clone(),
                        loan_access: info.access,
                        origin: info.origin,
                    })
            })
        })
        .min_by_key(|conflict| conflict.key)
}

/// A pair of overlapping places from two root sets, for call-argument conflicts.
fn first_overlap(left: &BTreeSet<Place>, right: &BTreeSet<Place>) -> Option<Place> {
    left.iter()
        .find(|a| right.iter().any(|b| places_may_overlap(a, b)))
        .cloned()
}

fn source_provenance(function: &Function, state: &[Provenance], operand: &Operand) -> Provenance {
    if type_at(function, operand.source).is_some_and(is_reference) {
        operand_provenance(function, state, operand)
    } else {
        roots_for_owner(function, state, operand)
    }
}

#[allow(clippy::too_many_arguments)]
fn check_reference_read(
    program: &Program,
    function: &Function,
    state: &[Provenance],
    reference: &Operand,
    span: Option<Span>,
    active_before: &HashMap<LoanKey, LoanInfo>,
    infos: &HashMap<LoanKey, LoanInfo>,
    diagnostics: &mut Vec<Pending>,
) {
    let provenance = operand_provenance(function, state, reference);
    let own = parent_closure(&provenance.loans, infos);
    if let Some(conflict) = active_conflict(&provenance.roots, Access::Borrow, active_before, &own)
    {
        diagnostics.push(conflict_diagnostic(
            span,
            "read",
            (function, program),
            conflict,
        ));
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
    consts: &[Option<u128>],
    intermediates: &HashSet<u32>,
    diagnostics: &mut Vec<Pending>,
) {
    let transported = match &instruction.kind {
        InstructionKind::Capture(operand) | InstructionKind::Assign { value: operand, .. } => {
            Some(operand)
        }
        InstructionKind::EnumNew { payload, .. } => payload.first(),
        _ => None,
    };
    if let Some(operand) =
        transported.filter(|op| type_at(function, op.source).is_some_and(is_reference))
    {
        check_transport(
            program,
            function,
            state,
            operand,
            active_before,
            infos,
            diagnostics,
        );
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
        }
        | InstructionKind::FieldAddr {
            loan,
            base: owner,
            access,
            ..
        }
        | InstructionKind::VariantAddr {
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
            let provenance = address_provenance(function, state, instruction, consts)
                .expect("address instruction")
                .0;
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
            let transient = instruction
                .output
                .is_some_and(|output| intermediates.contains(&output.0));
            if let Some(conflict) =
                active_conflict(&provenance.roots, *access, active_before, &ancestors)
            {
                if !repeated_site && !transient {
                    let mut pending = conflict_diagnostic(
                        instruction.span,
                        address_action(function, instruction.output, *access),
                        (function, program),
                        conflict,
                    );
                    if let (Some(span), true) =
                        (instruction.span, feeds_swap(function, instruction.output))
                    {
                        pending.diagnostic.labels.push(Label {
                            span,
                            message: "swap needs two disjoint places; dynamic indices into the same collection are not provably disjoint".into(),
                        });
                    }
                    diagnostics.push(pending);
                }
            }
        }
        InstructionKind::Load { reference }
        | InstructionKind::ListLen { source: reference }
        | InstructionKind::CollectionSearch {
            source: reference, ..
        }
        | InstructionKind::ListGet {
            source: reference, ..
        }
        | InstructionKind::ListRead {
            source: reference, ..
        }
        | InstructionKind::StringLen { source: reference }
        | InstructionKind::StringIsCharBoundary {
            source: reference, ..
        }
        | InstructionKind::StringByteAt {
            source: reference, ..
        }
        | InstructionKind::ValidateUtf8 {
            source: reference, ..
        }
        | InstructionKind::StringScalarAt {
            source: reference, ..
        }
        | InstructionKind::StringScalarRead {
            source: reference, ..
        } if type_at(function, reference.source).is_some_and(is_reference) => {
            check_reference_read(
                program,
                function,
                state,
                reference,
                instruction.span,
                active_before,
                infos,
                diagnostics,
            );
        }
        InstructionKind::InitConcatString { strings, .. } => {
            for reference in strings {
                check_reference_read(
                    program,
                    function,
                    state,
                    reference,
                    instruction.span,
                    active_before,
                    infos,
                    diagnostics,
                );
            }
        }
        InstructionKind::ReplaceStringField { target, field, .. } => {
            let local = &function.locals[target.0 as usize];
            let root = if matches!(
                local.ty,
                Type::Reference {
                    access: Access::Share,
                    ..
                }
            ) && function.parameter_locals.contains(target)
            {
                Root::Parameter(target.0)
            } else {
                Root::Local(target.0)
            };
            let roots = BTreeSet::from([Place {
                root,
                path: vec![Step::Field(*field)],
            }]);
            if let Some(conflict) =
                active_conflict(&roots, Access::Share, active_before, &BTreeSet::new())
            {
                diagnostics.push(conflict_diagnostic(
                    instruction.span,
                    "write",
                    (function, program),
                    conflict,
                ));
            }
        }
        InstructionKind::SwapPlaces { left, right } => {
            for reference in [left, right] {
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
                    diagnostics.push(conflict_diagnostic(
                        instruction.span,
                        "write",
                        (function, program),
                        conflict,
                    ));
                }
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
                diagnostics.push(conflict_diagnostic(
                    instruction.span,
                    "write",
                    (function, program),
                    conflict,
                ));
            }
        }
        InstructionKind::EndStructLocal { local }
        | InstructionKind::EndStringLocal { local }
        | InstructionKind::EndListLocal { local } => {
            let roots = BTreeSet::from([Place::whole(Root::Local(local.0))]);
            if let Some(conflict) =
                active_conflict(&roots, Access::Share, active_after, &BTreeSet::new())
            {
                diagnostics.push(conflict_diagnostic(
                    instruction.span,
                    "end the scope of",
                    (function, program),
                    conflict,
                ));
            }
        }
        InstructionKind::ListPush { target, .. }
        | InstructionKind::ListPop { target }
        | InstructionKind::ListClear { target } => {
            let receiver = Operand {
                source: Source::Local(*target),
                mode: UseMode::Share,
                span: instruction.span,
            };
            let provenance = source_provenance(function, state, &receiver);
            let own = parent_closure(&provenance.loans, infos);
            if let Some(conflict) =
                active_conflict(&provenance.roots, Access::Share, active_before, &own)
            {
                diagnostics.push(conflict_diagnostic(
                    instruction.span,
                    match instruction.kind {
                        InstructionKind::ListPop { .. } => "pop from",
                        InstructionKind::ListClear { .. } => "clear",
                        _ => "push to",
                    },
                    (function, program),
                    conflict,
                ));
            }
        }
        InstructionKind::Assign { target, .. } => {
            let roots = BTreeSet::from([Place::whole(Root::Local(target.0))]);
            if let Some(conflict) =
                active_conflict(&roots, Access::Share, active_after, &BTreeSet::new())
            {
                diagnostics.push(conflict_diagnostic(
                    instruction.span,
                    "assign to",
                    (function, program),
                    conflict,
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
            InstructionKind::ElementAddr { base, .. }
            | InstructionKind::FieldAddr { base, .. }
            | InstructionKind::VariantAddr { base, .. } => std::ptr::eq(base, operand),
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
            let action = match operand.mode {
                UseMode::Consume
                    if matches!(instruction.kind, InstructionKind::DropLocal { .. }) =>
                {
                    "drop"
                }
                UseMode::Consume => "move",
                UseMode::Share => "share",
                UseMode::Read | UseMode::Borrow => "read",
            };
            diagnostics.push(conflict_diagnostic(
                operand.span.or(instruction.span),
                action,
                (function, program),
                conflict,
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
    diagnostics: &mut Vec<Pending>,
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
        // Conflicts between the arguments themselves are reported pairwise below.
        let mut own = BTreeSet::new();
        for (_, _, other) in &call_loans {
            own.extend(parent_closure(&other.loans, active));
        }
        if let Some(conflict) = active_conflict(&provenance.roots, *access, active, &own) {
            diagnostics.push(conflict_diagnostic(
                argument.span.or(instruction.span),
                access_verb(*access),
                (function, program),
                conflict,
            ));
        }
        for (other_argument, other_access, other_provenance) in call_loans.iter().skip(index + 1) {
            if let Some(place) = first_overlap(&provenance.roots, &other_provenance.roots)
                .filter(|_| loan_conflicts(*access, *other_access))
            {
                let name = place_name(function, program, &place);
                let mut pending = diagnostic(
                    5,
                    other_argument.span.or(instruction.span),
                    format!(
                        "cannot {} {name} while another argument of this call already {}s it",
                        access_verb(*other_access),
                        access_verb(*access),
                    ),
                );
                if let Some(span) = argument.span.or(instruction.span) {
                    pending.diagnostic.labels.push(Label {
                        span,
                        message: format!("{name} is {} here first", loan_state(*access)),
                    });
                }
                pending.preferred = true;
                diagnostics.push(pending);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{steps_may_overlap, Step};

    #[test]
    fn variant_steps_overlap_across_variants_but_not_across_fields() {
        // Different variants share the payload storage.
        assert!(steps_may_overlap(Step::Variant(0, 0), Step::Variant(1, 0)));
        assert!(steps_may_overlap(Step::Variant(0, 1), Step::Variant(1, 0)));
        // One variant's payload fields are distinct storage.
        assert!(steps_may_overlap(Step::Variant(2, 1), Step::Variant(2, 1)));
        assert!(!steps_may_overlap(Step::Variant(2, 0), Step::Variant(2, 1)));
        // Fields, constants and variants never compare equal to each other.
        assert!(steps_may_overlap(Step::Variant(0, 0), Step::Field(0)));
        assert!(!steps_may_overlap(Step::Field(0), Step::Field(1)));
    }
}
