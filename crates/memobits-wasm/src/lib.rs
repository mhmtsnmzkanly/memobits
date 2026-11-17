//! Experimental WebAssembly backend for the validated primitive IR subset.
//!
//! The current output ABI maps `Bool`, 8-bit, and 16-bit values to `i32`,
//! `i32`/`u32` to Wasm `i32`, 64-bit integers to Wasm `i64`, and floats to
//! their Wasm float type. `Unit` has no exported result and is represented by
//! an internal zero-valued `i32` when an IR value is needed. These choices are
//! experimental and do not define a stable Memobits ABI.
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_ir::{
    ArrayInit, BinaryOp, BlockId, Constant, Function, FunctionId, Instruction, InstructionKind,
    LocalId, Operand, Primitive, Program, Source, TerminatorKind, Type, TypeDef, TypeDefKind,
    UnaryOp,
};
use std::collections::{BTreeMap, BTreeSet};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, ExportKind, ExportSection, Function as WasmFunction,
    FunctionSection, GlobalSection, GlobalType, Instruction as WasmInstruction, MemArg,
    MemorySection, MemoryType, Module, TypeSection, ValType,
};

fn diagnostic(message: impl Into<String>, span: Option<Span>) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(
        DiagnosticCode::new(Category::StaticOperation, 900).expect("static LE code"),
        Severity::Error,
        message,
    );
    diagnostic.span = span;
    diagnostic
}

/// Compile a validated, ownership-safe primitive IR program to a Wasm module.
///
/// `exports` maps the external Wasm export spelling to a function ID in
/// `program`. The caller selects the application entry or library exports from
/// project metadata; this backend deliberately does not infer visibility or
/// package roots. Only exported functions and their transitive direct callees
/// are emitted, retaining their relative Program order. All source IR is
/// validated and checked before this artifact selection.
///
/// Internal direct calls support borrow/share references to non-Unit primitives
/// and to (nested) fixed arrays of them, owned array parameters (copied into the
/// callee's frame) and array results (written through a hidden pointer to
/// caller-allocated storage). Exported signatures remain primitive-only; reference
/// and array ABIs are not defined. Indirect calls, reference results and other
/// pointees are rejected.
/// Integer arithmetic is checked in every profile; a failed runtime check
/// traps with Wasm `unreachable` until the host runtime maps traps to language
/// runtime diagnostics.
pub fn compile(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
) -> Result<Vec<u8>, Vec<Diagnostic>> {
    if let Err(errors) = program.validate() {
        return Err(errors
            .into_iter()
            .map(|error| {
                let span = error
                    .function
                    .and_then(|id| program.functions.get(id.0 as usize))
                    .map(|function| function.span);
                diagnostic(format!("invalid IR: {}", error.message), span)
            })
            .collect());
    }
    let ownership = memobits_ownership::check_ownership(program);
    if !ownership.is_empty() {
        return Err(ownership);
    }
    let structs = match struct_layouts(&program.types) {
        Ok(structs) => structs,
        Err(message) => return Err(vec![diagnostic(message, None)]),
    };
    let mut errors = Vec::new();
    for (name, function) in exports {
        if program.functions.get(function.0 as usize).is_none() {
            errors.push(diagnostic(
                format!(
                    "Wasm export '{name}' refers to missing function {:?}",
                    function
                ),
                None,
            ));
        }
    }
    for id in exports.values() {
        if let Some(function) = program.functions.get(id.0 as usize) {
            if function
                .signature
                .parameters
                .iter()
                .any(|p| matches!(p.ty, Type::Array { .. }))
            {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot take arrays or array references; the external array ABI is not defined",
                    Some(function.span),
                ));
            } else if matches!(function.signature.result.as_ref(), Type::Array { .. }) {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot return arrays; the external array ABI is not defined",
                    Some(function.span),
                ));
            } else if !function.signature.parameters.iter().all(|p| {
                p.access == memobits_ir::Access::Owned && matches!(p.ty, Type::Primitive(_))
            }) || !matches!(function.signature.result.as_ref(), Type::Primitive(_))
            {
                errors.push(diagnostic(
                    "Wasm exported reference signatures have no defined external ABI",
                    Some(function.span),
                ));
            }
        }
    }
    for function in &program.functions {
        if let Err(error) = FrameLayout::for_function_in(&structs, function) {
            errors.push(diagnostic(error.message, error.span));
        }
        for block in &function.blocks {
            for instruction in &block.instructions {
                if let Some(message) = unsupported_instruction(instruction) {
                    errors.push(diagnostic(message, instruction.span));
                }
            }
        }
        if !primitive_signature(
            function.signature.parameters.iter(),
            &function.signature.result,
        ) {
            errors.push(diagnostic(
                "Wasm backend supports primitive or array results and primitive, array or borrow/share parameters only",
                Some(function.span),
            ));
        }
        if function
            .locals
            .iter()
            .any(|local| !supported_type(&local.ty))
            || function.values.iter().any(|ty| !supported_type(ty))
        {
            errors.push(diagnostic(
                "Wasm backend supports primitive and borrow/share primitive locals and values only",
                Some(function.span),
            ));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }

    encode(program, exports).map_err(|message| vec![diagnostic(message, None)])
}

fn unsupported_instruction(instruction: &Instruction) -> Option<String> {
    match &instruction.kind {
        InstructionKind::Constant(_)
        | InstructionKind::Capture(_)
        | InstructionKind::Copy { .. }
        | InstructionKind::Assign { .. } => None,
        InstructionKind::Borrow { .. }
        | InstructionKind::Load { .. }
        | InstructionKind::Store { .. } => None,
        InstructionKind::ArrayNew { .. } | InstructionKind::ElementAddr { .. } => None,
        InstructionKind::StructNew { .. } | InstructionKind::FieldAddr { .. } => None,
        InstructionKind::Call { callee, .. } => match callee.source {
            Source::Function(_) => None,
            _ => Some("indirect function calls are not supported by this Wasm backend yet".into()),
        },
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

fn primitive_signature<'a>(
    mut parameters: impl Iterator<Item = &'a memobits_ir::ParameterType>,
    result: &Type,
) -> bool {
    parameters.all(|p| match p.access {
        memobits_ir::Access::Owned => matches!(p.ty, Type::Primitive(_) | Type::Array { .. }),
        memobits_ir::Access::Borrow | memobits_ir::Access::Share => {
            matches!(p.ty, Type::Primitive(kind) if kind != Primitive::Unit)
                || matches!(p.ty, Type::Array { .. })
        }
    }) && matches!(result, Type::Primitive(_) | Type::Array { .. })
}

fn supported_type(ty: &Type) -> bool {
    match ty {
        Type::Primitive(_) => true,
        // A struct is an inline frame-cell value; it never crosses a signature.
        Type::Struct(_) => true,
        Type::Reference {
            access: memobits_ir::Access::Borrow | memobits_ir::Access::Share,
            inner,
        } => match inner.as_ref() {
            Type::Primitive(kind) => *kind != Primitive::Unit,
            array @ Type::Array { .. } => supported_type(array),
            _ => false,
        },
        Type::Array { element, .. } => match element.as_ref() {
            Type::Primitive(kind) => *kind != Primitive::Unit,
            nested @ Type::Array { .. } => supported_type(nested),
            _ => false,
        },
        _ => false,
    }
}

/// Upper bound for one activation frame. The shared stack page is 64 KiB, so a
/// source-supplied array length can never request host or guest memory beyond
/// this cap; larger layouts are compile-time diagnostics.
const MAX_FRAME_SIZE: u32 = 32 * 1024;

/// Identity of an array cell owner within one function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Slot {
    Local(u32),
    Value(u32),
}

/// Inline storage for an array-typed local or value. Nested arrays are laid
/// out contiguously row by row, so a cell is just an offset and a byte size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ArrayCell {
    offset: u32,
    size: u32,
}

/// Address-taken primitive owners have one authoritative cell per activation.
/// Reference locals and values carry the cell address rather than own a cell.
#[derive(Clone, Debug, PartialEq, Eq)]
struct FrameLayout {
    slots: BTreeMap<u32, FrameSlot>,
    /// Every array- or struct-typed local and value owns one inline cell.
    arrays: BTreeMap<Slot, ArrayCell>,
    /// Layout of each struct type, indexed by `TypeId`.
    structs: Vec<StructLayout>,
    size: u32,
}

/// Natural-alignment layout of a struct: fields in declaration order, each at
/// the next offset aligned to its own size, total size rounded up to the largest
/// field alignment. Fields are non-Unit primitives (validated).
#[derive(Clone, Debug, PartialEq, Eq)]
struct StructLayout {
    size: u32,
    align: u32,
    offsets: Vec<u32>,
    fields: Vec<Primitive>,
}

const STRUCT_LAYOUT_OVERFLOW: &str = "struct layout overflows the 32-bit address space";

fn struct_layouts(types: &[TypeDef]) -> Result<Vec<StructLayout>, String> {
    types
        .iter()
        .map(|definition| {
            let TypeDefKind::Struct { fields } = &definition.kind;
            let mut offset = 0u32;
            let mut align = 1u32;
            let mut offsets = Vec::with_capacity(fields.len());
            let mut primitives = Vec::with_capacity(fields.len());
            for field in fields {
                let Type::Primitive(kind) = field.ty else {
                    return Err(format!(
                        "field '{}' of struct '{}' is not a primitive",
                        field.name, definition.path.name
                    ));
                };
                let (size, field_align) = storage_layout(kind)?;
                offset = align_up(offset, field_align).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                offsets.push(offset);
                primitives.push(kind);
                offset = offset.checked_add(size).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                align = align.max(field_align);
            }
            Ok(StructLayout {
                size: align_up(offset, align).ok_or(STRUCT_LAYOUT_OVERFLOW)?,
                align,
                offsets,
                fields: primitives,
            })
        })
        .collect()
}

/// Size and alignment of an array or struct type.
fn aggregate_layout(structs: &[StructLayout], ty: &Type) -> Result<(u32, u32), String> {
    match ty {
        Type::Struct(id) => structs
            .get(id.0 as usize)
            .map(|layout| (layout.size, layout.align))
            .ok_or_else(|| "struct type is out of range".to_string()),
        other => array_layout(other),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FrameSlot {
    local: LocalId,
    offset: u32,
    size: u32,
    align: u32,
    ty: Primitive,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FrameLayoutError {
    message: String,
    span: Option<Span>,
}

impl FrameLayout {
    /// Layout for a function that uses no struct types.
    #[cfg(test)]
    fn for_function(function: &Function) -> Result<Self, FrameLayoutError> {
        Self::for_function_in(&[], function)
    }

    fn for_function_in(
        structs: &[StructLayout],
        function: &Function,
    ) -> Result<Self, FrameLayoutError> {
        let mut owners = BTreeSet::new();
        for block in &function.blocks {
            for instruction in &block.instructions {
                let InstructionKind::Borrow { owner, .. } = &instruction.kind else {
                    continue;
                };
                let error = |message: String| FrameLayoutError {
                    message,
                    span: owner.span.or(instruction.span),
                };
                let ty = match owner.source {
                    Source::Local(local) => {
                        &function
                            .locals
                            .get(local.0 as usize)
                            .ok_or_else(|| {
                                error(format!("borrow owner local {:?} is out of range", local))
                            })?
                            .ty
                    }
                    Source::Value(value) => {
                        function.values.get(value.0 as usize).ok_or_else(|| {
                            error(format!("borrow owner value {:?} is out of range", value))
                        })?
                    }
                    Source::Function(_) => {
                        return Err(error(
                            "borrowing a function is not supported by frame layout".into(),
                        ))
                    }
                };
                match ty {
                    Type::Primitive(primitive) => {
                        let Source::Local(local) = owner.source else {
                            return Err(error("borrowing a primitive temporary is not supported by frame layout".into()));
                        };
                        storage_layout(*primitive).map_err(error)?;
                        owners.insert(local.0);
                    }
                    Type::Reference { access: memobits_ir::Access::Borrow | memobits_ir::Access::Share, inner } => {
                        match inner.as_ref() {
                            Type::Primitive(primitive) => {
                                storage_layout(*primitive).map_err(error)?;
                            }
                            Type::Array { .. } => {}
                            _ => return Err(error("nested or non-primitive references are not supported by frame layout".into())),
                        }
                        // A reference already carries its owner's address. Reborrowing
                        // it must never create a second authoritative owner cell.
                    }
                    // An array owner already has its cell (one per array local or value).
                    Type::Array { .. } => {}
                    _ => return Err(error("Owned references and non-primitive owners are not supported by frame layout".into())),
                }
            }
        }

        let mut slots = BTreeMap::new();
        let mut offset = 0u32;
        for local_index in owners {
            let local_id = LocalId(local_index);
            let local = &function.locals[local_index as usize];
            let Type::Primitive(ty) = local.ty else {
                unreachable!("owner type was checked above")
            };
            let (size, align) = storage_layout(ty).expect("type checked above");
            offset = align_up(offset, align).ok_or_else(|| FrameLayoutError {
                message: "owner frame layout exceeds the 32-bit address space".into(),
                span: Some(local.span),
            })?;
            let end = offset.checked_add(size).ok_or_else(|| FrameLayoutError {
                message: "owner frame layout exceeds the 32-bit address space".into(),
                span: Some(local.span),
            })?;
            slots.insert(
                local_index,
                FrameSlot {
                    local: local_id,
                    offset,
                    size,
                    align,
                    ty,
                },
            );
            offset = end;
        }
        let array_types = function
            .locals
            .iter()
            .enumerate()
            .map(|(index, local)| (Slot::Local(index as u32), &local.ty, Some(local.span)))
            .chain(
                function
                    .values
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| (Slot::Value(index as u32), ty, None)),
            );
        let aliases = construction_aliases(function);
        let mut arrays = BTreeMap::new();
        for (slot, ty, span) in array_types {
            if !matches!(ty, Type::Array { .. } | Type::Struct(_)) {
                continue;
            }
            if matches!(slot, Slot::Value(value) if aliases.contains_key(&value)) {
                continue;
            }
            let error = |message: &str| FrameLayoutError {
                message: message.into(),
                span: span.or(Some(function.span)),
            };
            let too_large = if matches!(ty, Type::Struct(_)) {
                "struct frame layout exceeds the 32 KiB activation frame limit"
            } else {
                "array frame layout exceeds the 32 KiB activation frame limit"
            };
            let (bytes, align) = aggregate_layout(structs, ty).map_err(|m| {
                if m == LAYOUT_OVERFLOW {
                    error(too_large)
                } else {
                    error(&m)
                }
            })?;
            offset = align_up(offset, align).ok_or_else(|| error(too_large))?;
            let end = offset.checked_add(bytes).ok_or_else(|| error(too_large))?;
            if end > MAX_FRAME_SIZE {
                return Err(error(too_large));
            }
            arrays.insert(
                slot,
                ArrayCell {
                    offset,
                    size: bytes,
                },
            );
            offset = end;
        }
        for (value, local) in aliases {
            if let Some(cell) = arrays.get(&Slot::Local(local)).copied() {
                arrays.insert(Slot::Value(value), cell);
            }
        }
        let size = if slots.is_empty() && arrays.is_empty() {
            0
        } else {
            align_up(offset, 16)
                .ok_or_else(|| FrameLayoutError {
                    message: "aligned owner frame layout exceeds the 32-bit address space".into(),
                    span: Some(function.span),
                })?
                .max(16)
        };
        if size > MAX_FRAME_SIZE {
            return Err(FrameLayoutError {
                message: "activation frame exceeds the 32 KiB frame limit".into(),
                span: Some(function.span),
            });
        }
        Ok(Self {
            slots,
            arrays,
            structs: structs.to_vec(),
            size,
        })
    }
}

/// Array values built and immediately assigned to a local share that local's
/// cell, so the array is constructed in place instead of occupying a second
/// cell and being copied. The pattern is an `ArrayNew` or array `Capture`
/// whose output is consumed only by the very next instruction, an `Assign` to
/// a distinct array local. Element operands are scalars, so constructing into
/// the destination cannot read the cell being written.
fn construction_aliases(function: &Function) -> BTreeMap<u32, u32> {
    let mut uses = vec![0u32; function.values.len()];
    let mut count = |operand: &Operand| {
        if let Source::Value(value) = operand.source {
            if let Some(slot) = uses.get_mut(value.0 as usize) {
                *slot += 1;
            }
        }
    };
    let count_edge = |edge: &memobits_ir::Edge, count: &mut dyn FnMut(&Operand)| {
        edge.arguments.iter().for_each(&mut *count);
    };
    for block in &function.blocks {
        for instruction in &block.instructions {
            match &instruction.kind {
                InstructionKind::Constant(_) => {}
                InstructionKind::Capture(operand)
                | InstructionKind::Copy { source: operand }
                | InstructionKind::Borrow { owner: operand, .. }
                | InstructionKind::Load { reference: operand }
                | InstructionKind::Unary { operand, .. }
                | InstructionKind::Assign { value: operand, .. } => count(operand),
                InstructionKind::ArrayNew { init } => {
                    if let ArrayInit::Elements(elements) = init {
                        elements.iter().for_each(&mut count);
                    }
                }
                InstructionKind::ElementAddr { base, index, .. } => {
                    count(base);
                    count(index);
                }
                InstructionKind::FieldAddr { base, .. } => count(base),
                InstructionKind::StructNew { fields, .. } => fields.iter().for_each(&mut count),
                InstructionKind::Store { reference, value } => {
                    count(reference);
                    count(value);
                }
                InstructionKind::Binary { left, right, .. } => {
                    count(left);
                    count(right);
                }
                InstructionKind::Call { callee, arguments } => {
                    count(callee);
                    arguments.iter().for_each(&mut count);
                }
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Goto(edge) => count_edge(edge, &mut count),
            TerminatorKind::Branch {
                condition,
                then_edge,
                else_edge,
            } => {
                count(condition);
                count_edge(then_edge, &mut count);
                count_edge(else_edge, &mut count);
            }
            TerminatorKind::Return(value) => value.iter().for_each(&mut count),
            TerminatorKind::Unreachable => {}
        }
    }
    let mut aliases = BTreeMap::new();
    for block in &function.blocks {
        for pair in block.instructions.windows(2) {
            let [producer, consumer] = pair else { continue };
            let Some(output) = producer.output else {
                continue;
            };
            let InstructionKind::Assign {
                target,
                value:
                    Operand {
                        source: Source::Value(assigned),
                        ..
                    },
                ..
            } = &consumer.kind
            else {
                continue;
            };
            let source_is_target = matches!(
                &producer.kind,
                InstructionKind::Capture(Operand { source: Source::Local(local), .. }) if local == target
            );
            let array =
                |ty: Option<&Type>| matches!(ty, Some(Type::Array { .. } | Type::Struct(_)));
            if *assigned == output
                && uses[output.0 as usize] == 1
                && matches!(
                    producer.kind,
                    InstructionKind::ArrayNew { .. }
                        | InstructionKind::StructNew { .. }
                        | InstructionKind::Capture(_)
                )
                && array(function.values.get(output.0 as usize))
                && function.values.get(output.0 as usize)
                    == function.locals.get(target.0 as usize).map(|l| &l.ty)
                && !source_is_target
            {
                aliases.insert(output.0, target.0);
            }
        }
    }
    aliases
}

fn storage_layout(ty: Primitive) -> Result<(u32, u32), String> {
    let width = match ty {
        Primitive::Unit => return Err("Unit references are not supported by frame layout".into()),
        Primitive::Bool | Primitive::I8 | Primitive::U8 => 1,
        Primitive::I16 | Primitive::U16 => 2,
        Primitive::I32 | Primitive::U32 | Primitive::F32 => 4,
        Primitive::I64 | Primitive::U64 | Primitive::F64 => 8,
    };
    Ok((width, width))
}

const LAYOUT_OVERFLOW: &str = "array layout overflows the 32-bit address space";

/// Size and alignment of an array type: element size times length with checked
/// multiplication. Nested arrays recurse over the type only, so the cost depends
/// on nesting depth and never on any source-supplied count.
fn array_layout(ty: &Type) -> Result<(u32, u32), String> {
    match ty {
        Type::Primitive(kind) => storage_layout(*kind),
        Type::Array { element, len } => {
            let (size, align) = array_layout(element)?;
            let bytes = len.checked_mul(size).ok_or(LAYOUT_OVERFLOW)?;
            Ok((bytes, align))
        }
        _ => Err("array elements must be primitive or arrays in frame layout".into()),
    }
}

/// Byte size of the pointee of an array operand type (owner or reference).
fn array_bytes(ty: &Type) -> Result<u32, String> {
    match ty {
        Type::Array { .. } => array_layout(ty).map(|(size, _)| size),
        Type::Reference { inner, .. } => array_bytes(inner),
        _ => Err("expected an array type".into()),
    }
}

fn align_up(value: u32, align: u32) -> Option<u32> {
    debug_assert!(align.is_power_of_two());
    value
        .checked_add(align - 1)
        .map(|value| value & !(align - 1))
}

fn wasm_type(ty: &Type) -> ValType {
    match ty {
        Type::Primitive(
            Primitive::Unit
            | Primitive::Bool
            | Primitive::I8
            | Primitive::I16
            | Primitive::I32
            | Primitive::U8
            | Primitive::U16
            | Primitive::U32,
        ) => ValType::I32,
        Type::Primitive(Primitive::I64 | Primitive::U64) => ValType::I64,
        Type::Primitive(Primitive::F32) => ValType::F32,
        Type::Primitive(Primitive::F64) => ValType::F64,
        Type::Function(_) => unreachable!("unsupported function type checked before encoding"),
        Type::Reference { .. } => ValType::I32,
        // Array slots keep an unused Wasm local; their authoritative storage is
        // a frame cell and operands push the cell address.
        Type::Array { .. } | Type::Struct(_) => ValType::I32,
    }
}

// Experimental fixed one-page private stack. Address zero stays reserved; frames
// grow upward, aligned to 16 bytes. Traps do not unwind active caller frames.
const FRAME_START: u32 = 16;
const FRAME_LIMIT: u32 = 65536;

#[derive(Clone, Copy)]
struct FrameState {
    base: u32,
    size: u32,
}

impl FrameState {
    fn enter(self, body: &mut WasmFunction) {
        body.instruction(&WasmInstruction::GlobalGet(0));
        body.instruction(&WasmInstruction::LocalSet(self.base));
        // Check available space before addition, so neither wrapping nor a
        // failed allocation can mutate the shared stack pointer.
        body.instruction(&WasmInstruction::I32Const(self.size as i32));
        body.instruction(&WasmInstruction::I32Const(FRAME_LIMIT as i32));
        body.instruction(&WasmInstruction::LocalGet(self.base));
        body.instruction(&WasmInstruction::I32Sub);
        body.instruction(&WasmInstruction::I32GtU);
        trap_if(body);
        body.instruction(&WasmInstruction::LocalGet(self.base));
        body.instruction(&WasmInstruction::I32Const(self.size as i32));
        body.instruction(&WasmInstruction::I32Add);
        body.instruction(&WasmInstruction::GlobalSet(0));
    }

    fn restore(self, body: &mut WasmFunction) {
        body.instruction(&WasmInstruction::LocalGet(self.base));
        body.instruction(&WasmInstruction::GlobalSet(0));
    }
}

fn encode(program: &Program, exports: &BTreeMap<String, FunctionId>) -> Result<Vec<u8>, String> {
    let structs = struct_layouts(&program.types)?;
    let sizes = program
        .functions
        .iter()
        .map(|function| {
            FrameLayout::for_function_in(&structs, function)
                .map(|layout| layout.size)
                .map_err(|error| error.message)
        })
        .collect::<Result<Vec<_>, _>>()?;
    encode_frames(program, exports, &sizes, false)
}

// Tests may override frame sizes to exercise allocation and restoration
// independently of owner layout.
#[cfg(test)]
fn encode_with_frame_sizes(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    sizes: &[u32],
) -> Result<Vec<u8>, String> {
    encode_frames(program, exports, sizes, true)
}

fn encode_frames(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    sizes: &[u32],
    observe: bool,
) -> Result<Vec<u8>, String> {
    let mut reachable = BTreeSet::new();
    let mut pending = exports.values().copied().collect::<Vec<_>>();
    while let Some(id) = pending.pop() {
        if !reachable.insert(id.0) {
            continue;
        }
        for block in &program.functions[id.0 as usize].blocks {
            for instruction in &block.instructions {
                if let InstructionKind::Call {
                    callee:
                        Operand {
                            source: Source::Function(target),
                            ..
                        },
                    ..
                } = &instruction.kind
                {
                    pending.push(*target);
                }
            }
        }
    }
    let indices = reachable
        .iter()
        .enumerate()
        .map(|(index, id)| (*id, index as u32))
        .collect::<BTreeMap<_, _>>();
    let selected = reachable
        .iter()
        .map(|id| &program.functions[*id as usize])
        .collect::<Vec<_>>();
    let mut signatures = Vec::new();
    let function_types = selected
        .iter()
        .map(|function| {
            let signature = function.signature.clone();
            if let Some(index) = signatures.iter().position(|known| known == &signature) {
                index as u32
            } else {
                let index = signatures.len() as u32;
                signatures.push(signature);
                index
            }
        })
        .collect::<Vec<_>>();
    let mut types = TypeSection::new();
    for signature in &signatures {
        // An array result is written through a hidden trailing pointer
        // parameter to caller-allocated storage; the Wasm result list is empty.
        let hidden =
            matches!(signature.result.as_ref(), Type::Array { .. }).then_some(ValType::I32);
        let params = signature
            .parameters
            .iter()
            .map(|p| {
                if p.access == memobits_ir::Access::Owned {
                    wasm_type(&p.ty)
                } else {
                    ValType::I32
                }
            })
            .chain(hidden)
            .collect::<Vec<_>>();
        let results = if matches!(
            signature.result.as_ref(),
            Type::Primitive(Primitive::Unit) | Type::Array { .. }
        ) {
            Vec::new()
        } else {
            vec![wasm_type(&signature.result)]
        };
        types.ty().function(params, results);
    }
    let mut functions = FunctionSection::new();
    for type_index in &function_types {
        functions.function(*type_index);
    }
    let mut export_section = ExportSection::new();
    for (name, function) in exports {
        export_section.export(name, ExportKind::Func, indices[&function.0]);
    }
    let has_frames = reachable.iter().any(|id| sizes[*id as usize] != 0);
    if observe && has_frames {
        export_section.export("__test_memory", ExportKind::Memory, 0);
        export_section.export("__test_sp", ExportKind::Global, 0);
    }
    let structs = struct_layouts(&program.types)?;
    let mut code = CodeSection::new();
    for id in &reachable {
        code.function(&compile_function(
            &program.functions[*id as usize],
            &indices,
            sizes[*id as usize],
            observe,
            &structs,
        )?);
    }
    let mut memories = MemorySection::new();
    let mut globals = GlobalSection::new();
    if has_frames {
        memories.memory(MemoryType {
            minimum: 1,
            maximum: Some(1),
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(FRAME_START as i32),
        );
    }
    let mut module = Module::new();
    module.section(&types).section(&functions);
    if has_frames {
        module.section(&memories).section(&globals);
    }
    module.section(&export_section).section(&code);
    Ok(module.finish())
}

fn compile_function(
    function: &Function,
    indices: &BTreeMap<u32, u32>,
    frame_size: u32,
    observe: bool,
    structs: &[StructLayout],
) -> Result<WasmFunction, String> {
    let layout = FrameLayout::for_function_in(structs, function).map_err(|error| error.message)?;
    let result_is_array = matches!(function.signature.result.as_ref(), Type::Array { .. });
    // Wasm parameters: the source parameters plus, for an array result, one
    // hidden pointer to the caller-allocated result storage (last parameter).
    let param_count = function.signature.parameters.len() as u32 + u32::from(result_is_array);
    let mut local_types = function
        .locals
        .iter()
        .map(|local| wasm_type(&local.ty))
        .collect::<Vec<_>>();
    local_types.extend(function.values.iter().map(wasm_type));
    local_types.push(ValType::I32); // dispatcher program counter
    local_types.push(ValType::I64); // exact wide intermediate for <= 32-bit ints
    if frame_size != 0 {
        local_types.push(ValType::I32);
    } // activation frame base
    let locals = local_types
        .into_iter()
        .map(|ty| (1, ty))
        .collect::<Vec<_>>();
    let pc = param_count + function.locals.len() as u32 + function.values.len() as u32;
    let scratch64 = pc + 1;
    let mut wasm = WasmFunction::new(locals);
    let body = &mut wasm;
    let frame = (frame_size != 0).then_some(FrameState {
        base: scratch64 + 1,
        size: frame_size,
    });
    if let Some(frame) = frame {
        frame.enter(body);
        if observe {
            // Test-only watermark in the allocated frame: its own base address.
            body.instruction(&WasmInstruction::LocalGet(frame.base));
            body.instruction(&WasmInstruction::LocalGet(frame.base));
            body.instruction(&WasmInstruction::I32Store(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                target: wasm_encoder::MemArgTarget::Memory(0),
                ordering: None,
            }));
        }
    }
    for (index, local) in function.parameter_locals.iter().enumerate() {
        guard_parameter(body, index as u32, &function.locals[local.0 as usize].ty)?;
        if let Some(slot) = layout.slots.get(&local.0) {
            emit_address(body, frame.ok_or("owner cell requires frame")?, slot.offset);
            body.instruction(&WasmInstruction::LocalGet(index as u32));
            emit_store(body, slot.ty);
            continue;
        }
        if let Some(cell) = layout.arrays.get(&Slot::Local(local.0)) {
            // An owned array arrives as a pointer to caller-side storage. The
            // callee copies it into its own cell, so mutating a `var` parameter
            // never reaches the caller and recursion keeps separate frames.
            emit_address(body, frame.ok_or("array cell requires frame")?, cell.offset);
            body.instruction(&WasmInstruction::LocalGet(index as u32));
            body.instruction(&WasmInstruction::I32Const(cell.size as i32));
            body.instruction(&WasmInstruction::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
            continue;
        }
        body.instruction(&WasmInstruction::LocalGet(index as u32));
        body.instruction(&WasmInstruction::LocalSet(param_count + local.0));
    }
    body.instruction(&WasmInstruction::I32Const(function.entry.0 as i32));
    body.instruction(&WasmInstruction::LocalSet(pc));
    body.instruction(&WasmInstruction::Loop(BlockType::Empty));
    for (block_id, block) in function.blocks.iter().enumerate() {
        body.instruction(&WasmInstruction::LocalGet(pc));
        body.instruction(&WasmInstruction::I32Const(block_id as i32));
        body.instruction(&WasmInstruction::I32Eq);
        body.instruction(&WasmInstruction::If(BlockType::Empty));
        for instruction in &block.instructions {
            compile_instruction(
                body,
                instruction,
                function,
                param_count,
                scratch64,
                indices,
                &layout,
                frame,
            )?;
        }
        compile_terminator(
            body,
            &block.terminator.kind,
            function,
            pc,
            param_count,
            frame,
            &layout,
        )?;
        body.instruction(&WasmInstruction::End);
    }
    body.instruction(&WasmInstruction::Unreachable);
    body.instruction(&WasmInstruction::End);
    body.instruction(&WasmInstruction::Unreachable);
    body.instruction(&WasmInstruction::End);
    Ok(wasm)
}

// Address-taken owners live exclusively in their frame cells. The arithmetic
// helpers use Wasm locals as instruction-scoped snapshots, refreshed on every
// operand use; assignments never update a second persistent owner copy.
fn emit_address(body: &mut WasmFunction, frame: FrameState, offset: u32) {
    body.instruction(&WasmInstruction::LocalGet(frame.base));
    body.instruction(&WasmInstruction::I32Const(offset as i32));
    body.instruction(&WasmInstruction::I32Add);
}

fn memory_arg(kind: Primitive) -> MemArg {
    let (_, align) = storage_layout(kind).expect("validated reference primitive");
    MemArg {
        offset: 0,
        align: align.trailing_zeros(),
        target: wasm_encoder::MemArgTarget::Memory(0),
        ordering: None,
    }
}

fn emit_load(body: &mut WasmFunction, kind: Primitive) {
    // References are created only from live owner cells and never cross the
    // export ABI. Private memory receives only validated typed stores, so Bool
    // cells remain 0/1 and reference addresses need no host-pointer checks.
    let arg = memory_arg(kind);
    body.instruction(&match kind {
        Primitive::Bool | Primitive::U8 => WasmInstruction::I32Load8U(arg),
        Primitive::I8 => WasmInstruction::I32Load8S(arg),
        Primitive::U16 => WasmInstruction::I32Load16U(arg),
        Primitive::I16 => WasmInstruction::I32Load16S(arg),
        Primitive::I32 | Primitive::U32 => WasmInstruction::I32Load(arg),
        Primitive::I64 | Primitive::U64 => WasmInstruction::I64Load(arg),
        Primitive::F32 => WasmInstruction::F32Load(arg),
        Primitive::F64 => WasmInstruction::F64Load(arg),
        Primitive::Unit => unreachable!("Unit references rejected"),
    });
}

fn emit_store(body: &mut WasmFunction, kind: Primitive) {
    let arg = memory_arg(kind);
    body.instruction(&match kind {
        Primitive::Bool | Primitive::U8 | Primitive::I8 => WasmInstruction::I32Store8(arg),
        Primitive::U16 | Primitive::I16 => WasmInstruction::I32Store16(arg),
        Primitive::I32 | Primitive::U32 => WasmInstruction::I32Store(arg),
        Primitive::I64 | Primitive::U64 => WasmInstruction::I64Store(arg),
        Primitive::F32 => WasmInstruction::F32Store(arg),
        Primitive::F64 => WasmInstruction::F64Store(arg),
        Primitive::Unit => unreachable!("Unit references rejected"),
    });
}

fn reference_primitive(function: &Function, operand: &Operand) -> Result<Primitive, String> {
    match value_type(function, operand)? {
        Type::Reference { inner, .. } => match *inner {
            Type::Primitive(kind) if kind != Primitive::Unit => Ok(kind),
            _ => Err("unsupported reference pointee".into()),
        },
        _ => Err("expected primitive reference".into()),
    }
}

fn emit_operand(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    operand: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    if let Source::Local(local) = operand.source {
        if let Some(slot) = layout.slots.get(&local.0) {
            emit_address(body, frame.ok_or("owner cell requires frame")?, slot.offset);
            emit_load(body, slot.ty);
            return Ok(());
        }
    }
    if let Some(cell) = array_cell(layout, operand) {
        emit_address(body, frame.ok_or("array cell requires frame")?, cell.offset);
        return Ok(());
    }
    body.instruction(&WasmInstruction::LocalGet(operand_local(
        function,
        param_count,
        operand,
    )?));
    Ok(())
}

fn array_cell(layout: &FrameLayout, operand: &Operand) -> Option<ArrayCell> {
    let slot = match operand.source {
        Source::Local(local) => Slot::Local(local.0),
        Source::Value(value) => Slot::Value(value.0),
        Source::Function(_) => return None,
    };
    layout.arrays.get(&slot).copied()
}

fn array_cell_of(layout: &FrameLayout, slot: Slot) -> Result<ArrayCell, String> {
    layout
        .arrays
        .get(&slot)
        .copied()
        .ok_or_else(|| "array storage cell is missing".to_string())
}

/// Copy a whole array between two cells of identical layout.
fn emit_array_copy(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    destination: ArrayCell,
    source: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    let frame = frame.ok_or("array cell requires frame")?;
    if array_cell(layout, source).is_some_and(|cell| cell.offset == destination.offset) {
        // The array was constructed in the destination cell already.
        return Ok(());
    }
    emit_address(body, frame, destination.offset);
    emit_operand(body, function, param_count, source, layout, frame.into())?;
    body.instruction(&WasmInstruction::I32Const(destination.size as i32));
    body.instruction(&WasmInstruction::MemoryCopy {
        src_mem: 0,
        dst_mem: 0,
    });
    Ok(())
}

fn refresh_operand(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    operand: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    if let Source::Local(local) = operand.source {
        if layout.slots.contains_key(&local.0) {
            emit_operand(body, function, param_count, operand, layout, frame)?;
            body.instruction(&WasmInstruction::LocalSet(param_count + local.0));
        }
    }
    Ok(())
}

fn value_local(function: &Function, param_count: u32, value: memobits_ir::ValueId) -> u32 {
    param_count + function.locals.len() as u32 + value.0
}

fn operand_local(function: &Function, param_count: u32, operand: &Operand) -> Result<u32, String> {
    match operand.source {
        Source::Local(local) => Ok(param_count + local.0),
        Source::Value(value) => Ok(value_local(function, param_count, value)),
        Source::Function(_) => {
            Err("function operands are only supported as direct call targets".into())
        }
    }
}

fn value_type(function: &Function, operand: &Operand) -> Result<Type, String> {
    match operand.source {
        Source::Local(local) => Ok(function.locals[local.0 as usize].ty.clone()),
        Source::Value(value) => Ok(function.values[value.0 as usize].clone()),
        Source::Function(_) => Err("function references have no scalar value type".into()),
    }
}

fn guard_parameter(body: &mut WasmFunction, parameter: u32, ty: &Type) -> Result<(), String> {
    let Type::Primitive(kind) = ty else {
        if supported_type(ty) {
            return Ok(());
        }
        return Err("function-valued parameters are unsupported".into());
    };
    let get = |body: &mut WasmFunction| {
        body.instruction(&WasmInstruction::LocalGet(parameter));
    };
    match kind {
        Primitive::Unit | Primitive::Bool => {
            get(body);
            if *kind == Primitive::Unit {
                body.instruction(&WasmInstruction::I32Eqz);
                body.instruction(&WasmInstruction::I32Eqz);
            } else {
                body.instruction(&WasmInstruction::I32Const(1));
                body.instruction(&WasmInstruction::I32GtU);
            }
            trap_if(body);
        }
        Primitive::I8 | Primitive::I16 => {
            let (min, max) = if *kind == Primitive::I8 {
                (i8::MIN as i32, i8::MAX as i32)
            } else {
                (i16::MIN as i32, i16::MAX as i32)
            };
            get(body);
            body.instruction(&WasmInstruction::I32Const(min));
            body.instruction(&WasmInstruction::I32LtS);
            trap_if(body);
            get(body);
            body.instruction(&WasmInstruction::I32Const(max));
            body.instruction(&WasmInstruction::I32GtS);
            trap_if(body);
        }
        Primitive::U8 | Primitive::U16 => {
            let max = if *kind == Primitive::U8 {
                u8::MAX as i32
            } else {
                u16::MAX as i32
            };
            get(body);
            body.instruction(&WasmInstruction::I32Const(max));
            body.instruction(&WasmInstruction::I32GtU);
            trap_if(body);
        }
        _ => {}
    }
    Ok(())
}

fn trap_if(body: &mut WasmFunction) {
    body.instruction(&WasmInstruction::If(BlockType::Empty));
    body.instruction(&WasmInstruction::Unreachable);
    body.instruction(&WasmInstruction::End);
}

fn emit_unary(
    body: &mut WasmFunction,
    op: UnaryOp,
    input: u32,
    ty: &Type,
    output: u32,
) -> Result<(), String> {
    match (op, ty) {
        (UnaryOp::Plus, Type::Primitive(_)) => {
            body.instruction(&WasmInstruction::LocalGet(input));
        }
        (UnaryOp::Not, Type::Primitive(Primitive::Bool)) => {
            body.instruction(&WasmInstruction::LocalGet(input));
            body.instruction(&WasmInstruction::I32Eqz);
        }
        (UnaryOp::Negate, Type::Primitive(Primitive::F32)) => {
            body.instruction(&WasmInstruction::LocalGet(input));
            body.instruction(&WasmInstruction::F32Neg);
        }
        (UnaryOp::Negate, Type::Primitive(Primitive::F64)) => {
            body.instruction(&WasmInstruction::LocalGet(input));
            body.instruction(&WasmInstruction::F64Neg);
        }
        (UnaryOp::Negate, Type::Primitive(kind)) => {
            let (min, is_i64) = match kind {
                Primitive::I8 => (i8::MIN as i64, false),
                Primitive::I16 => (i16::MIN as i64, false),
                Primitive::I32 => (i32::MIN as i64, false),
                Primitive::I64 => (i64::MIN, true),
                _ => return Err("integer negation requires a signed integer".into()),
            };
            body.instruction(&WasmInstruction::LocalGet(input));
            if is_i64 {
                body.instruction(&WasmInstruction::I64Const(min));
                body.instruction(&WasmInstruction::I64Eq);
            } else {
                body.instruction(&WasmInstruction::I32Const(min as i32));
                body.instruction(&WasmInstruction::I32Eq);
            }
            trap_if(body);
            if is_i64 {
                body.instruction(&WasmInstruction::I64Const(0));
                body.instruction(&WasmInstruction::LocalGet(input));
                body.instruction(&WasmInstruction::I64Sub);
            } else {
                body.instruction(&WasmInstruction::I32Const(0));
                body.instruction(&WasmInstruction::LocalGet(input));
                body.instruction(&WasmInstruction::I32Sub);
            }
        }
        _ => return Err("unary operation and primitive type are incompatible".into()),
    };
    body.instruction(&WasmInstruction::LocalSet(output));
    Ok(())
}

fn emit_binary(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    ty: &Type,
    output: u32,
    scratch64: u32,
) -> Result<(), String> {
    if matches!(
        op,
        BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual
    ) {
        emit_compare(body, op, left, right, ty)?;
        body.instruction(&WasmInstruction::LocalSet(output));
        return Ok(());
    }
    let Type::Primitive(kind) = ty else {
        return Err("binary arithmetic requires primitive operands".into());
    };
    match kind {
        Primitive::Bool if matches!(op, BinaryOp::Equal | BinaryOp::NotEqual) => {
            body.instruction(&WasmInstruction::LocalGet(left));
            body.instruction(&WasmInstruction::LocalGet(right));
            body.instruction(if op == BinaryOp::Equal {
                &WasmInstruction::I32Eq
            } else {
                &WasmInstruction::I32Ne
            });
        }
        Primitive::F32 | Primitive::F64 => {
            if op == BinaryOp::Remainder {
                return Err("floating-point remainder is unsupported".into());
            }
            body.instruction(&WasmInstruction::LocalGet(left));
            body.instruction(&WasmInstruction::LocalGet(right));
            let instruction = match (kind, op) {
                (Primitive::F32, BinaryOp::Add) => WasmInstruction::F32Add,
                (Primitive::F32, BinaryOp::Subtract) => WasmInstruction::F32Sub,
                (Primitive::F32, BinaryOp::Multiply) => WasmInstruction::F32Mul,
                (Primitive::F32, BinaryOp::Divide) => WasmInstruction::F32Div,
                (Primitive::F64, BinaryOp::Add) => WasmInstruction::F64Add,
                (Primitive::F64, BinaryOp::Subtract) => WasmInstruction::F64Sub,
                (Primitive::F64, BinaryOp::Multiply) => WasmInstruction::F64Mul,
                (Primitive::F64, BinaryOp::Divide) => WasmInstruction::F64Div,
                _ => return Err("unsupported floating-point operation".into()),
            };
            body.instruction(&instruction);
        }
        Primitive::I8
        | Primitive::I16
        | Primitive::I32
        | Primitive::U8
        | Primitive::U16
        | Primitive::U32 => {
            return emit_narrow_integer(body, op, left, right, *kind, output, scratch64);
        }
        Primitive::I64 | Primitive::U64 => {
            return emit_wide_integer(body, op, left, right, *kind, output);
        }
        Primitive::Unit => return Err("Unit does not support binary operations".into()),
        Primitive::Bool => return Err("Bool supports equality comparisons only".into()),
    }
    body.instruction(&WasmInstruction::LocalSet(output));
    Ok(())
}

fn emit_compare(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    ty: &Type,
) -> Result<(), String> {
    let Type::Primitive(kind) = ty else {
        return Err("comparison requires primitive operands".into());
    };
    body.instruction(&WasmInstruction::LocalGet(left));
    body.instruction(&WasmInstruction::LocalGet(right));
    let signed = matches!(
        kind,
        Primitive::I8 | Primitive::I16 | Primitive::I32 | Primitive::I64
    );
    let instruction = match (kind, op) {
        (Primitive::F32, BinaryOp::Equal) => WasmInstruction::F32Eq,
        (Primitive::F32, BinaryOp::NotEqual) => WasmInstruction::F32Ne,
        (Primitive::F32, BinaryOp::Less) => WasmInstruction::F32Lt,
        (Primitive::F32, BinaryOp::LessEqual) => WasmInstruction::F32Le,
        (Primitive::F32, BinaryOp::Greater) => WasmInstruction::F32Gt,
        (Primitive::F32, BinaryOp::GreaterEqual) => WasmInstruction::F32Ge,
        (Primitive::F64, BinaryOp::Equal) => WasmInstruction::F64Eq,
        (Primitive::F64, BinaryOp::NotEqual) => WasmInstruction::F64Ne,
        (Primitive::F64, BinaryOp::Less) => WasmInstruction::F64Lt,
        (Primitive::F64, BinaryOp::LessEqual) => WasmInstruction::F64Le,
        (Primitive::F64, BinaryOp::Greater) => WasmInstruction::F64Gt,
        (Primitive::F64, BinaryOp::GreaterEqual) => WasmInstruction::F64Ge,
        (Primitive::Bool | Primitive::Unit, BinaryOp::Equal) => WasmInstruction::I32Eq,
        (Primitive::Bool | Primitive::Unit, BinaryOp::NotEqual) => WasmInstruction::I32Ne,
        (_, BinaryOp::Equal) => {
            if matches!(kind, Primitive::I64 | Primitive::U64) {
                WasmInstruction::I64Eq
            } else {
                WasmInstruction::I32Eq
            }
        }
        (_, BinaryOp::NotEqual) => {
            if matches!(kind, Primitive::I64 | Primitive::U64) {
                WasmInstruction::I64Ne
            } else {
                WasmInstruction::I32Ne
            }
        }
        (_, BinaryOp::Less) => int_compare(
            *kind,
            signed,
            WasmInstruction::I32LtS,
            WasmInstruction::I32LtU,
            WasmInstruction::I64LtS,
            WasmInstruction::I64LtU,
        ),
        (_, BinaryOp::LessEqual) => int_compare(
            *kind,
            signed,
            WasmInstruction::I32LeS,
            WasmInstruction::I32LeU,
            WasmInstruction::I64LeS,
            WasmInstruction::I64LeU,
        ),
        (_, BinaryOp::Greater) => int_compare(
            *kind,
            signed,
            WasmInstruction::I32GtS,
            WasmInstruction::I32GtU,
            WasmInstruction::I64GtS,
            WasmInstruction::I64GtU,
        ),
        (_, BinaryOp::GreaterEqual) => int_compare(
            *kind,
            signed,
            WasmInstruction::I32GeS,
            WasmInstruction::I32GeU,
            WasmInstruction::I64GeS,
            WasmInstruction::I64GeU,
        ),
        _ => return Err("unsupported comparison".into()),
    };
    body.instruction(&instruction);
    Ok(())
}

fn int_compare(
    kind: Primitive,
    signed: bool,
    i32_signed: WasmInstruction<'static>,
    i32_unsigned: WasmInstruction<'static>,
    i64_signed: WasmInstruction<'static>,
    i64_unsigned: WasmInstruction<'static>,
) -> WasmInstruction<'static> {
    if matches!(kind, Primitive::I64 | Primitive::U64) {
        if signed {
            i64_signed
        } else {
            i64_unsigned
        }
    } else if signed {
        i32_signed
    } else {
        i32_unsigned
    }
}

fn emit_narrow_integer(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    kind: Primitive,
    output: u32,
    scratch: u32,
) -> Result<(), String> {
    if matches!(op, BinaryOp::Divide | BinaryOp::Remainder) {
        if matches!(kind, Primitive::I8 | Primitive::I16) && op == BinaryOp::Divide {
            let min = if kind == Primitive::I8 {
                i8::MIN as i32
            } else {
                i16::MIN as i32
            };
            body.instruction(&WasmInstruction::LocalGet(left));
            body.instruction(&WasmInstruction::I32Const(min));
            body.instruction(&WasmInstruction::I32Eq);
            body.instruction(&WasmInstruction::LocalGet(right));
            body.instruction(&WasmInstruction::I32Const(-1));
            body.instruction(&WasmInstruction::I32Eq);
            body.instruction(&WasmInstruction::I32And);
            trap_if(body);
        }
        body.instruction(&WasmInstruction::LocalGet(left));
        body.instruction(&WasmInstruction::LocalGet(right));
        let unsigned = matches!(kind, Primitive::U8 | Primitive::U16 | Primitive::U32);
        body.instruction(match (op, unsigned) {
            (BinaryOp::Divide, true) => &WasmInstruction::I32DivU,
            (BinaryOp::Divide, false) => &WasmInstruction::I32DivS,
            (BinaryOp::Remainder, true) => &WasmInstruction::I32RemU,
            (BinaryOp::Remainder, false) => &WasmInstruction::I32RemS,
            _ => unreachable!(),
        });
        body.instruction(&WasmInstruction::LocalSet(output));
        return Ok(());
    }

    let signed = matches!(kind, Primitive::I8 | Primitive::I16 | Primitive::I32);
    body.instruction(&WasmInstruction::LocalGet(left));
    body.instruction(if signed {
        &WasmInstruction::I64ExtendI32S
    } else {
        &WasmInstruction::I64ExtendI32U
    });
    body.instruction(&WasmInstruction::LocalGet(right));
    body.instruction(if signed {
        &WasmInstruction::I64ExtendI32S
    } else {
        &WasmInstruction::I64ExtendI32U
    });
    body.instruction(match op {
        BinaryOp::Add => &WasmInstruction::I64Add,
        BinaryOp::Subtract => &WasmInstruction::I64Sub,
        BinaryOp::Multiply => &WasmInstruction::I64Mul,
        _ => return Err("unsupported narrow integer operation".into()),
    });
    body.instruction(&WasmInstruction::LocalSet(scratch));

    let (min, max) = match kind {
        Primitive::I8 => (Some(i8::MIN as i64), Some(i8::MAX as i64)),
        Primitive::I16 => (Some(i16::MIN as i64), Some(i16::MAX as i64)),
        Primitive::I32 => (Some(i32::MIN as i64), Some(i32::MAX as i64)),
        Primitive::U8 => (None, Some(u8::MAX as i64)),
        Primitive::U16 => (None, Some(u16::MAX as i64)),
        Primitive::U32 => (None, Some(u32::MAX as i64)),
        _ => return Err("non-narrow type reached narrow integer emission".into()),
    };
    if let Some(min) = min {
        body.instruction(&WasmInstruction::LocalGet(scratch));
        body.instruction(&WasmInstruction::I64Const(min));
        body.instruction(&WasmInstruction::I64LtS);
        trap_if(body);
    }
    if let Some(max) = max {
        body.instruction(&WasmInstruction::LocalGet(scratch));
        body.instruction(&WasmInstruction::I64Const(max));
        body.instruction(if signed {
            &WasmInstruction::I64GtS
        } else {
            &WasmInstruction::I64GtU
        });
        trap_if(body);
    }
    body.instruction(&WasmInstruction::LocalGet(scratch));
    body.instruction(&WasmInstruction::I32WrapI64);
    body.instruction(&WasmInstruction::LocalSet(output));
    Ok(())
}

fn emit_wide_integer(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    kind: Primitive,
    output: u32,
) -> Result<(), String> {
    let signed = kind == Primitive::I64;
    body.instruction(&WasmInstruction::LocalGet(left));
    body.instruction(&WasmInstruction::LocalGet(right));
    match op {
        BinaryOp::Add => {
            body.instruction(&WasmInstruction::I64Add);
            body.instruction(&WasmInstruction::LocalSet(output));
            if signed {
                body.instruction(&WasmInstruction::LocalGet(left));
                body.instruction(&WasmInstruction::LocalGet(output));
                body.instruction(&WasmInstruction::I64Xor);
                body.instruction(&WasmInstruction::LocalGet(right));
                body.instruction(&WasmInstruction::LocalGet(output));
                body.instruction(&WasmInstruction::I64Xor);
                body.instruction(&WasmInstruction::I64And);
                body.instruction(&WasmInstruction::I64Const(0));
                body.instruction(&WasmInstruction::I64LtS);
            } else {
                body.instruction(&WasmInstruction::LocalGet(output));
                body.instruction(&WasmInstruction::LocalGet(left));
                body.instruction(&WasmInstruction::I64LtU);
            }
            trap_if(body);
        }
        BinaryOp::Subtract => {
            body.instruction(&WasmInstruction::I64Sub);
            body.instruction(&WasmInstruction::LocalSet(output));
            if signed {
                body.instruction(&WasmInstruction::LocalGet(left));
                body.instruction(&WasmInstruction::LocalGet(right));
                body.instruction(&WasmInstruction::I64Xor);
                body.instruction(&WasmInstruction::LocalGet(left));
                body.instruction(&WasmInstruction::LocalGet(output));
                body.instruction(&WasmInstruction::I64Xor);
                body.instruction(&WasmInstruction::I64And);
                body.instruction(&WasmInstruction::I64Const(0));
                body.instruction(&WasmInstruction::I64LtS);
            } else {
                body.instruction(&WasmInstruction::LocalGet(left));
                body.instruction(&WasmInstruction::LocalGet(right));
                body.instruction(&WasmInstruction::I64LtU);
            }
            trap_if(body);
        }
        BinaryOp::Multiply => {
            body.instruction(&WasmInstruction::I64Mul);
            body.instruction(&WasmInstruction::LocalSet(output));
            if signed {
                // The quotient check is safe after excluding the one pair that
                // could itself trap during the check (MIN * -1).
                body.instruction(&WasmInstruction::LocalGet(left));
                body.instruction(&WasmInstruction::I64Const(i64::MIN));
                body.instruction(&WasmInstruction::I64Eq);
                body.instruction(&WasmInstruction::LocalGet(right));
                body.instruction(&WasmInstruction::I64Const(-1));
                body.instruction(&WasmInstruction::I64Eq);
                body.instruction(&WasmInstruction::I32And);
                body.instruction(&WasmInstruction::LocalGet(right));
                body.instruction(&WasmInstruction::I64Const(i64::MIN));
                body.instruction(&WasmInstruction::I64Eq);
                body.instruction(&WasmInstruction::LocalGet(left));
                body.instruction(&WasmInstruction::I64Const(-1));
                body.instruction(&WasmInstruction::I64Eq);
                body.instruction(&WasmInstruction::I32And);
                body.instruction(&WasmInstruction::I32Or);
                trap_if(body);
            }
            body.instruction(&WasmInstruction::LocalGet(left));
            body.instruction(&WasmInstruction::I64Eqz);
            body.instruction(&WasmInstruction::I32Eqz);
            body.instruction(&WasmInstruction::If(BlockType::Empty));
            body.instruction(&WasmInstruction::LocalGet(output));
            body.instruction(&WasmInstruction::LocalGet(left));
            body.instruction(if signed {
                &WasmInstruction::I64DivS
            } else {
                &WasmInstruction::I64DivU
            });
            body.instruction(&WasmInstruction::LocalGet(right));
            body.instruction(&WasmInstruction::I64Ne);
            trap_if(body);
            body.instruction(&WasmInstruction::End);
        }
        BinaryOp::Divide | BinaryOp::Remainder => {
            body.instruction(match (op, signed) {
                (BinaryOp::Divide, true) => &WasmInstruction::I64DivS,
                (BinaryOp::Divide, false) => &WasmInstruction::I64DivU,
                (BinaryOp::Remainder, true) => &WasmInstruction::I64RemS,
                (BinaryOp::Remainder, false) => &WasmInstruction::I64RemU,
                _ => unreachable!(),
            });
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        _ => return Err("unsupported wide integer operation".into()),
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn compile_instruction(
    body: &mut wasm_encoder::Function,
    instruction: &Instruction,
    function: &Function,
    param_count: u32,
    scratch64: u32,
    indices: &BTreeMap<u32, u32>,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    let output = instruction
        .output
        .map(|id| value_local(function, param_count, id));
    match &instruction.kind {
        InstructionKind::Constant(constant) => {
            let output = output.ok_or("constant lacks an output")?;
            emit_constant(
                body,
                constant,
                function.values[instruction.output.unwrap().0 as usize].clone(),
            )?;
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::Capture(operand) => {
            let output = output.ok_or("capture lacks an output")?;
            if let Ok(cell) = array_cell_of(layout, Slot::Value(instruction.output.unwrap().0)) {
                return emit_array_copy(body, function, param_count, cell, operand, layout, frame);
            }
            emit_operand(body, function, param_count, operand, layout, frame)?;
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::Copy { source } => {
            let output = output.ok_or("copy lacks an output")?;
            emit_operand(body, function, param_count, source, layout, frame)?;
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::ArrayNew { init } => {
            let value = instruction.output.ok_or("array creation lacks an output")?;
            let cell = array_cell_of(layout, Slot::Value(value.0))?;
            let frame = frame.ok_or("array cell requires frame")?;
            let Type::Array { element, len } = function.values[value.0 as usize].clone() else {
                return Err("array creation output must have an array type".into());
            };
            let (size, _) = array_layout(&element)?;
            match init {
                ArrayInit::Elements(elements) => {
                    if elements.len() != len as usize {
                        return Err("array literal length differs from its array type".into());
                    }
                    for (index, operand) in elements.iter().enumerate() {
                        let destination = cell
                            .offset
                            .checked_add(
                                u32::try_from(index)
                                    .ok()
                                    .and_then(|index| index.checked_mul(size))
                                    .ok_or(LAYOUT_OVERFLOW)?,
                            )
                            .ok_or(LAYOUT_OVERFLOW)?;
                        emit_address(body, frame, destination);
                        emit_operand(body, function, param_count, operand, layout, Some(frame))?;
                        match element.as_ref() {
                            Type::Primitive(kind) => emit_store(body, *kind),
                            _ => {
                                // A nested array element is copied from its cell.
                                body.instruction(&WasmInstruction::I32Const(size as i32));
                                body.instruction(&WasmInstruction::MemoryCopy {
                                    src_mem: 0,
                                    dst_mem: 0,
                                });
                            }
                        }
                    }
                }
                ArrayInit::Zeroed => {
                    emit_address(body, frame, cell.offset);
                    body.instruction(&WasmInstruction::I32Const(0));
                    body.instruction(&WasmInstruction::I32Const(cell.size as i32));
                    body.instruction(&WasmInstruction::MemoryFill(0));
                }
            }
        }
        InstructionKind::StructNew { fields, .. } => {
            let value = instruction
                .output
                .ok_or("struct creation lacks an output")?;
            let cell = array_cell_of(layout, Slot::Value(value.0))?;
            let frame = frame.ok_or("struct cell requires frame")?;
            let Type::Struct(type_id) = function.values[value.0 as usize] else {
                return Err("struct creation output must have a struct type".into());
            };
            let struct_layout = layout
                .structs
                .get(type_id.0 as usize)
                .ok_or("struct type is out of range")?;
            if struct_layout.offsets.len() != fields.len() {
                return Err("struct creation operand count differs from its type".into());
            }
            for (index, operand) in fields.iter().enumerate() {
                let destination = cell
                    .offset
                    .checked_add(struct_layout.offsets[index])
                    .ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                emit_address(body, frame, destination);
                emit_operand(body, function, param_count, operand, layout, Some(frame))?;
                emit_store(body, struct_layout.fields[index]);
            }
        }
        InstructionKind::FieldAddr { base, field, .. } => {
            let output = output.ok_or("field address lacks an output")?;
            // The base is a struct owner: its operand is the cell address.
            let Type::Struct(type_id) = value_type(function, base)? else {
                return Err("field address base is not a struct".into());
            };
            let offset = layout
                .structs
                .get(type_id.0 as usize)
                .and_then(|struct_layout| struct_layout.offsets.get(*field as usize))
                .copied()
                .ok_or("field address refers to a missing field")?;
            emit_operand(body, function, param_count, base, layout, frame)?;
            body.instruction(&WasmInstruction::I32Const(offset as i32));
            body.instruction(&WasmInstruction::I32Add);
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::ElementAddr { base, index, .. } => {
            let output = output.ok_or("element address lacks an output")?;
            // The base is an array owner (its operand is the cell address) or a
            // reference to an array (its operand is the owner's address).
            let (len, element) = match value_type(function, base)? {
                Type::Array { element, len } => (len, element),
                Type::Reference { inner, .. } => match *inner {
                    Type::Array { element, len } => (len, element),
                    _ => return Err("element address base is not an array".into()),
                },
                _ => return Err("element address base is not an array".into()),
            };
            let (size, _) = array_layout(&element)?;
            let wide = matches!(
                value_type(function, index)?,
                Type::Primitive(Primitive::I64 | Primitive::U64)
            );
            // The unsigned comparison also rejects negative indices. The index
            // operand is read-only, so it is re-read for the address computation.
            emit_operand(body, function, param_count, index, layout, frame)?;
            if wide {
                body.instruction(&WasmInstruction::I64Const(i64::from(len)));
                body.instruction(&WasmInstruction::I64GeU);
            } else {
                body.instruction(&WasmInstruction::I32Const(len as i32));
                body.instruction(&WasmInstruction::I32GeU);
            }
            trap_if(body);
            emit_operand(body, function, param_count, base, layout, frame)?;
            emit_operand(body, function, param_count, index, layout, frame)?;
            if wide {
                body.instruction(&WasmInstruction::I32WrapI64);
            }
            body.instruction(&WasmInstruction::I32Const(size as i32));
            body.instruction(&WasmInstruction::I32Mul);
            body.instruction(&WasmInstruction::I32Add);
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::Borrow { owner, .. } => {
            if let Source::Local(local) = owner.source {
                if let Some(slot) = layout.slots.get(&local.0) {
                    emit_address(body, frame.ok_or("owner cell requires frame")?, slot.offset);
                } else {
                    emit_operand(body, function, param_count, owner, layout, frame)?;
                }
            } else {
                emit_operand(body, function, param_count, owner, layout, frame)?;
            }
            body.instruction(&WasmInstruction::LocalSet(
                output.ok_or("borrow lacks output")?,
            ));
        }
        InstructionKind::Load { reference } => {
            emit_operand(body, function, param_count, reference, layout, frame)?;
            emit_load(body, reference_primitive(function, reference)?);
            body.instruction(&WasmInstruction::LocalSet(
                output.ok_or("load lacks output")?,
            ));
        }
        InstructionKind::Store { reference, value } => {
            emit_operand(body, function, param_count, reference, layout, frame)?;
            emit_operand(body, function, param_count, value, layout, frame)?;
            if let Type::Reference { inner, .. } = value_type(function, reference)? {
                if matches!(inner.as_ref(), Type::Array { .. }) {
                    // Whole-array store through a share reference: the value
                    // operand is the address of an array cell of the same layout.
                    body.instruction(&WasmInstruction::I32Const(array_bytes(&inner)? as i32));
                    body.instruction(&WasmInstruction::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                    return Ok(());
                }
            }
            emit_store(body, reference_primitive(function, reference)?);
        }
        InstructionKind::Assign { target, value, .. } => {
            if let Some(cell) = layout.arrays.get(&Slot::Local(target.0)).copied() {
                return emit_array_copy(body, function, param_count, cell, value, layout, frame);
            }
            if let Some(slot) = layout.slots.get(&target.0) {
                emit_address(body, frame.ok_or("owner cell requires frame")?, slot.offset);
                emit_operand(body, function, param_count, value, layout, frame)?;
                emit_store(body, slot.ty);
            } else {
                emit_operand(body, function, param_count, value, layout, frame)?;
                body.instruction(&WasmInstruction::LocalSet(param_count + target.0));
            }
        }
        InstructionKind::Call { callee, arguments } => {
            let Source::Function(target) = callee.source else {
                return Err("indirect calls are unsupported".into());
            };
            for argument in arguments {
                emit_operand(body, function, param_count, argument, layout, frame)?;
            }
            let value = output.ok_or("call lacks an output")?;
            let id = instruction.output.unwrap();
            if matches!(function.values[id.0 as usize], Type::Array { .. }) {
                // Struct-return: the callee writes its result into this call's
                // own value cell in the caller's frame (never into a dead
                // callee frame), passed as the hidden trailing pointer.
                let cell = array_cell_of(layout, Slot::Value(id.0))?;
                emit_address(body, frame.ok_or("array cell requires frame")?, cell.offset);
                body.instruction(&WasmInstruction::Call(indices[&target.0]));
                return Ok(());
            }
            body.instruction(&WasmInstruction::Call(indices[&target.0]));
            // The Program's function table is available only to the caller; a
            // Unit call leaves no Wasm stack result and receives an internal zero.
            // Determine Unit from the value's recorded type.
            if matches!(
                function.values[id.0 as usize],
                Type::Primitive(Primitive::Unit)
            ) {
                body.instruction(&WasmInstruction::I32Const(0));
            }
            body.instruction(&WasmInstruction::LocalSet(value));
        }
        InstructionKind::Unary { op, operand } => {
            let output = output.ok_or("unary operation lacks an output")?;
            let ty = value_type(function, operand)?;
            refresh_operand(body, function, param_count, operand, layout, frame)?;
            emit_unary(
                body,
                *op,
                operand_local(function, param_count, operand)?,
                &ty,
                output,
            )?;
        }
        InstructionKind::Binary { op, left, right } => {
            let output = output.ok_or("binary operation lacks an output")?;
            let ty = value_type(function, left)?;
            refresh_operand(body, function, param_count, left, layout, frame)?;
            refresh_operand(body, function, param_count, right, layout, frame)?;
            emit_binary(
                body,
                *op,
                operand_local(function, param_count, left)?,
                operand_local(function, param_count, right)?,
                &ty,
                output,
                scratch64,
            )?;
        }
    }
    Ok(())
}

fn emit_constant(
    body: &mut wasm_encoder::Function,
    constant: &Constant,
    ty: Type,
) -> Result<(), String> {
    match (constant, ty) {
        (Constant::Unit, Type::Primitive(Primitive::Unit)) => {
            body.instruction(&WasmInstruction::I32Const(0));
        }
        (Constant::Bool(value), Type::Primitive(Primitive::Bool)) => {
            body.instruction(&WasmInstruction::I32Const(i32::from(*value)));
        }
        (Constant::Integer(text), Type::Primitive(kind)) => match kind {
            Primitive::I8 | Primitive::I16 | Primitive::I32 => {
                let value = text
                    .replace('_', "")
                    .parse::<i32>()
                    .map_err(|_| "invalid signed integer constant")?;
                if !integer_fits_signed(kind, value as i128) {
                    return Err(format!("integer constant does not fit {kind:?}"));
                }
                body.instruction(&WasmInstruction::I32Const(value));
            }
            Primitive::U8 | Primitive::U16 | Primitive::U32 => {
                let value = text
                    .replace('_', "")
                    .parse::<u32>()
                    .map_err(|_| "invalid unsigned integer constant")?;
                if !integer_fits_unsigned(kind, value as u128) {
                    return Err(format!("integer constant does not fit {kind:?}"));
                }
                body.instruction(&WasmInstruction::I32Const(value as i32));
            }
            Primitive::I64 => {
                let value = text
                    .replace('_', "")
                    .parse::<i64>()
                    .map_err(|_| "invalid signed integer constant")?;
                body.instruction(&WasmInstruction::I64Const(value));
            }
            Primitive::U64 => {
                let value = text
                    .replace('_', "")
                    .parse::<u64>()
                    .map_err(|_| "invalid unsigned integer constant")?;
                body.instruction(&WasmInstruction::I64Const(value as i64));
            }
            _ => return Err(format!("integer constant has non-integer type {kind:?}")),
        },
        (Constant::Float(text), Type::Primitive(Primitive::F32)) => {
            let value = text
                .replace('_', "")
                .parse::<f32>()
                .map_err(|_| "invalid f32 constant")?;
            body.instruction(&WasmInstruction::F32Const(value.into()));
        }
        (Constant::Float(text), Type::Primitive(Primitive::F64)) => {
            let value = text
                .replace('_', "")
                .parse::<f64>()
                .map_err(|_| "invalid f64 constant")?;
            body.instruction(&WasmInstruction::F64Const(value.into()));
        }
        _ => return Err("constant does not match its recorded primitive type".into()),
    }
    Ok(())
}

fn integer_fits_signed(kind: Primitive, value: i128) -> bool {
    match kind {
        Primitive::I8 => i8::try_from(value).is_ok(),
        Primitive::I16 => i16::try_from(value).is_ok(),
        Primitive::I32 => i32::try_from(value).is_ok(),
        _ => false,
    }
}

fn integer_fits_unsigned(kind: Primitive, value: u128) -> bool {
    match kind {
        Primitive::U8 => u8::try_from(value).is_ok(),
        Primitive::U16 => u16::try_from(value).is_ok(),
        Primitive::U32 => u32::try_from(value).is_ok(),
        _ => false,
    }
}

fn compile_terminator(
    body: &mut wasm_encoder::Function,
    terminator: &TerminatorKind,
    function: &Function,
    pc: u32,
    param_count: u32,
    frame: Option<FrameState>,
    layout: &FrameLayout,
) -> Result<(), String> {
    match terminator {
        TerminatorKind::Goto(edge) => {
            emit_edge(
                body,
                function,
                edge.target,
                &edge.arguments,
                pc,
                param_count,
                layout,
                frame,
            )?;
            body.instruction(&WasmInstruction::Br(1));
        }
        TerminatorKind::Branch {
            condition,
            then_edge,
            else_edge,
        } => {
            emit_operand(body, function, param_count, condition, layout, frame)?;
            body.instruction(&WasmInstruction::If(BlockType::Empty));
            emit_edge(
                body,
                function,
                then_edge.target,
                &then_edge.arguments,
                pc,
                param_count,
                layout,
                frame,
            )?;
            body.instruction(&WasmInstruction::Br(2));
            body.instruction(&WasmInstruction::Else);
            emit_edge(
                body,
                function,
                else_edge.target,
                &else_edge.arguments,
                pc,
                param_count,
                layout,
                frame,
            )?;
            body.instruction(&WasmInstruction::Br(2));
            body.instruction(&WasmInstruction::End);
        }
        TerminatorKind::Return(value) => {
            if let Some(value) = value {
                let ty = value_type(function, value)?;
                if matches!(ty, Type::Array { .. }) {
                    // Write the result through the hidden pointer parameter
                    // (the last Wasm parameter) before the frame is released.
                    body.instruction(&WasmInstruction::LocalGet(param_count - 1));
                    emit_operand(body, function, param_count, value, layout, frame)?;
                    body.instruction(&WasmInstruction::I32Const(array_bytes(&ty)? as i32));
                    body.instruction(&WasmInstruction::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                } else if ty != Type::Primitive(Primitive::Unit) {
                    emit_operand(body, function, param_count, value, layout, frame)?;
                }
            }
            if let Some(frame) = frame {
                frame.restore(body);
            }
            body.instruction(&WasmInstruction::Return);
        }
        TerminatorKind::Unreachable => {
            body.instruction(&WasmInstruction::Unreachable);
        }
    };
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_edge(
    body: &mut wasm_encoder::Function,
    function: &Function,
    target: BlockId,
    arguments: &[Operand],
    pc: u32,
    param_count: u32,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    let parameters = &function.blocks[target.0 as usize].parameters;
    // Stage every argument on the operand stack before assigning any target
    // parameter. This gives block edges parallel-copy semantics, including
    // swaps and loop backedges.
    // Array parameters live in frame cells: their arguments are copied in
    // memory after the scalars are staged, so they take no stack slot.
    let is_array = |parameter: &memobits_ir::ValueId| {
        matches!(function.values[parameter.0 as usize], Type::Array { .. })
    };
    for (argument, parameter) in arguments.iter().zip(parameters) {
        if !is_array(parameter) {
            emit_operand(body, function, param_count, argument, layout, frame)?;
        }
    }
    for (argument, parameter) in arguments.iter().zip(parameters) {
        if is_array(parameter) {
            let cell = array_cell_of(layout, Slot::Value(parameter.0))?;
            emit_array_copy(body, function, param_count, cell, argument, layout, frame)?;
        }
    }
    for parameter in parameters.iter().rev() {
        if !is_array(parameter) {
            body.instruction(&WasmInstruction::LocalSet(value_local(
                function,
                param_count,
                *parameter,
            )));
        }
    }
    body.instruction(&WasmInstruction::I32Const(target.0 as i32));
    body.instruction(&WasmInstruction::LocalSet(pc));
    Ok(())
}

#[cfg(test)]
mod frame_layout_tests {
    use super::*;
    use memobits_ir::{Block, CanonicalFunction, LoanId, Local, Signature};

    fn fixture(local_types: Vec<Type>, owners: Vec<Source>) -> Function {
        let span = Span {
            source: memobits_diagnostics::SourceId(7),
            start: 3,
            end: 8,
        };
        let locals = local_types
            .iter()
            .enumerate()
            .map(|(index, ty)| Local {
                name: format!("owner_{index}"),
                ty: ty.clone(),
                mutable: true,
                span,
            })
            .collect::<Vec<_>>();
        let mut values = Vec::new();
        let instructions = owners
            .into_iter()
            .enumerate()
            .map(|(index, source)| {
                let inner = match source {
                    Source::Local(local) => local_types
                        .get(local.0 as usize)
                        .cloned()
                        .unwrap_or(Type::Primitive(Primitive::I32)),
                    _ => Type::Primitive(Primitive::I32),
                };
                values.push(Type::Reference {
                    access: memobits_ir::Access::Borrow,
                    inner: Box::new(inner),
                });
                Instruction {
                    span: Some(span),
                    output: Some(memobits_ir::ValueId(index as u32)),
                    kind: InstructionKind::Borrow {
                        loan: LoanId(index as u32),
                        owner: Operand {
                            source,
                            mode: memobits_ir::UseMode::Borrow,
                            span: Some(span),
                        },
                        access: memobits_ir::Access::Borrow,
                    },
                }
            })
            .collect();
        Function {
            path: CanonicalFunction {
                package: "fixture".into(),
                module: vec!["layout".into()],
                name: "test".into(),
            },
            span,
            signature: Signature {
                parameters: vec![],
                result: Box::new(Type::Primitive(Primitive::Unit)),
            },
            parameter_locals: vec![],
            locals,
            values,
            blocks: vec![Block {
                parameters: vec![],
                instructions,
                terminator: memobits_ir::Terminator {
                    span: Some(span),
                    kind: TerminatorKind::Return(None),
                },
            }],
            entry: BlockId(0),
        }
    }

    #[test]
    fn cells_are_collected_once_and_aligned_by_local_identity() {
        let types = [
            Primitive::I8,
            Primitive::I16,
            Primitive::I32,
            Primitive::I64,
            Primitive::F32,
            Primitive::F64,
        ]
        .into_iter()
        .map(Type::Primitive)
        .collect();
        let owners = vec![
            Source::Local(LocalId(5)),
            Source::Local(LocalId(0)),
            Source::Local(LocalId(3)),
            Source::Local(LocalId(2)),
            Source::Local(LocalId(4)),
            Source::Local(LocalId(1)),
            Source::Local(LocalId(0)),
        ];
        let function = fixture(types, owners);
        let layout = FrameLayout::for_function(&function).unwrap();
        let expected = [
            (0, 0, 1),
            (1, 2, 2),
            (2, 4, 4),
            (3, 8, 8),
            (4, 16, 4),
            (5, 24, 8),
        ];
        assert_eq!(layout.slots.len(), expected.len());
        for (local, offset, size) in expected {
            let slot = layout.slots.get(&local).unwrap();
            assert_eq!((slot.offset, slot.size), (offset, size));
            assert_eq!(slot.offset % slot.align, 0);
        }
        assert_eq!(layout.size, 32);
        let mut ends = layout
            .slots
            .values()
            .map(|slot| slot.offset..slot.offset + slot.size)
            .collect::<Vec<_>>();
        ends.sort_by_key(|range| range.start);
        assert!(ends.windows(2).all(|pair| pair[0].end <= pair[1].start));
        assert!(ends.iter().all(|range| range.end <= layout.size));

        let rebuilt = FrameLayout::for_function(&fixture(
            function
                .locals
                .iter()
                .map(|local| local.ty.clone())
                .collect(),
            vec![
                Source::Local(LocalId(0)),
                Source::Local(LocalId(1)),
                Source::Local(LocalId(2)),
                Source::Local(LocalId(3)),
                Source::Local(LocalId(4)),
                Source::Local(LocalId(5)),
            ],
        ))
        .unwrap();
        assert_eq!(layout, rebuilt);
    }

    #[test]
    fn no_owner_borrows_need_no_frame_and_alignment_is_checked() {
        let function = fixture(vec![Type::Primitive(Primitive::I32)], vec![]);
        assert_eq!(FrameLayout::for_function(&function).unwrap().size, 0);
        assert_eq!(align_up(0, 8), Some(0));
        assert_eq!(align_up(9, 8), Some(16));
        assert_eq!(align_up(u32::MAX, 8), None);
    }

    fn reference(access: memobits_ir::Access, inner: Type) -> Type {
        Type::Reference {
            access,
            inner: Box::new(inner),
        }
    }

    #[test]
    fn reference_handles_reuse_addresses_and_owners_remain_deterministic() {
        use memobits_ir::{Access, ValueId};
        let types = vec![
            Type::Primitive(Primitive::I8),
            reference(Access::Borrow, Type::Primitive(Primitive::I32)),
            Type::Primitive(Primitive::I64),
        ];
        let mut function = fixture(
            types.clone(),
            vec![
                Source::Local(LocalId(2)),
                Source::Local(LocalId(1)),
                Source::Value(ValueId(0)),
                Source::Local(LocalId(0)),
            ],
        );
        function.values[0] = reference(Access::Share, Type::Primitive(Primitive::I16));
        let layout = FrameLayout::for_function(&function).unwrap();
        assert_eq!(
            layout,
            FrameLayout::for_function(&fixture(
                types,
                vec![Source::Local(LocalId(0)), Source::Local(LocalId(2))]
            ))
            .unwrap()
        );
        assert_eq!(layout.slots[&2].offset, 8);
        assert_eq!(layout.size, 16);
    }

    #[test]
    fn unsupported_roots_and_invalid_ids_are_rejected_with_spans() {
        use memobits_ir::{Access, ValueId};
        let primitive = Type::Primitive(Primitive::I32);
        let cases = [
            (
                primitive.clone(),
                Source::Value(ValueId(0)),
                "primitive temporary",
            ),
            (
                primitive.clone(),
                Source::Value(ValueId(99)),
                "out of range",
            ),
            (
                primitive.clone(),
                Source::Local(LocalId(99)),
                "out of range",
            ),
            (
                primitive.clone(),
                Source::Function(FunctionId(0)),
                "function",
            ),
            (
                Type::Primitive(Primitive::Unit),
                Source::Local(LocalId(0)),
                "Unit",
            ),
            (
                reference(Access::Owned, primitive.clone()),
                Source::Local(LocalId(0)),
                "Owned",
            ),
            (
                reference(Access::Borrow, reference(Access::Borrow, primitive)),
                Source::Local(LocalId(0)),
                "nested",
            ),
        ];
        for (ty, source, message) in cases {
            let mut function = fixture(vec![ty.clone()], vec![source]);
            function.values[0] = ty;
            let error = FrameLayout::for_function(&function).unwrap_err();
            assert!(error.message.contains(message), "{error:?}");
            assert_eq!(error.span, Some(function.span));
        }
    }

    #[test]
    fn source_call_reborrows_need_only_owner_cells() {
        let source = "fn read(x: borrow i32) -> i32 { x + 0 } fn relay(x: borrow i32) -> i32 { read(x) } fn main() -> i32 { let x := 1; let r := x.borrow(); read(r) + read(x.borrow()) }";
        let parsed = memobits_syntax::parse(memobits_diagnostics::SourceId(0), source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let program =
            memobits_analysis::lower_module(&parsed.module, "test", &["main".into()]).unwrap();
        assert!(memobits_ownership::check_ownership(&program).is_empty());
        let mut saw_local_reborrow = false;
        let mut saw_value_reborrow = false;
        for function in &program.functions {
            let layout = FrameLayout::for_function(function).unwrap();
            if function.path.name == "main" {
                assert_eq!(layout.slots.len(), 1);
                assert_eq!(layout.size, 16);
            } else {
                assert!(layout.slots.is_empty());
                assert_eq!(layout.size, 0);
            }
            for instruction in function.blocks.iter().flat_map(|block| &block.instructions) {
                if let InstructionKind::Borrow { owner, .. } = &instruction.kind {
                    match owner.source {
                        Source::Local(local)
                            if matches!(
                                function.locals[local.0 as usize].ty,
                                Type::Reference { .. }
                            ) =>
                        {
                            saw_local_reborrow = true
                        }
                        Source::Value(value)
                            if matches!(
                                function.values[value.0 as usize],
                                Type::Reference { .. }
                            ) =>
                        {
                            saw_value_reborrow = true
                        }
                        _ => {}
                    }
                }
            }
        }
        assert!(saw_local_reborrow);
        assert!(saw_value_reborrow);
        assert!(compile(&program, &BTreeMap::new()).is_ok());
    }
}

#[cfg(test)]
mod activation_tests {
    use super::*;
    use wasmi::{Engine, Linker, Module, Store};

    fn lower(source: &str) -> Program {
        let parsed = memobits_syntax::parse(memobits_diagnostics::SourceId(0), source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        memobits_analysis::lower_module(&parsed.module, "test", &["main".into()]).unwrap()
    }

    fn instance(bytes: &[u8]) -> (Store<()>, wasmi::Instance) {
        wasmparser::validate(bytes).unwrap();
        let engine = Engine::default();
        let module = Module::new(&engine, bytes).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = Linker::new(&engine)
            .instantiate_and_start(&mut store, &module)
            .unwrap();
        (store, instance)
    }

    fn sp(store: &Store<()>, instance: wasmi::Instance) -> i32 {
        instance
            .get_global(store, "__test_sp")
            .unwrap()
            .get(store)
            .i32()
            .unwrap()
    }

    #[test]
    fn nested_recursive_and_early_returns_restore_each_activation() {
        let program = lower("fn recurse(n: i32) -> i32 { if n == 0 { return 42; } recurse(n - 1) } fn main() -> i32 { recurse(3) }");
        let exports = BTreeMap::from([("main".into(), FunctionId(1))]);
        let wasm = encode_with_frame_sizes(&program, &exports, &[16, 32]).unwrap();
        let (mut store, instance) = instance(&wasm);
        let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
        for _ in 0..20 {
            assert_eq!(main.call(&mut store, ()).unwrap(), 42);
            assert_eq!(sp(&store, instance), FRAME_START as i32);
        }
        let memory = instance.get_memory(&store, "__test_memory").unwrap();
        let data = memory.data(&store);
        // Main and each recursive invocation retain separate base addresses.
        for base in [16usize, 48, 64, 80, 96] {
            assert_eq!(
                u32::from_le_bytes(data[base..base + 4].try_into().unwrap()),
                base as u32
            );
        }
    }

    #[test]
    fn exhaustion_traps_before_mutation_and_oversized_frames_do_not_wrap() {
        let program =
            lower("fn recurse(n: i32) -> i32 { if n == 0 { 7 } else { recurse(n - 1) } }");
        let exports = BTreeMap::from([("recurse".into(), FunctionId(0))]);
        let wasm = encode_with_frame_sizes(&program, &exports, &[32752]).unwrap();
        let (mut store, instance) = instance(&wasm);
        let recurse = instance
            .get_typed_func::<i32, i32>(&store, "recurse")
            .unwrap();
        assert_eq!(recurse.call(&mut store, 1).unwrap(), 7);
        assert_eq!(sp(&store, instance), 16);
        assert!(recurse.call(&mut store, 2).is_err());
        // Two active frames remain after a trap; failed third entry changed nothing.
        assert_eq!(sp(&store, instance), 65520);
        for size in [65536, u32::MAX] {
            let bytes = encode_with_frame_sizes(&program, &exports, &[size]).unwrap();
            let (mut store, instance) = self::instance(&bytes);
            let recurse = instance
                .get_typed_func::<i32, i32>(&store, "recurse")
                .unwrap();
            assert!(recurse.call(&mut store, 0).is_err());
            assert_eq!(sp(&store, instance), 16);
        }
    }

    #[test]
    fn unit_returns_restore_and_unselected_frames_emit_no_stack() {
        let program = lower("fn helper() { return; } fn main() { helper() }");
        let exports = BTreeMap::from([("main".into(), FunctionId(1))]);
        let bytes = encode_with_frame_sizes(&program, &exports, &[16, 16]).unwrap();
        let (mut store, instance) = instance(&bytes);
        let main = instance.get_typed_func::<(), ()>(&store, "main").unwrap();
        for _ in 0..3 {
            main.call(&mut store, ()).unwrap();
            assert_eq!(sp(&store, instance), 16);
        }
        let no_roots = encode_with_frame_sizes(&program, &BTreeMap::new(), &[16, 16]).unwrap();
        assert!(!wasmparser::Parser::new(0)
            .parse_all(&no_roots)
            .any(|part| matches!(
                part.unwrap(),
                wasmparser::Payload::MemorySection(_) | wasmparser::Payload::GlobalSection(_)
            )));
    }

    #[test]
    fn zero_frame_output_is_identical_and_private_stack_is_unexported() {
        let program = lower("fn main() -> i32 { 42 }");
        let exports = BTreeMap::from([("main".into(), FunctionId(0))]);
        let normal = compile(&program, &exports).unwrap();
        assert_eq!(
            normal,
            encode_with_frame_sizes(&program, &exports, &[0]).unwrap()
        );
        assert!(!wasmparser::Parser::new(0)
            .parse_all(&normal)
            .any(|part| matches!(
                part.unwrap(),
                wasmparser::Payload::MemorySection(_) | wasmparser::Payload::GlobalSection(_)
            )));
        let private = encode_frames(&program, &exports, &[16], false).unwrap();
        let (store, instance) = instance(&private);
        assert!(instance.get_memory(&store, "__test_memory").is_none());
        assert!(instance.get_global(&store, "__test_sp").is_none());
    }
}

#[cfg(test)]
mod struct_layout_tests {
    use super::*;
    use wasmi::{Engine, Linker, Module, Store};

    const MIXED: &str = "type M { a: u8, b: i64, c: Bool, d: f32, e: i16 } \
        fn main() -> i32 { let m := M { e: -7, a: 200, d: 1.5, c: true, b: 5000000000 }; 1 }";

    fn lower(source: &str) -> Program {
        let parsed = memobits_syntax::parse(memobits_diagnostics::SourceId(0), source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        memobits_analysis::lower_module(&parsed.module, "test", &["main".into()]).unwrap()
    }

    #[test]
    fn fields_use_natural_alignment_in_declaration_order() {
        let program = lower(MIXED);
        let layouts = struct_layouts(&program.types).unwrap();
        assert_eq!(layouts.len(), 1);
        // a: u8 @0, b: i64 @8, c: Bool @16, d: f32 @20, e: i16 @24; size 32, align 8.
        assert_eq!(layouts[0].offsets, [0, 8, 16, 20, 24]);
        assert_eq!(layouts[0].size, 32);
        assert_eq!(layouts[0].align, 8);
        let small = lower("type S { a: u8, b: u16, c: u8 } fn main() {}");
        let layouts = struct_layouts(&small.types).unwrap();
        assert_eq!(layouts[0].offsets, [0, 2, 4]);
        assert_eq!(layouts[0].size, 6);
        assert_eq!(layouts[0].align, 2);
        let empty = lower("type U {} fn main() {}");
        let layouts = struct_layouts(&empty.types).unwrap();
        assert_eq!((layouts[0].size, layouts[0].align), (0, 1));
    }

    #[test]
    fn construction_writes_each_field_at_its_offset() {
        let program = lower(MIXED);
        let exports = BTreeMap::from([("main".to_string(), FunctionId(0))]);
        let structs = struct_layouts(&program.types).unwrap();
        let sizes = vec![
            FrameLayout::for_function_in(&structs, &program.functions[0])
                .unwrap()
                .size,
        ];
        let wasm = encode_with_frame_sizes(&program, &exports, &sizes).unwrap();
        wasmparser::validate(&wasm).unwrap();
        let engine = Engine::default();
        let module = Module::new(&engine, &wasm[..]).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = Linker::new(&engine)
            .instantiate_and_start(&mut store, &module)
            .unwrap();
        instance
            .get_typed_func::<(), i32>(&store, "main")
            .unwrap()
            .call(&mut store, ())
            .unwrap();
        let memory = instance.get_memory(&store, "__test_memory").unwrap();
        let bytes = &memory.data(&store)[FRAME_START as usize..FRAME_START as usize + 32];
        assert_eq!(bytes[0], 200);
        assert_eq!(
            i64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            5_000_000_000
        );
        assert_eq!(bytes[16], 1);
        assert_eq!(f32::from_le_bytes(bytes[20..24].try_into().unwrap()), 1.5);
        assert_eq!(i16::from_le_bytes(bytes[24..26].try_into().unwrap()), -7);
        // Padding is untouched (still zero-initialised memory).
        assert!(bytes[1..8].iter().all(|&b| b == 0));
        assert!(bytes[17..20].iter().all(|&b| b == 0));
        assert!(bytes[26..32].iter().all(|&b| b == 0));
    }
}
