//! Experimental WebAssembly backend for the validated primitive IR subset.
//!
//! The current output ABI maps `Bool`, 8-bit, and 16-bit values to `i32`,
//! `i32`/`u32` to Wasm `i32`, 64-bit integers to Wasm `i64`, and floats to
//! their Wasm float type. `Unit` has no exported result and is represented by
//! an internal zero-valued `i32` when an IR value is needed. These choices are
//! experimental and do not define a stable Memobits ABI.
use memobits_diagnostics::{Category, Diagnostic, DiagnosticCode, Severity, Span};
use memobits_entry_abi as entry_abi;
use memobits_ir::{
    ArrayInit, BinaryOp, BlockId, Constant, EntryOutcome, ErrorAncestry, Function, FunctionId,
    Instruction, InstructionKind, LocalId, Operand, Primitive, Program, Source, TerminatorKind,
    Type, TypeDef, TypeDefKind, UnaryOp, ValueId,
};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, CustomSection, DataSection, ExportKind, ExportSection,
    Function as WasmFunction, FunctionSection, GlobalSection, GlobalType,
    Instruction as WasmInstruction, MemArg, MemorySection, MemoryType, Module, TypeSection,
    ValType,
};

mod list_descriptor;
mod memory;
mod string_descriptor;
mod string_heap;
mod utf8;
use memory::{LayoutError, StaticLayout};

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
/// Internal direct calls support borrow/share references to non-Unit primitives,
/// to (nested) fixed arrays of them and to structs. Error references can be
/// passed to parameters of a nominal ancestor at the same address. Calls also
/// support owned array and struct parameters (copied into the callee's frame)
/// and array and struct results (written through a hidden pointer to
/// caller-allocated storage). Exported
/// signatures remain primitive-only; reference, array and struct ABIs are not
/// defined. Indirect calls, reference results and other
/// pointees are rejected.
/// Integer arithmetic and array indexing are checked in every profile. A failed
/// check records its reason and source location in the exported `__mb_trap`
/// global (see [`TrapReason`]) and then traps with Wasm `unreachable`, so the
/// host runtime can report a language-level runtime error.
pub fn compile(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
) -> Result<Vec<u8>, Vec<Diagnostic>> {
    compile_with(program, exports, &CompileOptions::default())
}

/// Default stack size in bytes (1 MiB), matching `[build].stack_size`.
pub const DEFAULT_STACK_SIZE: u32 = 1024 * 1024;

/// Reserved low addresses: address zero stays unused and the stack begins at
/// this offset.
pub const RESERVED_BYTES: u32 = 16;

/// Backend settings. The experimental ABI is not stable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompileOptions {
    /// Stack size in bytes; a non-zero multiple of 16 that fits a 32-bit memory.
    pub stack_size: u32,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            stack_size: DEFAULT_STACK_SIZE,
        }
    }
}

/// First address after the stack. An outcome entry places its return cell
/// here. `None` when the layout does not fit 32-bit memory.
pub fn static_data_start(stack_size: u32) -> Option<u32> {
    align_up(RESERVED_BYTES.checked_add(stack_size)?, 16)
}

/// Like [`compile`], with explicit backend settings.
pub fn compile_with(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    options: &CompileOptions,
) -> Result<Vec<u8>, Vec<Diagnostic>> {
    compile_traced(program, exports, options).map(|compiled| compiled.bytes)
}

/// A compiled module together with the source spans of its trap sites.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compiled {
    pub bytes: Vec<u8>,
    /// `trap_sites[i]` is the span of location id `i + 1` as stored in the
    /// `__mb_trap` global. The caller owns source text, so it maps spans to
    /// file, line and column and may embed the result in a custom section named
    /// [`TRAP_SECTION`].
    pub trap_sites: Vec<Span>,
}

/// Like [`compile_with`], also returning the trap-site spans.
pub fn compile_traced(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    options: &CompileOptions,
) -> Result<Compiled, Vec<Diagnostic>> {
    compile_target(program, exports, options, false)
}

/// Compile the project's application entry. A supported outcome result uses
/// the private versioned runner adapter; library exports are scalar-only.
pub fn compile_application_traced(
    program: &Program,
    entry: FunctionId,
    options: &CompileOptions,
) -> Result<Compiled, Vec<Diagnostic>> {
    let exports = BTreeMap::from([(entry_abi::ENTRY_EXPORT.into(), entry)]);
    compile_target(program, &exports, options, true)
}

fn compile_target(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    options: &CompileOptions,
    application: bool,
) -> Result<Compiled, Vec<Diagnostic>> {
    let stack_size = options.stack_size;
    let Some(static_layout) = StaticLayout::new(stack_size) else {
        return Err(vec![diagnostic(
            format!(
                "invalid stack size {stack_size}: it must be a non-zero multiple of 16 bytes that fits a 32-bit memory"
            ),
            None,
        )]);
    };
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
    let mut entry = None;
    for id in exports.values() {
        if let Some(function) = program.functions.get(id.0 as usize) {
            if function
                .signature
                .parameters
                .iter()
                .any(|p| p.ty == Type::String)
                || *function.signature.result == Type::String
            {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot use String; the external String ABI is not defined",
                    Some(function.span),
                ));
                continue;
            }
            if function
                .signature
                .parameters
                .iter()
                .any(|parameter| matches!(parameter.ty, Type::List(_)))
                || matches!(function.signature.result.as_ref(), Type::List(_))
            {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot use List; the external List ABI is not defined",
                    Some(function.span),
                ));
                continue;
            }
            if application {
                match outcome_entry(program, function, &structs, static_layout) {
                    Ok(Some(adapter)) => {
                        entry = Some(adapter);
                        continue;
                    }
                    Ok(None) => {}
                    Err(message) => {
                        errors.push(diagnostic(message, Some(function.span)));
                        continue;
                    }
                }
            }
            if function
                .signature
                .parameters
                .iter()
                .any(|p| matches!(p.ty, Type::Struct(_)))
            {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot take structs or struct references; the external struct ABI is not defined",
                    Some(function.span),
                ));
            } else if function
                .signature
                .parameters
                .iter()
                .any(|p| matches!(p.ty, Type::Enum(_)))
            {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot take enums or enum references; the external enum ABI is not defined",
                    Some(function.span),
                ));
            } else if matches!(function.signature.result.as_ref(), Type::Enum(_)) {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot return enums; the external enum ABI is not defined",
                    Some(function.span),
                ));
            } else if matches!(function.signature.result.as_ref(), Type::Struct(_)) {
                errors.push(diagnostic(
                    "Wasm exported signatures cannot return structs; the external struct ABI is not defined",
                    Some(function.span),
                ));
            } else if function
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
        if let Err(error) = FrameLayout::for_function_in(&structs, function, stack_size) {
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

    encode(program, exports, stack_size, entry)
        .map(|(bytes, trap_sites)| Compiled { bytes, trap_sites })
        .map_err(|message| vec![diagnostic(message, None)])
}

fn unsupported_instruction(instruction: &Instruction) -> Option<String> {
    match &instruction.kind {
        InstructionKind::Constant(_)
        | InstructionKind::EndStringLocal { .. }
        | InstructionKind::Capture(_)
        | InstructionKind::Copy { .. }
        | InstructionKind::StringLen { .. }
        | InstructionKind::ListGet { .. }
        | InstructionKind::ListLen { .. }
        | InstructionKind::ListPush { .. }
        | InstructionKind::EndListLocal { .. }
        | InstructionKind::EmptyList
        | InstructionKind::InitConcatString { .. }
        | InstructionKind::StringIsCharBoundary { .. }
        | InstructionKind::StringByteAt { .. }
        | InstructionKind::StringScalarAt { .. }
        | InstructionKind::ValidateUtf8 { .. }
        | InstructionKind::Assign { .. } => None,
        InstructionKind::Borrow { .. }
        | InstructionKind::Load { .. }
        | InstructionKind::Store { .. } => None,
        InstructionKind::ArrayNew { .. } | InstructionKind::ElementAddr { .. } => None,
        InstructionKind::StructNew { .. }
        | InstructionKind::EnumNew { .. }
        | InstructionKind::FieldAddr { .. }
        | InstructionKind::VariantAddr { .. }
        | InstructionKind::Extract { .. }
        | InstructionKind::EnumTag { .. }
        | InstructionKind::VariantExtract { .. } => None,
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
        memobits_ir::Access::Owned => {
            matches!(
                p.ty,
                Type::Primitive(_)
                    | Type::String
                    | Type::List(_)
                    | Type::Array { .. }
                    | Type::Struct(_)
                    | Type::Enum(_)
            )
        }
        memobits_ir::Access::Borrow | memobits_ir::Access::Share => {
            matches!(p.ty, Type::List(_))
                || matches!(p.ty, Type::Primitive(kind) if kind != Primitive::Unit)
                || matches!(
                    p.ty,
                    Type::String | Type::Array { .. } | Type::Struct(_) | Type::Enum(_)
                )
        }
    }) && matches!(
        result,
        Type::Primitive(_)
            | Type::String
            | Type::List(_)
            | Type::Array { .. }
            | Type::Struct(_)
            | Type::Enum(_)
    )
}

fn supported_type(ty: &Type) -> bool {
    match ty {
        Type::Primitive(_) => true,
        // A struct or enum is an inline frame-cell value, passed internally by address.
        Type::String | Type::List(_) | Type::Struct(_) | Type::Enum(_) => true,
        Type::Reference {
            access: memobits_ir::Access::Borrow | memobits_ir::Access::Share,
            inner,
        } if matches!(inner.as_ref(), Type::List(_)) => true,
        Type::Reference {
            access: memobits_ir::Access::Borrow | memobits_ir::Access::Share,
            inner,
        } => match inner.as_ref() {
            Type::Primitive(kind) => *kind != Primitive::Unit,
            array @ Type::Array { .. } => supported_type(array),
            Type::String | Type::Struct(_) | Type::Enum(_) => true,
            _ => false,
        },
        Type::Array { element, .. } => match element.as_ref() {
            Type::Primitive(kind) => *kind != Primitive::Unit,
            nested @ Type::Array { .. } => supported_type(nested),
            Type::Struct(_) | Type::Enum(_) => true,
            _ => false,
        },
        _ => false,
    }
}

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

/// How one struct field is stored: a primitive written with a typed store, or a
/// nested array or struct copied as `size` bytes from its value cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FieldStorage {
    Primitive(Primitive),
    Aggregate(u32),
}

/// Natural-alignment layout of a struct or enum. A struct lays its fields out
/// in declaration order, each at the next offset aligned to its own alignment,
/// total size rounded up to the largest field alignment. An enum (`variants` is
/// `Some`) stores its tag at offset 0 and every variant's payload in one shared
/// area; `offsets` and `fields` are empty for it. A nested aggregate is laid
/// out inline with its own size and alignment (the validator rejects by-value
/// cycles).
#[derive(Clone, Debug, PartialEq, Eq)]
struct StructLayout {
    size: u32,
    align: u32,
    offsets: Vec<u32>,
    fields: Vec<FieldStorage>,
    enum_layout: Option<EnumLayout>,
    error_identity: Option<u32>,
}

/// Enum layout: the tag at offset 0 with the smallest unsigned width that holds
/// the variant count (1 byte up to 256 variants, 2 up to 65536, else 4), then
/// the payload area, aligned to the largest payload alignment of any variant.
/// Each variant places its payload fields from the start of that area, so the
/// size is the largest variant extent, rounded up to the enum's alignment. The
/// layout is internal, not a stable ABI, and bytes beyond the active variant's
/// payload are unspecified.
#[derive(Clone, Debug, PartialEq, Eq)]
struct EnumLayout {
    tag_size: u32,
    string_success: bool,
    variants: Vec<VariantLayout>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VariantLayout {
    offsets: Vec<u32>,
    fields: Vec<FieldStorage>,
}

const STRUCT_LAYOUT_OVERFLOW: &str = "struct layout overflows the 32-bit address space";

fn struct_layouts(types: &[TypeDef]) -> Result<Vec<StructLayout>, String> {
    let mut done: Vec<Option<StructLayout>> = vec![None; types.len()];
    for index in 0..types.len() {
        struct_layout_at(types, index, &mut done, &mut Vec::new())?;
    }
    Ok(done
        .into_iter()
        .map(|layout| layout.expect("laid out"))
        .collect())
}

/// Size, alignment and storage kind of one field or payload value.
fn member_layout(
    types: &[TypeDef],
    ty: &Type,
    done: &mut Vec<Option<StructLayout>>,
    active: &mut Vec<usize>,
) -> Result<Option<(u32, u32, FieldStorage)>, String> {
    Ok(match ty {
        Type::Primitive(kind) => {
            let (size, align) = storage_layout(*kind)?;
            Some((size, align, FieldStorage::Primitive(*kind)))
        }
        Type::Reference { inner, .. } if **inner == Type::String => {
            return Err("Wasm does not yet support String fields or enum payloads".into());
        }
        // Validated local borrow Option payloads store a Wasm address.
        Type::Reference { .. } => Some((4, 4, FieldStorage::Primitive(Primitive::U32))),
        Type::String => {
            return Err("Wasm does not yet support String fields or enum payloads".into())
        }
        nested @ (Type::Array { .. } | Type::Struct(_) | Type::Enum(_)) => {
            nested_struct_layouts(types, nested, done, active)?;
            let layout_at = |id: u32| done.get(id as usize).and_then(Option::as_ref);
            if matches!(nested, Type::Enum(id) if layout_at(id.0).is_some_and(has_string_success)) {
                return Err("Wasm does not yet support nested Result<String, E> storage".into());
            }
            let (size, align) = type_layout(&layout_at, nested)?;
            Some((size, align, FieldStorage::Aggregate(size)))
        }
        _ => None,
    })
}

fn struct_layout_at(
    types: &[TypeDef],
    index: usize,
    done: &mut Vec<Option<StructLayout>>,
    active: &mut Vec<usize>,
) -> Result<(), String> {
    if done[index].is_some() {
        return Ok(());
    }
    let definition = &types[index];
    if active.contains(&index) {
        let what = match definition.kind {
            TypeDefKind::Struct { .. } => "struct",
            TypeDefKind::Enum { .. } => "enum",
        };
        return Err(format!(
            "{what} '{}' contains itself by value",
            definition.path.name
        ));
    }
    active.push(index);
    let layout = match &definition.kind {
        TypeDefKind::Struct { fields } => {
            let mut offset = if definition.error_ancestry == Some(ErrorAncestry::Root) {
                entry_abi::ERROR_ID_BYTES
            } else {
                0
            };
            let mut align = 1u32;
            let mut offsets = Vec::with_capacity(fields.len());
            let mut storage = Vec::with_capacity(fields.len());
            if let Some(ErrorAncestry::Derived(parent)) = definition.error_ancestry {
                let parent = parent.0 as usize;
                struct_layout_at(types, parent, done, active)?;
                let base = done[parent].as_ref().expect("laid out parent");
                // Whole stores through a Share of the ancestor copy its padded size.
                // Reserve that entire prefix before placing any descendant fields.
                offset = base.size;
                align = base.align;
                offsets.extend_from_slice(&base.offsets);
                storage.extend_from_slice(&base.fields);
            }
            for field in &fields[offsets.len()..] {
                let Some((size, field_align, kind)) =
                    member_layout(types, &field.ty, done, active)?
                else {
                    return Err(format!(
                        "field '{}' of struct '{}' has an unsupported type",
                        field.name, definition.path.name
                    ));
                };
                offset = align_up(offset, field_align).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                offsets.push(offset);
                storage.push(kind);
                offset = offset.checked_add(size).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                align = align.max(field_align);
            }
            StructLayout {
                size: align_up(offset, align).ok_or(STRUCT_LAYOUT_OVERFLOW)?,
                align,
                offsets,
                fields: storage,
                enum_layout: None,
                error_identity: definition.error_ancestry.map(|_| index as u32 + 1),
            }
        }
        TypeDefKind::Enum { variants } => {
            let tag_size = match variants.len() {
                0..=256 => 1u32,
                257..=65536 => 2,
                _ => 4,
            };
            let string_success = definition.entry_outcome == Some(EntryOutcome::Result)
                && variants
                    .first()
                    .is_some_and(|variant| variant.payload == [Type::String]);
            // First pass: member sizes, so the payload area's alignment is known.
            let mut sized: Vec<Vec<(u32, u32, FieldStorage)>> = Vec::with_capacity(variants.len());
            let mut payload_align = 1u32;
            for (index, variant) in variants.iter().enumerate() {
                let mut members = Vec::with_capacity(variant.payload.len());
                for ty in &variant.payload {
                    let member = if string_success && index == 0 {
                        Some((
                            string_descriptor::SIZE,
                            string_descriptor::ALIGN,
                            FieldStorage::Aggregate(string_descriptor::SIZE),
                        ))
                    } else {
                        member_layout(types, ty, done, active)?
                    };
                    let Some(member) = member else {
                        return Err(format!(
                            "payload of variant '{}' of enum '{}' has an unsupported type",
                            variant.name, definition.path.name
                        ));
                    };
                    payload_align = payload_align.max(member.1);
                    members.push(member);
                }
                sized.push(members);
            }
            let payload_start = align_up(tag_size, payload_align).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
            let align = payload_align.max(tag_size);
            let mut extent = tag_size;
            let mut laid_out = Vec::with_capacity(sized.len());
            for members in sized {
                let mut cursor = payload_start;
                let mut offsets = Vec::with_capacity(members.len());
                let mut fields = Vec::with_capacity(members.len());
                for (size, member_align, kind) in members {
                    cursor = align_up(cursor, member_align).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                    offsets.push(cursor);
                    fields.push(kind);
                    cursor = cursor.checked_add(size).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                }
                extent = extent.max(cursor);
                laid_out.push(VariantLayout { offsets, fields });
            }
            StructLayout {
                size: align_up(extent, align).ok_or(STRUCT_LAYOUT_OVERFLOW)?,
                align,
                offsets: Vec::new(),
                fields: Vec::new(),
                error_identity: None,
                enum_layout: Some(EnumLayout {
                    tag_size,
                    string_success,
                    variants: laid_out,
                }),
            }
        }
    };
    done[index] = Some(layout);
    active.pop();
    Ok(())
}

/// Lay out every struct or enum reachable from a field type before the field itself.
fn nested_struct_layouts(
    types: &[TypeDef],
    ty: &Type,
    done: &mut Vec<Option<StructLayout>>,
    active: &mut Vec<usize>,
) -> Result<(), String> {
    match ty {
        Type::Struct(id) | Type::Enum(id) => struct_layout_at(types, id.0 as usize, done, active),
        Type::Array { element, .. } => nested_struct_layouts(types, element, done, active),
        _ => Ok(()),
    }
}

/// Size and alignment of an array or struct type. Arrays multiply the element
/// size by the length with checked arithmetic at every level; the cost depends
/// on the nesting depth of the type only, never on a source-supplied count.
fn aggregate_layout(structs: &[StructLayout], ty: &Type) -> Result<(u32, u32), String> {
    type_layout(&|id| structs.get(id as usize), ty)
}

fn has_string_success(layout: &StructLayout) -> bool {
    layout
        .enum_layout
        .as_ref()
        .is_some_and(|layout| layout.string_success)
}

fn type_layout<'a>(
    struct_layout: &dyn Fn(u32) -> Option<&'a StructLayout>,
    ty: &Type,
) -> Result<(u32, u32), String> {
    match ty {
        Type::Primitive(kind) => storage_layout(*kind),
        Type::String => Ok((string_descriptor::SIZE, string_descriptor::ALIGN)),
        Type::List(_) => Ok((list_descriptor::SIZE, list_descriptor::ALIGN)),
        Type::Struct(id) | Type::Enum(id) => struct_layout(id.0)
            .map(|layout| (layout.size, layout.align))
            .ok_or_else(|| "type is out of range".to_string()),
        Type::Array { element, len } => {
            if **element == Type::String {
                return Err("Wasm does not yet support String array elements".into());
            }
            if matches!(element.as_ref(), Type::Enum(id) if struct_layout(id.0).is_some_and(has_string_success))
            {
                return Err("Wasm does not yet support nested Result<String, E> storage".into());
            }
            let (size, align) = type_layout(struct_layout, element)?;
            let bytes = len.checked_mul(size).ok_or(LAYOUT_OVERFLOW)?;
            Ok((bytes, align))
        }
        _ => Err(
            "array elements must be primitives, structs, enums or arrays in frame layout".into(),
        ),
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
        Self::for_function_in(&[], function, DEFAULT_STACK_SIZE)
    }

    /// Lay out one activation frame. A frame larger than `stack_size` can never
    /// run, so it is a compile-time diagnostic; source-supplied array lengths
    /// therefore cannot request memory beyond the configured stack.
    fn for_function_in(
        structs: &[StructLayout],
        function: &Function,
        stack_size: u32,
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
                            Type::String | Type::List(_) | Type::Array { .. } | Type::Struct(_) | Type::Enum(_) => {}
                            _ => return Err(error("nested or non-primitive references are not supported by frame layout".into())),
                        }
                        // A reference already carries its owner's address. Reborrowing
                        // it must never create a second authoritative owner cell.
                    }
                    // An array owner already has its cell (one per array local or value).
                    Type::String | Type::List(_) | Type::Array { .. } | Type::Struct(_) | Type::Enum(_) => {}
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
            if !is_aggregate(ty) {
                continue;
            }
            if matches!(slot, Slot::Value(value) if aliases.contains_key(&value)) {
                continue;
            }
            let error = |message: &str| FrameLayoutError {
                message: message.into(),
                span: span.or(Some(function.span)),
            };
            let what = if *ty == Type::String {
                "String"
            } else if matches!(ty, Type::List(_)) {
                "List"
            } else if matches!(ty, Type::Struct(_)) {
                "struct"
            } else if matches!(ty, Type::Enum(_)) {
                "enum"
            } else {
                "array"
            };
            let too_large = |size: Option<u64>| {
                error(&stack_exceeded(
                    what,
                    size.map_or("more than 4 GiB".into(), |s| format!("{s} bytes")),
                    stack_size,
                ))
            };
            let (bytes, align) = aggregate_layout(structs, ty).map_err(|m| {
                if m == LAYOUT_OVERFLOW {
                    too_large(None)
                } else {
                    error(&m)
                }
            })?;
            offset = align_up(offset, align).ok_or_else(|| too_large(None))?;
            let end = offset.checked_add(bytes).ok_or_else(|| too_large(None))?;
            if end > stack_size {
                return Err(too_large(Some(u64::from(end))));
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
                    message: stack_exceeded("owner", "more than 4 GiB".into(), stack_size),
                    span: Some(function.span),
                })?
                .max(16)
        };
        if size > stack_size {
            return Err(FrameLayoutError {
                message: stack_exceeded("activation", format!("{size} bytes"), stack_size),
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

fn stack_exceeded(what: &str, size: String, stack_size: u32) -> String {
    format!(
        "{what} frame layout of {size} exceeds the configured stack size of {stack_size} bytes; raise [build].stack_size"
    )
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
                InstructionKind::ListPush { value, .. } => count(value),
                InstructionKind::EndListLocal { .. }
                | InstructionKind::EmptyList
                | InstructionKind::Constant(_)
                | InstructionKind::EndStringLocal { .. } => {}
                InstructionKind::Capture(operand)
                | InstructionKind::Copy { source: operand }
                | InstructionKind::ListLen { source: operand }
                | InstructionKind::StringLen { source: operand }
                | InstructionKind::Borrow { owner: operand, .. }
                | InstructionKind::Load { reference: operand }
                | InstructionKind::Unary { operand, .. }
                | InstructionKind::Assign { value: operand, .. } => count(operand),
                InstructionKind::ListGet {
                    source,
                    index: offset,
                }
                | InstructionKind::ValidateUtf8 {
                    source,
                    length: offset,
                    ..
                }
                | InstructionKind::StringIsCharBoundary { source, offset }
                | InstructionKind::StringByteAt { source, offset }
                | InstructionKind::StringScalarAt { source, offset } => {
                    count(source);
                    count(offset);
                }
                InstructionKind::ArrayNew { init } => {
                    if let ArrayInit::Elements(elements) = init {
                        elements.iter().for_each(&mut count);
                    }
                }
                InstructionKind::ElementAddr { base, index, .. } => {
                    count(base);
                    count(index);
                }
                InstructionKind::FieldAddr { base, .. }
                | InstructionKind::VariantAddr { base, .. }
                | InstructionKind::Extract { base, .. }
                | InstructionKind::EnumTag { base }
                | InstructionKind::VariantExtract { base, .. } => count(base),
                InstructionKind::StructNew { fields, .. } => fields.iter().for_each(&mut count),
                InstructionKind::EnumNew { payload, .. } => payload.iter().for_each(&mut count),
                InstructionKind::InitConcatString { strings, .. } => {
                    strings.iter().for_each(&mut count)
                }
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
            TerminatorKind::Switch {
                tag,
                targets,
                default,
                ..
            } => {
                count(tag);
                for edge in targets.iter().map(|(_, edge)| edge).chain(default) {
                    count_edge(edge, &mut count);
                }
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
                initialize,
            } = &consumer.kind
            else {
                continue;
            };
            if !initialize && matches!(producer.kind, InstructionKind::EmptyList) {
                // The previous List descriptor must survive until the replacement.
                continue;
            }
            let source_is_target = matches!(
                &producer.kind,
                InstructionKind::Capture(Operand { source: Source::Local(local), .. }) if local == target
            );
            let array = |ty: Option<&Type>| {
                matches!(
                    ty,
                    Some(
                        Type::String
                            | Type::List(_)
                            | Type::Array { .. }
                            | Type::Struct(_)
                            | Type::Enum(_)
                    )
                )
            };
            if *assigned == output
                && uses[output.0 as usize] == 1
                && matches!(
                    producer.kind,
                    InstructionKind::EmptyList
                        | InstructionKind::ArrayNew { .. }
                        | InstructionKind::StructNew { .. }
                        | InstructionKind::EnumNew { .. }
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

/// Byte size of the pointee of an aggregate operand type (array or struct,
/// owner or reference).
fn aggregate_bytes(structs: &[StructLayout], ty: &Type) -> Result<u32, String> {
    match ty {
        Type::String | Type::List(_) | Type::Array { .. } | Type::Struct(_) | Type::Enum(_) => {
            aggregate_layout(structs, ty).map(|(size, _)| size)
        }
        Type::Reference { inner, .. } => aggregate_bytes(structs, inner),
        _ => Err("expected an array or struct type".into()),
    }
}

/// Aggregate values (arrays and structs) live in frame cells and are passed
/// and returned by address.
fn is_aggregate(ty: &Type) -> bool {
    matches!(
        ty,
        Type::String | Type::List(_) | Type::Array { .. } | Type::Struct(_) | Type::Enum(_)
    )
}

fn scalar_option_offsets(
    layout: &FrameLayout,
    function: &Function,
    value: ValueId,
) -> Result<(u32, u32), String> {
    let cell = array_cell_of(layout, Slot::Value(value.0))?;
    let Type::Enum(type_id) = function.values[value.0 as usize] else {
        return Err("expected an Option output".into());
    };
    let payload = layout
        .structs
        .get(type_id.0 as usize)
        .and_then(|ty| ty.enum_layout.as_ref())
        .and_then(|ty| ty.variants.first())
        .and_then(|some| some.offsets.first())
        .ok_or("missing Option payload layout")?;
    Ok((
        cell.offset,
        cell.offset
            .checked_add(*payload)
            .ok_or(STRUCT_LAYOUT_OVERFLOW)?,
    ))
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
        Type::String | Type::List(_) | Type::Array { .. } | Type::Struct(_) | Type::Enum(_) => {
            ValType::I32
        }
    }
}

// Experimental private stack. Memory starts with reserved low addresses,
// then the stack of `stack_size` bytes, then the optional entry return cell
// (see `static_data_start`). Frames grow upward, aligned to 16 bytes. Traps do not
// unwind active caller frames. Global 0 is the stack pointer; global 1 is set
// to 1 before the trap raised by stack exhaustion so a host can tell it from
// other traps.
const FRAME_START: u32 = RESERVED_BYTES;
const OVERFLOW_FLAG_GLOBAL: u32 = 1;
/// Trap record global when frames exist (global 2); otherwise it is global 0.
const TRAP_GLOBAL: u32 = 2;
/// Name of the exported stack-exhaustion flag global.
pub const STACK_OVERFLOW_EXPORT: &str = "__mb_stack_overflow";

/// Name of the exported trap record global.
pub const TRAP_EXPORT: &str = "__mb_trap";
/// Name of the Wasm custom section a driver may add with the location table.
pub const TRAP_SECTION: &str = "memobits.traps";

/// Why a checked operation trapped. The code is the low byte of the
/// `__mb_trap` global; the remaining 24 bits hold the location id (0: unknown).
///
/// `Division` and `Remainder` are recorded before a native Wasm division, which
/// traps by itself; the host refines them by the native trap kind (divide by
/// zero, or signed overflow for division). They are meaningless after an
/// `unreachable` trap and must then be ignored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum TrapReason {
    Add = 1,
    Subtract = 2,
    Multiply = 3,
    Negate = 4,
    Division = 5,
    Remainder = 6,
    DivisionOverflow = 7,
    IndexOutOfBounds = 8,
    ArgumentRange = 9,
    HeapAllocation = 10,
}

impl TrapReason {
    pub const fn code(self) -> u8 {
        self as u8
    }
}

/// Where a check records its trap: the global to store to and a location id.
#[derive(Clone, Copy)]
struct Site {
    global: u32,
    location: u32,
}

impl Site {
    fn record(self, body: &mut WasmFunction, reason: TrapReason) {
        let packed = (self.location << 8) | u32::from(reason.code());
        body.instruction(&WasmInstruction::I32Const(packed as i32));
        body.instruction(&WasmInstruction::GlobalSet(self.global));
    }
}

/// Collects trap sites across functions while code is generated.
struct Traps {
    global: u32,
    spans: Vec<Span>,
}

impl Traps {
    /// Largest location id that fits beside the reason in an `i32`.
    const MAX_LOCATION: usize = (1 << 23) - 1;

    fn site(&mut self, span: Option<Span>) -> Site {
        let location = match span {
            Some(span) if self.spans.len() < Self::MAX_LOCATION => {
                self.spans.push(span);
                self.spans.len() as u32
            }
            _ => 0,
        };
        Site {
            global: self.global,
            location,
        }
    }
}

#[derive(Clone, Copy)]
struct FrameState {
    base: u32,
    size: u32,
    /// First address past the stack.
    limit: u32,
}

impl FrameState {
    fn enter(self, body: &mut WasmFunction) {
        body.instruction(&WasmInstruction::GlobalGet(0));
        body.instruction(&WasmInstruction::LocalSet(self.base));
        // Check available space before addition, so neither wrapping nor a
        // failed allocation can mutate the shared stack pointer.
        body.instruction(&WasmInstruction::I32Const(self.size as i32));
        body.instruction(&WasmInstruction::I32Const(self.limit as i32));
        body.instruction(&WasmInstruction::LocalGet(self.base));
        body.instruction(&WasmInstruction::I32Sub);
        body.instruction(&WasmInstruction::I32GtU);
        body.instruction(&WasmInstruction::If(BlockType::Empty));
        body.instruction(&WasmInstruction::I32Const(1));
        body.instruction(&WasmInstruction::GlobalSet(OVERFLOW_FLAG_GLOBAL));
        body.instruction(&WasmInstruction::Unreachable);
        body.instruction(&WasmInstruction::End);
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

struct EntryAdapter {
    address: u32,
    size: u32,
    metadata: Vec<u8>,
    static_layout: StaticLayout,
}

fn outcome_entry(
    program: &Program,
    function: &Function,
    layouts: &[StructLayout],
    mut static_layout: StaticLayout,
) -> Result<Option<EntryAdapter>, String> {
    let Type::Enum(id) = function.signature.result.as_ref() else {
        return Ok(None);
    };
    let definition = &program.types[id.0 as usize];
    let Some(outcome) = definition.entry_outcome else {
        return Ok(None);
    };
    if !function.signature.parameters.is_empty() {
        return Err("Result and Attempt application entries must take no parameters".into());
    }

    let TypeDefKind::Enum { variants } = &definition.kind else {
        unreachable!("validated outcome definition");
    };
    let success = match variants[0].payload.as_slice() {
        [Type::Primitive(kind)] => match kind {
            Primitive::Bool => Some(entry_abi::Scalar::Bool),
            Primitive::I8 => Some(entry_abi::Scalar::I8),
            Primitive::I16 => Some(entry_abi::Scalar::I16),
            Primitive::I32 => Some(entry_abi::Scalar::I32),
            Primitive::I64 => Some(entry_abi::Scalar::I64),
            Primitive::U8 => Some(entry_abi::Scalar::U8),
            Primitive::U16 => Some(entry_abi::Scalar::U16),
            Primitive::U32 => Some(entry_abi::Scalar::U32),
            Primitive::U64 => Some(entry_abi::Scalar::U64),
            Primitive::F32 => Some(entry_abi::Scalar::F32),
            Primitive::F64 => Some(entry_abi::Scalar::F64),
            Primitive::Unit => None,
        },
        _ => None,
    }
    .ok_or(
        "application entry outcomes require a primitive success payload (Bool, integer, or float)",
    )?;
    let failure_variant = outcome.variants().len() - 1;
    let [Type::Struct(error)] = variants[failure_variant].payload.as_slice() else {
        unreachable!("validated outcome error payload");
    };
    let error_def = &program.types[error.0 as usize];
    let error_layout = &layouts[error.0 as usize];
    let path = &error_def.path;
    let error_name = if error_def.error_ancestry == Some(ErrorAncestry::Root) {
        path.name.clone()
    } else {
        format!(
            "{}::{}::{}",
            path.package,
            path.module.join("::"),
            path.name
        )
    };

    let layout = &layouts[id.0 as usize];
    let variants = &layout.enum_layout.as_ref().expect("laid out enum").variants;
    let payload_offset = variants[0].offsets[0];
    debug_assert_eq!(payload_offset, variants[failure_variant].offsets[0]);
    debug_assert_eq!(error_layout.offsets[0], entry_abi::ERROR_ID_BYTES);
    let size = layout.size;
    let metadata = entry_abi::Metadata {
        family: match outcome {
            EntryOutcome::Result => entry_abi::Family::Result,
            EntryOutcome::Attempt => entry_abi::Family::Attempt,
        },
        success,
        payload_offset: payload_offset
            .try_into()
            .map_err(|_| "invalid entry payload offset")?,
        size,
        error_id: error_layout.error_identity.expect("laid out Error"),
        error_name: &error_name,
    }
    .encode()
    .ok_or("application entry outcome does not fit the version 1 metadata format")?;
    // Keep the return cell outside the guest stack so the configured stack
    // budget still belongs entirely to guest calls.
    let address = static_layout.reserve(size).map_err(|error| match error {
        LayoutError::AddressOverflow => "application entry result exceeds the 32-bit memory",
        LayoutError::PageLimit => "application entry result exceeds the supported memory size",
    })?;
    Ok(Some(EntryAdapter {
        address,
        size,
        metadata,
        static_layout,
    }))
}

fn encode(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    stack_size: u32,
    entry: Option<EntryAdapter>,
) -> Result<(Vec<u8>, Vec<Span>), String> {
    let structs = struct_layouts(&program.types)?;
    let sizes = program
        .functions
        .iter()
        .map(|function| {
            FrameLayout::for_function_in(&structs, function, stack_size)
                .map(|layout| layout.size)
                .map_err(|error| error.message)
        })
        .collect::<Result<Vec<_>, _>>()?;
    encode_frames_traced(program, exports, &sizes, false, stack_size, entry)
}

// Tests may override frame sizes to exercise allocation and restoration
// independently of owner layout.
#[cfg(test)]
fn encode_with_frame_sizes(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    sizes: &[u32],
    stack_size: u32,
) -> Result<Vec<u8>, String> {
    encode_frames(program, exports, sizes, true, stack_size)
}

#[cfg(test)]
fn encode_frames(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    sizes: &[u32],
    observe: bool,
    stack_size: u32,
) -> Result<Vec<u8>, String> {
    encode_frames_traced(program, exports, sizes, observe, stack_size, None).map(|(bytes, _)| bytes)
}

/// A private literal table. Each entry is a String descriptor with static
/// provenance, followed by the UTF-8 bytes. Guest code copies only
/// the descriptor into its frame; no language operation can write the bytes.
struct StringData<'a> {
    start: Option<u32>,
    offsets: BTreeMap<&'a str, u32>,
    bytes: Vec<u8>,
}

impl<'a> StringData<'a> {
    fn collect(functions: &[&'a Function], layout: &mut StaticLayout) -> Result<Self, String> {
        let mut data = Self {
            start: None,
            offsets: BTreeMap::new(),
            bytes: Vec::new(),
        };
        for function in functions {
            for instruction in function.blocks.iter().flat_map(|block| &block.instructions) {
                let InstructionKind::Constant(Constant::String(text)) = &instruction.kind else {
                    continue;
                };
                if data.offsets.contains_key(text.as_str()) {
                    continue;
                }
                let layout_error = "String literals exceed the supported Wasm memory size";
                let len = u32::try_from(text.len()).map_err(|_| layout_error)?;
                let size = string_descriptor::SIZE
                    .checked_add(len)
                    .ok_or(layout_error)?;
                let descriptor = layout.reserve(size).map_err(|_| layout_error)?;
                let address = descriptor + string_descriptor::SIZE;
                data.start.get_or_insert(descriptor);
                data.offsets.insert(text, descriptor);
                data.bytes.extend(string_descriptor::encode(address, len));
                data.bytes.extend(text.as_bytes());
            }
        }
        Ok(data)
    }
}

fn encode_frames_traced(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    sizes: &[u32],
    observe: bool,
    stack_size: u32,
    entry: Option<EntryAdapter>,
) -> Result<(Vec<u8>, Vec<Span>), String> {
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
    let mut static_layout = match &entry {
        Some(adapter) => adapter.static_layout,
        None => {
            StaticLayout::new(stack_size).ok_or("stack size does not fit the Wasm address space")?
        }
    };
    let strings = StringData::collect(&selected, &mut static_layout)?;
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
        let hidden = is_aggregate(signature.result.as_ref()).then_some(ValType::I32);
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
        let results = if matches!(signature.result.as_ref(), Type::Primitive(Primitive::Unit))
            || is_aggregate(signature.result.as_ref())
        {
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
        let index = if entry.is_some() && name == entry_abi::ENTRY_EXPORT {
            selected.len() as u32
        } else {
            indices[&function.0]
        };
        export_section.export(name, ExportKind::Func, index);
    }
    if entry.is_some() {
        types.ty().function([], [ValType::I32, ValType::I32]);
        functions.function(signatures.len() as u32);
        export_section.export(entry_abi::MEMORY_EXPORT, ExportKind::Memory, 0);
    }
    let heap_strings = program.heap_strings();
    let has_list_push = reachable.iter().any(|id| {
        program.functions[*id as usize]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|inst| matches!(inst.kind, InstructionKind::ListPush { .. }))
    });
    let use_heap = has_list_push
        || reachable.iter().any(|id| {
            let facts = &heap_strings[*id as usize];
            !facts.locals.is_empty() || facts.returns_heap_ok
        });
    let heap_copy_index = use_heap.then(|| {
        let adapter_count = u32::from(entry.is_some());
        let first = signatures.len() as u32 + adapter_count;
        types.ty().function([ValType::I32; 5], [ValType::I32]); // String copy
        types.ty().function([ValType::I32], []); // block release
        types.ty().function([ValType::I32], [ValType::I32]); // block reservation
        for offset in 0..3 {
            functions.function(first + offset);
        }
        if has_list_push {
            types.ty().function([ValType::I32; 3], [ValType::I32]);
            functions.function(first + 3);
        }
        selected.len() as u32 + adapter_count
    });
    let utf8 = reachable
        .iter()
        .any(|id| {
            program.functions[*id as usize]
                .blocks
                .iter()
                .flat_map(|block| &block.instructions)
                .any(|inst| matches!(inst.kind, InstructionKind::ValidateUtf8 { .. }))
        })
        .then(|| {
            let prior = u32::from(entry.is_some())
                + if use_heap {
                    3 + u32::from(has_list_push)
                } else {
                    0
                };
            types.ty().function([ValType::I32; 3], [ValType::I64]);
            functions.function(signatures.len() as u32 + prior);
            (selected.len() as u32 + prior, program)
        });
    let has_frames = reachable.iter().any(|id| sizes[*id as usize] != 0);
    if observe && has_frames {
        export_section.export("__test_memory", ExportKind::Memory, 0);
        export_section.export("__test_sp", ExportKind::Global, 0);
    }
    if has_frames {
        export_section.export(
            STACK_OVERFLOW_EXPORT,
            ExportKind::Global,
            OVERFLOW_FLAG_GLOBAL,
        );
    }
    let structs = struct_layouts(&program.types)?;
    let mut code = CodeSection::new();
    let mut traps = Traps {
        global: if has_frames { TRAP_GLOBAL } else { 0 },
        spans: Vec::new(),
    };
    for id in &reachable {
        code.function(&compile_function(
            &program.functions[*id as usize],
            &indices,
            sizes[*id as usize],
            observe,
            &structs,
            stack_size,
            &strings.offsets,
            &heap_strings[*id as usize].locals,
            heap_copy_index,
            utf8,
            &mut traps,
        )?);
    }
    if let Some(adapter) = &entry {
        let mut wrapper = WasmFunction::new([]);
        wrapper.instruction(&WasmInstruction::I32Const(adapter.address as i32));
        wrapper.instruction(&WasmInstruction::Call(
            indices[&exports[entry_abi::ENTRY_EXPORT].0],
        ));
        wrapper.instruction(&WasmInstruction::I32Const(adapter.address as i32));
        wrapper.instruction(&WasmInstruction::I32Const(adapter.size as i32));
        wrapper.instruction(&WasmInstruction::End);
        code.function(&wrapper);
    }
    if let Some(copy) = heap_copy_index {
        code.function(&string_heap::copy_ranges(copy + 2));
        code.function(&string_heap::releaser());
        code.function(&string_heap::reserve());
        if has_list_push {
            code.function(&list_descriptor::push(copy + 2, copy + 1));
        }
    }
    if utf8.is_some() {
        code.function(&utf8::validator());
    }
    // Check sites may exist without any frame (pure arithmetic), so the trap
    // record needs a global of its own then.
    let has_traps = heap_copy_index.is_some() || !traps.spans.is_empty();
    if has_traps {
        export_section.export(TRAP_EXPORT, ExportKind::Global, traps.global);
    }
    let mut memories = MemorySection::new();
    let mut globals = GlobalSection::new();
    let has_memory = has_frames || entry.is_some() || strings.start.is_some();
    if has_memory {
        let pages = static_layout.pages();
        memories.memory(MemoryType {
            minimum: pages,
            maximum: Some(if heap_copy_index.is_some() {
                memory::MAX_PAGES
            } else {
                pages
            }),
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
    }
    if has_frames {
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(FRAME_START as i32),
        );
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(0),
        );
    }
    if has_traps {
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(0),
        );
    }
    if heap_copy_index.is_some() {
        // Concat always has a String frame cell and an allocation trap site.
        debug_assert!(has_frames && has_traps);
        let heap_start = align_up(static_layout.end(), string_heap::BLOCK_ALIGN)
            .ok_or("heap start exceeds Wasm32 address space")?;
        let heap_global = GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        };
        globals.global(heap_global, &ConstExpr::i32_const(heap_start as i32));
        globals.global(heap_global, &ConstExpr::i32_const(0));
    }
    let mut module = Module::new();
    module.section(&types).section(&functions);
    if has_memory {
        module.section(&memories);
    }
    if has_frames || has_traps {
        module.section(&globals);
    }
    module.section(&export_section).section(&code);
    if let Some(start) = strings.start {
        let mut data = DataSection::new();
        data.active(0, &ConstExpr::i32_const(start as i32), strings.bytes);
        module.section(&data);
    }
    if let Some(adapter) = entry {
        module.section(&CustomSection {
            name: entry_abi::SECTION.into(),
            data: adapter.metadata.into(),
        });
    }
    Ok((module.finish(), traps.spans))
}

#[allow(clippy::too_many_arguments)]
fn compile_function(
    function: &Function,
    indices: &BTreeMap<u32, u32>,
    frame_size: u32,
    observe: bool,
    structs: &[StructLayout],
    stack_size: u32,
    strings: &BTreeMap<&str, u32>,
    heap_locals: &HashSet<LocalId>,
    heap_copy_index: Option<u32>,
    utf8: Option<(u32, &Program)>,
    traps: &mut Traps,
) -> Result<WasmFunction, String> {
    let layout = FrameLayout::for_function_in(structs, function, stack_size)
        .map_err(|error| error.message)?;
    let result_is_array = is_aggregate(function.signature.result.as_ref());
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
        limit: FRAME_START + stack_size,
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
        let site = traps.site(Some(function.span));
        guard_parameter(
            body,
            site,
            index as u32,
            &function.locals[local.0 as usize].ty,
        )?;
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
            if matches!(function.locals[local.0 as usize].ty, Type::List(_)) {
                body.instructions().local_get(index as u32);
                list_descriptor::clear_allocation(body);
            } else if heap_locals.contains(local) {
                // The incoming pointer addresses the caller's moved slot.
                // Clear it only after the callee has received the descriptor.
                body.instruction(&WasmInstruction::LocalGet(index as u32));
                body.instruction(&WasmInstruction::I32Const(0));
                string_descriptor::store_allocation(body);
            }
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
                strings,
                heap_locals,
                heap_copy_index,
                utf8,
                traps,
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

// Call only inside the branch where offset is below the descriptor length.
fn emit_string_byte(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    source: &Operand,
    offset: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    emit_string_byte_address(body, function, param_count, source, offset, layout, frame)?;
    emit_load(body, Primitive::U8);
    Ok(())
}

fn emit_string_byte_address(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    source: &Operand,
    offset: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    emit_operand(body, function, param_count, source, layout, frame)?;
    string_descriptor::load_address(body);
    emit_operand(body, function, param_count, offset, layout, frame)?;
    body.instruction(&WasmInstruction::I32Add);
    Ok(())
}

// Called only after index < len. Return -1 for a continuation byte or a
// width that would run past the logical end.
#[allow(clippy::too_many_arguments)]
fn emit_string_scalar(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    source: &Operand,
    offset: &Operand,
    layout: &FrameLayout,
    frame: FrameState,
    lead: u32,
) -> Result<(), String> {
    emit_string_byte(
        body,
        function,
        param_count,
        source,
        offset,
        layout,
        Some(frame),
    )?;
    body.instruction(&WasmInstruction::LocalSet(lead));
    // UTF-8 is already validated. Prefix ranges select the scalar width.
    // The 0x80..0xbf range is a continuation byte, never a scalar start.
    let prefixes = [
        (0x80, 1, 0x7f),
        (0xc0, 0, 0),
        (0xe0, 2, 0x1f),
        (0xf0, 3, 0x0f),
        (0xf5, 4, 0x07),
    ];
    for (limit, width, mask) in prefixes {
        body.instruction(&WasmInstruction::LocalGet(lead));
        body.instruction(&WasmInstruction::I32Const(limit));
        body.instruction(&WasmInstruction::I32LtU);
        body.instruction(&WasmInstruction::If(BlockType::Result(ValType::I32)));
        match width {
            0 => {
                body.instruction(&WasmInstruction::I32Const(-1));
            }
            1 => {
                body.instruction(&WasmInstruction::LocalGet(lead));
            }
            _ => {
                // index < len ensures subtraction cannot wrap. Checking the
                // remaining width before any tail load bounds all byte offsets.
                emit_operand(body, function, param_count, source, layout, Some(frame))?;
                string_descriptor::load_length(body);
                emit_operand(body, function, param_count, offset, layout, Some(frame))?;
                body.instruction(&WasmInstruction::I32Sub);
                body.instruction(&WasmInstruction::I32Const(width));
                body.instruction(&WasmInstruction::I32GeU);
                body.instruction(&WasmInstruction::If(BlockType::Result(ValType::I32)));
                body.instruction(&WasmInstruction::LocalGet(lead));
                body.instruction(&WasmInstruction::I32Const(mask));
                body.instruction(&WasmInstruction::I32And);
                for delta in 1..width {
                    body.instruction(&WasmInstruction::I32Const(6));
                    body.instruction(&WasmInstruction::I32Shl);
                    emit_string_byte_address(
                        body,
                        function,
                        param_count,
                        source,
                        offset,
                        layout,
                        Some(frame),
                    )?;
                    body.instruction(&WasmInstruction::I32Load8U(MemArg {
                        offset: delta as u64,
                        ..memory_arg(Primitive::U8)
                    }));
                    body.instruction(&WasmInstruction::I32Const(0x3f));
                    body.instruction(&WasmInstruction::I32And);
                    body.instruction(&WasmInstruction::I32Or);
                }
                body.instruction(&WasmInstruction::Else);
                body.instruction(&WasmInstruction::I32Const(-1));
                body.instruction(&WasmInstruction::End);
            }
        }
        body.instruction(&WasmInstruction::Else);
    }
    body.instruction(&WasmInstruction::I32Const(-1));
    for _ in prefixes {
        body.instruction(&WasmInstruction::End);
    }
    Ok(())
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

fn release_string_local(
    body: &mut WasmFunction,
    local: LocalId,
    layout: &FrameLayout,
    frame: Option<FrameState>,
    heap_copy_index: Option<u32>,
) -> Result<(), String> {
    let cell = array_cell_of(layout, Slot::Local(local.0))?;
    emit_address(
        body,
        frame.ok_or("String local requires a frame")?,
        cell.offset,
    );
    string_descriptor::load_allocation(body);
    let releaser = heap_copy_index.ok_or("missing String release helper")? + 1;
    body.instruction(&WasmInstruction::Call(releaser));
    Ok(())
}

fn release_list_cell(
    body: &mut WasmFunction,
    cell: ArrayCell,
    frame: Option<FrameState>,
    heap_copy_index: Option<u32>,
) -> Result<(), String> {
    if let Some(copy) = heap_copy_index {
        emit_address(body, frame.ok_or("List requires a frame")?, cell.offset);
        list_descriptor::load_allocation(body);
        body.instructions().call(copy + 1);
    }
    Ok(())
}

fn clear_moved_heap_source(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    operand: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
    heap_locals: &HashSet<LocalId>,
) -> Result<(), String> {
    if let Source::Local(source) = operand.source {
        if matches!(function.locals[source.0 as usize].ty, Type::List(_)) {
            emit_operand(body, function, param_count, operand, layout, frame)?;
            list_descriptor::clear_allocation(body);
        } else if heap_locals.contains(&source) {
            emit_operand(body, function, param_count, operand, layout, frame)?;
            body.instruction(&WasmInstruction::I32Const(0));
            string_descriptor::store_allocation(body);
        }
    }
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

fn guard_parameter(
    body: &mut WasmFunction,
    site: Site,
    parameter: u32,
    ty: &Type,
) -> Result<(), String> {
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
            trap_if(body, site, TrapReason::ArgumentRange);
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
            trap_if(body, site, TrapReason::ArgumentRange);
            get(body);
            body.instruction(&WasmInstruction::I32Const(max));
            body.instruction(&WasmInstruction::I32GtS);
            trap_if(body, site, TrapReason::ArgumentRange);
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
            trap_if(body, site, TrapReason::ArgumentRange);
        }
        _ => {}
    }
    Ok(())
}

fn arithmetic_reason(op: BinaryOp) -> TrapReason {
    match op {
        BinaryOp::Add => TrapReason::Add,
        BinaryOp::Subtract => TrapReason::Subtract,
        _ => TrapReason::Multiply,
    }
}

/// Trap when the condition on the stack is true, recording why and where.
fn trap_if(body: &mut WasmFunction, site: Site, reason: TrapReason) {
    body.instruction(&WasmInstruction::If(BlockType::Empty));
    site.record(body, reason);
    body.instruction(&WasmInstruction::Unreachable);
    body.instruction(&WasmInstruction::End);
}

fn emit_unary(
    body: &mut WasmFunction,
    op: UnaryOp,
    input: u32,
    ty: &Type,
    output: u32,
    site: Site,
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
            trap_if(body, site, TrapReason::Negate);
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

#[allow(clippy::too_many_arguments)]
fn emit_binary(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    ty: &Type,
    output: u32,
    scratch64: u32,
    site: Site,
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
            return emit_narrow_integer(body, op, left, right, *kind, output, scratch64, site);
        }
        Primitive::I64 | Primitive::U64 => {
            return emit_wide_integer(body, op, left, right, *kind, output, site);
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

#[allow(clippy::too_many_arguments)]
fn emit_narrow_integer(
    body: &mut WasmFunction,
    op: BinaryOp,
    left: u32,
    right: u32,
    kind: Primitive,
    output: u32,
    scratch: u32,
    site: Site,
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
            trap_if(body, site, TrapReason::DivisionOverflow);
        }
        site.record(
            body,
            if op == BinaryOp::Divide {
                TrapReason::Division
            } else {
                TrapReason::Remainder
            },
        );
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
        trap_if(body, site, arithmetic_reason(op));
    }
    if let Some(max) = max {
        body.instruction(&WasmInstruction::LocalGet(scratch));
        body.instruction(&WasmInstruction::I64Const(max));
        body.instruction(if signed {
            &WasmInstruction::I64GtS
        } else {
            &WasmInstruction::I64GtU
        });
        trap_if(body, site, arithmetic_reason(op));
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
    site: Site,
) -> Result<(), String> {
    let signed = kind == Primitive::I64;
    if matches!(op, BinaryOp::Divide | BinaryOp::Remainder) {
        // The native division traps by itself; note why and where first.
        site.record(
            body,
            if op == BinaryOp::Divide {
                TrapReason::Division
            } else {
                TrapReason::Remainder
            },
        );
    }
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
            trap_if(body, site, TrapReason::Add);
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
            trap_if(body, site, TrapReason::Subtract);
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
                trap_if(body, site, TrapReason::Multiply);
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
            trap_if(body, site, TrapReason::Multiply);
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
    strings: &BTreeMap<&str, u32>,
    heap_locals: &HashSet<LocalId>,
    heap_copy_index: Option<u32>,
    utf8: Option<(u32, &Program)>,
    traps: &mut Traps,
) -> Result<(), String> {
    let output = instruction
        .output
        .map(|id| value_local(function, param_count, id));
    match &instruction.kind {
        InstructionKind::EndStringLocal { local } => {
            if heap_locals.contains(local) {
                release_string_local(body, *local, layout, frame, heap_copy_index)?;
            }
        }
        InstructionKind::InitConcatString { target, strings } => {
            for source in strings {
                emit_operand(body, function, param_count, source, layout, frame)?;
                string_descriptor::load_address(body);
                emit_operand(body, function, param_count, source, layout, frame)?;
                string_descriptor::load_length(body);
            }
            let cell = array_cell_of(layout, Slot::Local(target.0))?;
            emit_address(
                body,
                frame.ok_or("concat local requires a frame")?,
                cell.offset,
            );
            body.instruction(&WasmInstruction::Call(
                heap_copy_index.ok_or("missing String allocation helper")?,
            ));
            body.instruction(&WasmInstruction::I32Eqz);
            trap_if(
                body,
                traps.site(instruction.span),
                TrapReason::HeapAllocation,
            );
        }
        InstructionKind::Constant(Constant::String(text)) => {
            let value = instruction.output.ok_or("String literal lacks an output")?;
            let cell = array_cell_of(layout, Slot::Value(value.0))?;
            let frame = frame.ok_or("String literal requires a frame")?;
            let address = *strings
                .get(text.as_str())
                .ok_or("missing String literal data")?;
            emit_address(body, frame, cell.offset);
            body.instruction(&WasmInstruction::I32Const(address as i32));
            body.instruction(&WasmInstruction::I32Const(string_descriptor::SIZE as i32));
            body.instruction(&WasmInstruction::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
        }
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
                emit_array_copy(body, function, param_count, cell, operand, layout, frame)?;
                // A validated heap capture stages the outgoing return value.
                // Lexical cleanup must see the original binding as moved.
                clear_moved_heap_source(
                    body,
                    function,
                    param_count,
                    operand,
                    layout,
                    frame,
                    heap_locals,
                )?;
                return Ok(());
            }
            emit_operand(body, function, param_count, operand, layout, frame)?;
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::ValidateUtf8 {
            source,
            length,
            construct_string,
        } => {
            let (validator, program) = utf8.ok_or("missing UTF-8 validator")?;
            let frame = frame.ok_or("UTF-8 result requires a frame")?;
            let Type::Reference { inner, .. } = value_type(function, source)? else {
                return Err("UTF-8 input must be a reference".into());
            };
            let Type::Array { len, .. } = *inner else {
                return Err("UTF-8 input must refer to an array".into());
            };
            emit_operand(body, function, param_count, source, layout, Some(frame))?;
            emit_operand(body, function, param_count, length, layout, Some(frame))?;
            body.instructions()
                .i32_const(len as i32)
                .call(validator)
                .local_set(scratch64);
            let result = instruction
                .output
                .ok_or("UTF-8 validation lacks a result")?;
            let cell = array_cell_of(layout, Slot::Value(result.0))?;
            let success = if *construct_string {
                Type::String
            } else {
                Type::Primitive(Primitive::I32)
            };
            utf8::write_outcome(
                body,
                program,
                &layout.structs,
                (frame, cell.offset),
                (&function.values[result.0 as usize], &success),
                scratch64,
                |body, destination| {
                    if *construct_string {
                        // Validation accepted this exact prefix. The read loan
                        // keeps the same bytes live through both leaf helpers.
                        emit_operand(body, function, param_count, source, layout, Some(frame))?;
                        emit_operand(body, function, param_count, length, layout, Some(frame))?;
                        body.instructions().i32_const(0).i32_const(0);
                        emit_address(body, frame, destination);
                        body.instructions()
                            .call(heap_copy_index.ok_or("missing String allocation helper")?)
                            .i32_eqz();
                        trap_if(
                            body,
                            traps.site(instruction.span),
                            TrapReason::HeapAllocation,
                        );
                    } else {
                        utf8::emit_word(body, frame, destination, scratch64);
                    }
                    Ok(())
                },
            )?;
        }
        InstructionKind::EndListLocal { local } => {
            let cell = array_cell_of(layout, Slot::Local(local.0))?;
            release_list_cell(body, cell, frame, heap_copy_index)?;
        }
        InstructionKind::ListPush { target, value } => {
            let list = match &function.locals[target.0 as usize].ty {
                Type::Reference { inner, .. } => inner.as_ref(),
                owner => owner,
            };
            let Type::List(element) = *list else {
                return Err("List push target is not a List".into());
            };
            let (width, _) = storage_layout(element)?;
            let receiver = Operand {
                source: Source::Local(*target),
                mode: memobits_ir::UseMode::Read,
                span: instruction.span,
            };
            emit_operand(body, function, param_count, &receiver, layout, frame)?;
            emit_operand(body, function, param_count, value, layout, frame)?;
            body.instructions()
                .i32_const(width as i32)
                .call(heap_copy_index.ok_or("missing List allocation helper")? + 3)
                .i32_eqz();
            trap_if(
                body,
                traps.site(instruction.span),
                TrapReason::HeapAllocation,
            );
        }
        InstructionKind::EmptyList => {
            let value = instruction.output.ok_or("empty List lacks a value")?;
            let cell = array_cell_of(layout, Slot::Value(value.0))?;
            emit_address(body, frame.ok_or("List requires a frame")?, cell.offset);
            list_descriptor::initialize_empty(body);
        }
        InstructionKind::ListGet { source, index } => {
            let frame = frame.ok_or("List get requires a frame")?;
            let value = instruction.output.ok_or("List get lacks an output")?;
            let (tag, payload) = scalar_option_offsets(layout, function, value)?;
            let source_type = value_type(function, source)?;
            let owner_type = match &source_type {
                Type::Reference { inner, .. } => inner.as_ref(),
                owner => owner,
            };
            let Type::List(element) = *owner_type else {
                return Err("List get source is not a List".into());
            };
            let (width, _) = storage_layout(element)?;
            emit_address(body, frame, tag);
            emit_operand(body, function, param_count, index, layout, Some(frame))?;
            emit_operand(body, function, param_count, source, layout, Some(frame))?;
            list_descriptor::load_length(body);
            body.instructions()
                .i32_lt_u()
                .if_(BlockType::Result(ValType::I32));

            // An initialized index is within the checked extent from push.
            emit_address(body, frame, payload);
            emit_operand(body, function, param_count, source, layout, Some(frame))?;
            list_descriptor::load_address(body);
            emit_operand(body, function, param_count, index, layout, Some(frame))?;
            body.instructions()
                .i32_const(width as i32)
                .i32_mul()
                .i32_add();
            emit_load(body, element);
            emit_store(body, element);
            body.instructions().i32_const(0).else_().i32_const(1).end();
            emit_store(body, Primitive::U8);
        }
        InstructionKind::ListLen { source } => {
            emit_operand(body, function, param_count, source, layout, frame)?;
            list_descriptor::load_length(body);
            body.instructions()
                .local_set(output.ok_or("List length lacks an output")?);
        }
        InstructionKind::StringLen { source } => {
            emit_operand(body, function, param_count, source, layout, frame)?;
            string_descriptor::load_length(body);
            body.instruction(&WasmInstruction::LocalSet(
                output.ok_or("StringLen lacks an output")?,
            ));
        }
        InstructionKind::StringIsCharBoundary { source, offset } => {
            let output = output.ok_or("StringIsCharBoundary lacks an output")?;
            emit_operand(body, function, param_count, source, layout, frame)?;
            string_descriptor::load_length(body);
            body.instruction(&WasmInstruction::LocalSet(output));
            emit_operand(body, function, param_count, offset, layout, frame)?;
            body.instruction(&WasmInstruction::LocalGet(output));
            body.instruction(&WasmInstruction::I32LtU);
            body.instruction(&WasmInstruction::If(BlockType::Result(ValType::I32)));
            // Only offsets strictly below the byte length can reach the byte load.
            emit_string_byte(body, function, param_count, source, offset, layout, frame)?;
            body.instruction(&WasmInstruction::I32Const(0xc0));
            body.instruction(&WasmInstruction::I32And);
            body.instruction(&WasmInstruction::I32Const(0x80));
            body.instruction(&WasmInstruction::I32Ne);
            body.instruction(&WasmInstruction::Else);
            emit_operand(body, function, param_count, offset, layout, frame)?;
            body.instruction(&WasmInstruction::LocalGet(output));
            body.instruction(&WasmInstruction::I32Eq);
            body.instruction(&WasmInstruction::End);
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::StringByteAt { source, offset }
        | InstructionKind::StringScalarAt { source, offset } => {
            let scalar = matches!(&instruction.kind, InstructionKind::StringScalarAt { .. });
            let output = output.ok_or("String read lacks an output")?;
            let value = instruction.output.ok_or("String read lacks an output")?;
            let (tag, payload) = scalar_option_offsets(layout, function, value)?;
            let frame = frame.ok_or("String read requires a frame")?;

            emit_operand(body, function, param_count, offset, layout, Some(frame))?;
            emit_operand(body, function, param_count, source, layout, Some(frame))?;
            string_descriptor::load_length(body);
            body.instruction(&WasmInstruction::I32LtU);
            body.instruction(&WasmInstruction::If(BlockType::Result(ValType::I32)));
            let payload_type = if scalar {
                // Aggregate operands use the frame cell. Their otherwise unused
                // Wasm local can hold the lead byte and then the decoded scalar.
                emit_string_scalar(
                    body,
                    function,
                    param_count,
                    source,
                    offset,
                    layout,
                    frame,
                    output,
                )?;
                Primitive::U32
            } else {
                emit_string_byte(
                    body,
                    function,
                    param_count,
                    source,
                    offset,
                    layout,
                    Some(frame),
                )?;
                Primitive::U8
            };
            body.instruction(&WasmInstruction::Else);
            body.instruction(&WasmInstruction::I32Const(-1));
            body.instruction(&WasmInstruction::End);
            body.instruction(&WasmInstruction::LocalSet(output));

            emit_address(body, frame, tag);
            body.instruction(&WasmInstruction::LocalGet(output));
            body.instruction(&WasmInstruction::I32Const(-1));
            body.instruction(&WasmInstruction::I32Ne);
            body.instruction(&WasmInstruction::If(BlockType::Result(ValType::I32)));
            emit_address(body, frame, payload);
            body.instruction(&WasmInstruction::LocalGet(output));
            emit_store(body, payload_type);
            body.instruction(&WasmInstruction::I32Const(0)); // Some
            body.instruction(&WasmInstruction::Else);
            body.instruction(&WasmInstruction::I32Const(1)); // None
            body.instruction(&WasmInstruction::End);
            // Both Option types have two variants and therefore a one-byte tag.
            emit_store(body, Primitive::U8);
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
            let (size, _) = aggregate_layout(&layout.structs, &element)?;
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
            if let Some(identity) = struct_layout.error_identity {
                emit_address(body, frame, cell.offset);
                body.instruction(&WasmInstruction::I32Const(identity as i32));
                emit_store(body, Primitive::U32);
            }
            for (index, operand) in fields.iter().enumerate() {
                let destination = cell
                    .offset
                    .checked_add(struct_layout.offsets[index])
                    .ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                emit_address(body, frame, destination);
                emit_operand(body, function, param_count, operand, layout, Some(frame))?;
                match struct_layout.fields[index] {
                    FieldStorage::Primitive(kind) => emit_store(body, kind),
                    FieldStorage::Aggregate(size) => {
                        // A nested struct or array field is copied from its cell.
                        body.instruction(&WasmInstruction::I32Const(size as i32));
                        body.instruction(&WasmInstruction::MemoryCopy {
                            src_mem: 0,
                            dst_mem: 0,
                        });
                    }
                }
            }
        }
        InstructionKind::EnumNew {
            variant, payload, ..
        } => {
            let value = instruction.output.ok_or("enum creation lacks an output")?;
            let cell = array_cell_of(layout, Slot::Value(value.0))?;
            let frame = frame.ok_or("enum cell requires frame")?;
            let Type::Enum(type_id) = function.values[value.0 as usize] else {
                return Err("enum creation output must have an enum type".into());
            };
            let enum_type = layout
                .structs
                .get(type_id.0 as usize)
                .ok_or("enum type is out of range")?;
            let enum_layout = enum_type
                .enum_layout
                .as_ref()
                .ok_or("enum creation names a struct type")?;
            let variant_layout = enum_layout
                .variants
                .get(*variant as usize)
                .ok_or("enum creation refers to a missing variant")?;
            if variant_layout.offsets.len() != payload.len() {
                return Err("enum creation operand count differs from its variant".into());
            }
            // Payload operands are read before the tag is written, so building
            // into the destination cell never reads a half-written enum.
            for (index, operand) in payload.iter().enumerate() {
                let destination = cell
                    .offset
                    .checked_add(variant_layout.offsets[index])
                    .ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                emit_address(body, frame, destination);
                emit_operand(body, function, param_count, operand, layout, Some(frame))?;
                match variant_layout.fields[index] {
                    FieldStorage::Primitive(kind) => emit_store(body, kind),
                    FieldStorage::Aggregate(size) => {
                        body.instruction(&WasmInstruction::I32Const(size as i32));
                        body.instruction(&WasmInstruction::MemoryCopy {
                            src_mem: 0,
                            dst_mem: 0,
                        });
                    }
                }
            }
            if enum_layout.string_success && *variant == 0 {
                // The Result owns this descriptor until the consuming match.
                clear_moved_heap_source(
                    body,
                    function,
                    param_count,
                    &payload[0],
                    layout,
                    Some(frame),
                    heap_locals,
                )?;
            }
            emit_address(body, frame, cell.offset);
            body.instruction(&WasmInstruction::I32Const(*variant as i32));
            match enum_layout.tag_size {
                1 => emit_store(body, Primitive::U8),
                2 => emit_store(body, Primitive::U16),
                _ => emit_store(body, Primitive::U32),
            }
        }
        InstructionKind::Extract { base, field } => {
            let output = output.ok_or("field extraction lacks an output")?;
            let Type::Struct(type_id) = value_type(function, base)? else {
                return Err("field extraction base is not a struct".into());
            };
            let struct_layout = layout
                .structs
                .get(type_id.0 as usize)
                .ok_or("field extraction refers to a missing struct")?;
            let offset = *struct_layout
                .offsets
                .get(*field as usize)
                .ok_or("field extraction refers to a missing field")?;
            match struct_layout.fields[*field as usize] {
                FieldStorage::Primitive(kind) => {
                    emit_operand(body, function, param_count, base, layout, frame)?;
                    body.instruction(&WasmInstruction::I32Const(offset as i32));
                    body.instruction(&WasmInstruction::I32Add);
                    emit_load(body, kind);
                    body.instruction(&WasmInstruction::LocalSet(output));
                }
                FieldStorage::Aggregate(size) => {
                    // A nested struct or array moves into the output's own cell.
                    let cell = array_cell_of(layout, Slot::Value(instruction.output.unwrap().0))?;
                    let frame = frame.ok_or("aggregate cell requires frame")?;
                    emit_address(body, frame, cell.offset);
                    emit_operand(body, function, param_count, base, layout, Some(frame))?;
                    body.instruction(&WasmInstruction::I32Const(offset as i32));
                    body.instruction(&WasmInstruction::I32Add);
                    body.instruction(&WasmInstruction::I32Const(size as i32));
                    body.instruction(&WasmInstruction::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                }
            }
        }
        InstructionKind::EnumTag { base } => {
            let output = output.ok_or("enum tag lacks an output")?;
            let type_id = match value_type(function, base)? {
                Type::Enum(type_id) => type_id,
                Type::Reference { inner, .. } => match *inner {
                    Type::Enum(type_id) => type_id,
                    _ => return Err("enum tag base is not an enum".into()),
                },
                _ => return Err("enum tag base is not an enum".into()),
            };
            let enum_layout = layout
                .structs
                .get(type_id.0 as usize)
                .and_then(|enum_type| enum_type.enum_layout.as_ref())
                .ok_or("enum tag refers to a missing enum")?;
            emit_operand(body, function, param_count, base, layout, frame)?;
            match enum_layout.tag_size {
                1 => emit_load(body, Primitive::U8),
                2 => emit_load(body, Primitive::U16),
                _ => emit_load(body, Primitive::U32),
            }
            body.instruction(&WasmInstruction::LocalSet(output));
        }
        InstructionKind::VariantExtract {
            base,
            variant,
            field,
        } => {
            let output = output.ok_or("variant extraction lacks an output")?;
            let Type::Enum(type_id) = value_type(function, base)? else {
                return Err("variant extraction base is not an enum".into());
            };
            let enum_layout = layout
                .structs
                .get(type_id.0 as usize)
                .and_then(|enum_type| enum_type.enum_layout.as_ref())
                .ok_or("variant extraction refers to a missing enum")?;
            let variant_layout = enum_layout
                .variants
                .get(*variant as usize)
                .ok_or("variant extraction refers to a missing variant")?;
            if matches!(
                function.values[instruction.output.unwrap().0 as usize],
                Type::Reference { .. } | Type::String
            ) {
                // An inactive payload may contain arbitrary descriptor or reference bytes.
                emit_operand(body, function, param_count, base, layout, frame)?;
                emit_load(body, Primitive::U8); // Borrow Option and String Result have two variants
                body.instruction(&WasmInstruction::I32Const(*variant as i32));
                body.instruction(&WasmInstruction::I32Ne);
                body.instruction(&WasmInstruction::If(BlockType::Empty));
                body.instruction(&WasmInstruction::Unreachable);
                body.instruction(&WasmInstruction::End);
            }
            let offset = *variant_layout
                .offsets
                .get(*field as usize)
                .ok_or("variant extraction refers to a missing payload field")?;
            match variant_layout.fields[*field as usize] {
                FieldStorage::Primitive(kind) => {
                    emit_operand(body, function, param_count, base, layout, frame)?;
                    body.instruction(&WasmInstruction::I32Const(offset as i32));
                    body.instruction(&WasmInstruction::I32Add);
                    emit_load(body, kind);
                    body.instruction(&WasmInstruction::LocalSet(output));
                }
                FieldStorage::Aggregate(size) => {
                    let cell = array_cell_of(layout, Slot::Value(instruction.output.unwrap().0))?;
                    let frame = frame.ok_or("aggregate cell requires frame")?;
                    emit_address(body, frame, cell.offset);
                    emit_operand(body, function, param_count, base, layout, Some(frame))?;
                    body.instruction(&WasmInstruction::I32Const(offset as i32));
                    body.instruction(&WasmInstruction::I32Add);
                    body.instruction(&WasmInstruction::I32Const(size as i32));
                    body.instruction(&WasmInstruction::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                }
            }
        }
        InstructionKind::FieldAddr { base, field, .. } => {
            let output = output.ok_or("field address lacks an output")?;
            // The base is a struct owner (its operand is the cell address) or
            // a reference to a struct (its operand is the owner's address).
            let type_id = match value_type(function, base)? {
                Type::Struct(type_id) => type_id,
                Type::Reference { inner, .. } => match *inner {
                    Type::Struct(type_id) => type_id,
                    _ => return Err("field address base is not a struct".into()),
                },
                _ => return Err("field address base is not a struct".into()),
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
        InstructionKind::VariantAddr {
            base,
            variant,
            field,
            ..
        } => {
            let output = output.ok_or("variant address lacks an output")?;
            let type_id = match value_type(function, base)? {
                Type::Enum(type_id) => type_id,
                Type::Reference { inner, .. } => match *inner {
                    Type::Enum(type_id) => type_id,
                    _ => return Err("variant address base is not an enum".into()),
                },
                _ => return Err("variant address base is not an enum".into()),
            };
            let offset = layout
                .structs
                .get(type_id.0 as usize)
                .and_then(|enum_type| enum_type.enum_layout.as_ref())
                .and_then(|enum_layout| enum_layout.variants.get(*variant as usize))
                .and_then(|variant_layout| variant_layout.offsets.get(*field as usize))
                .copied()
                .ok_or("variant address refers to a missing payload field")?;
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
            let (size, _) = aggregate_layout(&layout.structs, &element)?;
            let wide = matches!(
                value_type(function, index)?,
                Type::Primitive(Primitive::I64 | Primitive::U64)
            );
            let site = traps.site(instruction.span);
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
            trap_if(body, site, TrapReason::IndexOutOfBounds);
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
            if let Type::Reference { inner, .. } = value_type(function, reference)? {
                if is_aggregate(&inner) {
                    let list = matches!(inner.as_ref(), Type::List(_));
                    let owns_heap = list || *inner == Type::String;
                    if owns_heap {
                        if let Some(copy) = heap_copy_index {
                            emit_operand(body, function, param_count, reference, layout, frame)?;
                            if list {
                                list_descriptor::load_allocation(body);
                            } else {
                                string_descriptor::load_allocation(body);
                            }
                            body.instruction(&WasmInstruction::Call(copy + 1));
                        }
                    }
                    // An error share can point at a descendant. Replace only the
                    // statically visible fields, keeping the object's identity.
                    let skip = match inner.as_ref() {
                        Type::Struct(id)
                            if layout.structs[id.0 as usize].error_identity.is_some() =>
                        {
                            entry_abi::ERROR_ID_BYTES
                        }
                        _ => 0,
                    };
                    for operand in [reference, value] {
                        emit_operand(body, function, param_count, operand, layout, frame)?;
                        if skip != 0 {
                            body.instruction(&WasmInstruction::I32Const(skip as i32));
                            body.instruction(&WasmInstruction::I32Add);
                        }
                    }
                    let size = aggregate_bytes(&layout.structs, &inner)? - skip;
                    body.instruction(&WasmInstruction::I32Const(size as i32));
                    body.instruction(&WasmInstruction::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                    if owns_heap {
                        clear_moved_heap_source(
                            body,
                            function,
                            param_count,
                            value,
                            layout,
                            frame,
                            heap_locals,
                        )?;
                    }
                    return Ok(());
                }
            }
            emit_operand(body, function, param_count, reference, layout, frame)?;
            emit_operand(body, function, param_count, value, layout, frame)?;
            emit_store(body, reference_primitive(function, reference)?);
        }
        InstructionKind::Assign {
            target,
            value,
            initialize,
        } => {
            if let Some(cell) = layout.arrays.get(&Slot::Local(target.0)).copied() {
                let list = matches!(function.locals[target.0 as usize].ty, Type::List(_));
                if !initialize && (list || heap_locals.contains(target)) {
                    // A self-move leaves the descriptor in the same slot.
                    if value.source == Source::Local(*target) {
                        return Ok(());
                    }
                    if list {
                        release_list_cell(body, cell, frame, heap_copy_index)?;
                    } else {
                        release_string_local(body, *target, layout, frame, heap_copy_index)?;
                    }
                }
                emit_array_copy(body, function, param_count, cell, value, layout, frame)?;
                clear_moved_heap_source(
                    body,
                    function,
                    param_count,
                    value,
                    layout,
                    frame,
                    heap_locals,
                )?;
                return Ok(());
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
            if is_aggregate(&function.values[id.0 as usize]) {
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
            let site = if *op == UnaryOp::Negate && is_integer(&ty) {
                traps.site(instruction.span)
            } else {
                traps.site(None)
            };
            emit_unary(
                body,
                *op,
                operand_local(function, param_count, operand)?,
                &ty,
                output,
                site,
            )?;
        }
        InstructionKind::Binary { op, left, right } => {
            let output = output.ok_or("binary operation lacks an output")?;
            let ty = value_type(function, left)?;
            refresh_operand(body, function, param_count, left, layout, frame)?;
            refresh_operand(body, function, param_count, right, layout, frame)?;
            let checked = matches!(
                op,
                BinaryOp::Add
                    | BinaryOp::Subtract
                    | BinaryOp::Multiply
                    | BinaryOp::Divide
                    | BinaryOp::Remainder
            ) && is_integer(&ty);
            let site = traps.site(if checked { instruction.span } else { None });
            emit_binary(
                body,
                *op,
                operand_local(function, param_count, left)?,
                operand_local(function, param_count, right)?,
                &ty,
                output,
                scratch64,
                site,
            )?;
        }
    }
    Ok(())
}

fn is_integer(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Primitive(
            Primitive::I8
                | Primitive::I16
                | Primitive::I32
                | Primitive::I64
                | Primitive::U8
                | Primitive::U16
                | Primitive::U32
                | Primitive::U64
        )
    )
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
        TerminatorKind::Switch {
            tag,
            targets,
            default,
            ..
        } => {
            // A compare chain over the tag: each listed variant tests the tag
            // and takes its edge; the default (or, when every variant is
            // listed and there is no default, the last target) is the fallthrough.
            let (tested, fallthrough) = match default {
                Some(edge) => (&targets[..], edge),
                None => {
                    let (last, rest) = targets
                        .split_last()
                        .ok_or("switch has neither targets nor a default")?;
                    (rest, &last.1)
                }
            };
            for (variant, edge) in tested {
                emit_operand(body, function, param_count, tag, layout, frame)?;
                body.instruction(&WasmInstruction::I32Const(*variant as i32));
                body.instruction(&WasmInstruction::I32Eq);
                body.instruction(&WasmInstruction::If(BlockType::Empty));
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
                body.instruction(&WasmInstruction::Br(2));
                body.instruction(&WasmInstruction::End);
            }
            emit_edge(
                body,
                function,
                fallthrough.target,
                &fallthrough.arguments,
                pc,
                param_count,
                layout,
                frame,
            )?;
            body.instruction(&WasmInstruction::Br(1));
        }
        TerminatorKind::Return(value) => {
            if let Some(value) = value {
                let ty = value_type(function, value)?;
                if is_aggregate(&ty) {
                    // Write the result through the hidden pointer parameter
                    // (the last Wasm parameter) before the frame is released.
                    body.instruction(&WasmInstruction::LocalGet(param_count - 1));
                    emit_operand(body, function, param_count, value, layout, frame)?;
                    body.instruction(&WasmInstruction::I32Const(aggregate_bytes(
                        &layout.structs,
                        &ty,
                    )? as i32));
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
    let is_array =
        |parameter: &memobits_ir::ValueId| is_aggregate(&function.values[parameter.0 as usize]);
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
        let wasm =
            encode_with_frame_sizes(&program, &exports, &[16, 32], DEFAULT_STACK_SIZE).unwrap();
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
        let wasm = encode_with_frame_sizes(&program, &exports, &[32752], 65520).unwrap();
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
            let bytes = encode_with_frame_sizes(&program, &exports, &[size], 65520).unwrap();
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
        let bytes =
            encode_with_frame_sizes(&program, &exports, &[16, 16], DEFAULT_STACK_SIZE).unwrap();
        let (mut store, instance) = instance(&bytes);
        let main = instance.get_typed_func::<(), ()>(&store, "main").unwrap();
        for _ in 0..3 {
            main.call(&mut store, ()).unwrap();
            assert_eq!(sp(&store, instance), 16);
        }
        let no_roots =
            encode_with_frame_sizes(&program, &BTreeMap::new(), &[16, 16], DEFAULT_STACK_SIZE)
                .unwrap();
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
            encode_with_frame_sizes(&program, &exports, &[0], DEFAULT_STACK_SIZE).unwrap()
        );
        assert!(!wasmparser::Parser::new(0)
            .parse_all(&normal)
            .any(|part| matches!(
                part.unwrap(),
                wasmparser::Payload::MemorySection(_) | wasmparser::Payload::GlobalSection(_)
            )));
        let private = encode_frames(&program, &exports, &[16], false, DEFAULT_STACK_SIZE).unwrap();
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
    fn nested_aggregates_are_laid_out_inline_with_their_own_alignment() {
        let program = lower(
            "type Q { a: u8, b: i64, f: f32, ok: Bool } \
             type R { tag: u8, q: Q, xs: Array<Q, 2>, last: i16 } \
             type Z { e: Array<Q, 0>, n: u8 } \
             type W { g: Array<Array<R, 2>, 3> } fn main() {}",
        );
        let layouts = struct_layouts(&program.types).unwrap();
        // Q: u8 @0, i64 @8, f32 @16, Bool @20; size 24, align 8.
        assert_eq!((layouts[0].size, layouts[0].align), (24, 8));
        assert_eq!(layouts[0].offsets, [0, 8, 16, 20]);
        // R: u8 @0, Q @8, [Q; 2] @32 (48 bytes), i16 @80; size 88, align 8.
        assert_eq!(layouts[1].offsets, [0, 8, 32, 80]);
        assert_eq!((layouts[1].size, layouts[1].align), (88, 8));
        assert_eq!(
            layouts[1].fields,
            [
                FieldStorage::Primitive(Primitive::U8),
                FieldStorage::Aggregate(24),
                FieldStorage::Aggregate(48),
                FieldStorage::Primitive(Primitive::I16)
            ]
        );
        // A zero-length array of structs is empty but keeps the element alignment.
        assert_eq!(layouts[2].offsets, [0, 0]);
        assert_eq!((layouts[2].size, layouts[2].align), (8, 8));
        // [[R; 2]; 3] is 3 * 2 * 88 bytes.
        assert_eq!(layouts[3].size, 528);
        // Overflow is reported, never wrapped.
        let huge = lower(
            "type P { x: i64 } type A { a: Array<Array<Array<P, 65536>, 65536>, 65536> } fn main() {}",
        );
        assert!(struct_layouts(&huge.types).is_err());
    }

    #[test]
    fn construction_writes_each_field_at_its_offset() {
        let program = lower(MIXED);
        let exports = BTreeMap::from([("main".to_string(), FunctionId(0))]);
        let structs = struct_layouts(&program.types).unwrap();
        let sizes = vec![
            FrameLayout::for_function_in(&structs, &program.functions[0], DEFAULT_STACK_SIZE)
                .unwrap()
                .size,
        ];
        let wasm = encode_with_frame_sizes(&program, &exports, &sizes, DEFAULT_STACK_SIZE).unwrap();
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

#[cfg(test)]
mod enum_layout_tests {
    use super::*;
    use wasmi::{Engine, Linker, Module, Store};

    fn lower(source: &str) -> Program {
        let parsed = memobits_syntax::parse(memobits_diagnostics::SourceId(0), source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        memobits_analysis::lower_module(&parsed.module, "test", &["main".into()]).unwrap()
    }

    fn layout_of(source: &str, name: &str) -> StructLayout {
        let program = lower(source);
        let layouts = struct_layouts(&program.types).unwrap();
        let index = program
            .types
            .iter()
            .position(|t| t.path.name == name)
            .unwrap();
        layouts[index].clone()
    }

    fn variants_of(layout: &StructLayout) -> &[VariantLayout] {
        &layout.enum_layout.as_ref().unwrap().variants
    }

    /// Test hook for the missing `match`: run `main` and return the first `len`
    /// bytes of the frame, where the first aggregate local's cell starts.
    fn frame_bytes(source: &str, len: usize) -> Vec<u8> {
        let program = lower(source);
        let exports = BTreeMap::from([("main".to_string(), FunctionId(0))]);
        let structs = struct_layouts(&program.types).unwrap();
        let sizes: Vec<u32> = program
            .functions
            .iter()
            .map(|f| {
                FrameLayout::for_function_in(&structs, f, DEFAULT_STACK_SIZE)
                    .unwrap()
                    .size
            })
            .collect();
        let wasm = encode_with_frame_sizes(&program, &exports, &sizes, DEFAULT_STACK_SIZE).unwrap();
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
        memory.data(&store)[FRAME_START as usize..FRAME_START as usize + len].to_vec()
    }

    #[test]
    fn unit_only_enums_are_just_a_tag() {
        let layout = layout_of("type E [ A, B, C ] fn main() {}", "E");
        assert_eq!((layout.size, layout.align), (1, 1));
        assert_eq!(layout.enum_layout.as_ref().unwrap().tag_size, 1);
        assert!(variants_of(&layout).iter().all(|v| v.offsets.is_empty()));
    }

    #[test]
    fn tag_width_is_the_smallest_that_fits_the_variant_count() {
        let make = |count: usize| {
            let variants = (0..count)
                .map(|i| format!("V{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            layout_of(&format!("type E [ {variants} ] fn main() {{}}"), "E")
        };
        for (count, tag, size) in [
            (1, 1, 1),
            (256, 1, 1),
            (257, 2, 2),
            (300, 2, 2),
            (65536, 2, 2),
        ] {
            let layout = make(count);
            assert_eq!(
                layout.enum_layout.as_ref().unwrap().tag_size,
                tag,
                "{count}"
            );
            assert_eq!((layout.size, layout.align), (size, size), "{count}");
        }
        assert_eq!(make(65537).enum_layout.unwrap().tag_size, 4);
    }

    #[test]
    fn payload_area_follows_the_tag_at_the_maximum_payload_alignment() {
        // tag @0; the widest payload alignment (i64) puts every payload at 8.
        let layout = layout_of("type M [ A(u8), B(u16), C(u8, i64), D ] fn main() {}", "M");
        let variants = variants_of(&layout);
        assert_eq!(variants[0].offsets, [8]);
        assert_eq!(variants[1].offsets, [8]);
        assert_eq!(variants[2].offsets, [8, 16]);
        assert!(variants[3].offsets.is_empty());
        assert_eq!((layout.size, layout.align), (24, 8));
        // A u16 payload starts at 2, not 1.
        let layout = layout_of("type U [ A(u16), B ] fn main() {}", "U");
        assert_eq!(variants_of(&layout)[0].offsets, [2]);
        assert_eq!((layout.size, layout.align), (4, 2));
        // Byte payloads pack right after the tag.
        let layout = layout_of("type T [ A(u8), B(u8, u8) ] fn main() {}", "T");
        assert_eq!(variants_of(&layout)[1].offsets, [1, 2]);
        assert_eq!((layout.size, layout.align), (3, 1));
        // A wide tag shares the area with a narrow payload: tag 2 bytes, u8 at 2.
        let variants = (0..300)
            .map(|i| {
                if i == 0 {
                    "V0(u8)".into()
                } else {
                    format!("V{i}")
                }
            })
            .collect::<Vec<String>>()
            .join(", ");
        let layout = layout_of(&format!("type W [ {variants} ] fn main() {{}}"), "W");
        assert_eq!(variants_of(&layout)[0].offsets, [2]);
        assert_eq!((layout.size, layout.align), (4, 2));
    }

    #[test]
    fn nested_aggregates_use_their_own_size_and_alignment() {
        let layout = layout_of(
            "type P { x: i32, y: i32 } type Shape [ Empty, Circle(f64), Rect(i32, i32), \
             Poly(P, Array<u8, 3>) ] fn main() {}",
            "Shape",
        );
        let variants = variants_of(&layout);
        assert_eq!(variants[1].offsets, [8]);
        assert_eq!(variants[2].offsets, [8, 12]);
        assert_eq!(variants[3].offsets, [8, 16]);
        assert_eq!(
            variants[3].fields,
            [FieldStorage::Aggregate(8), FieldStorage::Aggregate(3)]
        );
        // Largest variant is Poly: 16 + 3 = 19, rounded to the alignment 8.
        assert_eq!((layout.size, layout.align), (24, 8));
        // An enum inside an enum, and an array of enums, stride by the enum size.
        let program =
            lower("type In [ X(i16), Y ] type Out [ A(In), B(Array<In, 3>) ] fn main() {}");
        let layouts = struct_layouts(&program.types).unwrap();
        assert_eq!((layouts[0].size, layouts[0].align), (4, 2));
        assert_eq!(
            layouts[1].enum_layout.as_ref().unwrap().variants[1].offsets,
            [2]
        );
        assert_eq!((layouts[1].size, layouts[1].align), (14, 2));
    }

    #[test]
    fn layout_arithmetic_is_checked() {
        let program =
            lower("type Huge [ A(Array<Array<Array<i64, 65536>, 65536>, 65536>) ] fn main() {}");
        assert!(struct_layouts(&program.types).is_err());
    }

    #[test]
    fn construction_writes_the_tag_and_the_payload_at_their_offsets() {
        let bytes = frame_bytes(
            "type Shape [ Empty, Circle(f64), Rect(i32, i32) ] \
             fn main() -> i32 { let s := Shape::Rect(7, -9); 1 }",
            16,
        );
        assert_eq!(bytes[0], 2);
        assert_eq!(i32::from_le_bytes(bytes[8..12].try_into().unwrap()), 7);
        assert_eq!(i32::from_le_bytes(bytes[12..16].try_into().unwrap()), -9);
        let bytes = frame_bytes(
            "type Shape [ Empty, Circle(f64), Rect(i32, i32) ] \
             fn main() -> i32 { let s := Shape::Circle(1.5); 1 }",
            16,
        );
        assert_eq!(bytes[0], 1);
        assert_eq!(f64::from_le_bytes(bytes[8..16].try_into().unwrap()), 1.5);
        let bytes = frame_bytes(
            "type Shape [ Empty, Circle(f64) ] fn main() -> i32 { let s := Shape::Empty; 1 }",
            1,
        );
        assert_eq!(bytes[0], 0);
    }

    #[test]
    fn a_300_variant_enum_stores_a_u16_tag() {
        let variants = (0..300)
            .map(|i| format!("V{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let bytes = frame_bytes(
            &format!("type Big [ {variants} ] fn main() -> i32 {{ let b := Big::V299; 1 }}"),
            2,
        );
        assert_eq!(u16::from_le_bytes(bytes[0..2].try_into().unwrap()), 299);
    }

    #[test]
    fn nested_payloads_land_inside_the_outer_payload_area() {
        // `In` is 4 bytes (tag @0, i16 @2, align 2); `Out` stores that cell at
        // its own payload offset 2.
        let bytes = frame_bytes(
            "type In [ X(i16), Y ] type Out [ A(In), B(u8) ] \
             fn main() -> i32 { let o := Out::A(In::X(1234)); 1 }",
            8,
        );
        // Out: tag A = 0 @0, In @2 (size 4, align 2): In tag X = 0 @2, i16 @4.
        assert_eq!(bytes[0], 0);
        assert_eq!(bytes[2], 0);
        assert_eq!(i16::from_le_bytes(bytes[4..6].try_into().unwrap()), 1234);
    }
}
