//! Out-of-line release functions for recursive owner types.
//!
//! A type that reaches itself through a `List` or `Box` element (a tree whose
//! nodes hold boxed children) cannot have its release code emitted inline: the
//! type-directed walk would never end. Each such type gets one Wasm function
//! that releases a value of the type at an address; every release site calls
//! it, and the function calls itself for the recursive positions.

use super::*;
use std::cell::{Cell, RefCell};

struct Table {
    ids: Vec<u32>,
    base: u32,
}

thread_local! {
    static TABLE: RefCell<Option<Table>> = const { RefCell::new(None) };
    static BODY: Cell<Option<u32>> = const { Cell::new(None) };
}

/// Types that reach themselves and hold heap storage, in id order.
pub(super) fn recursive_types(types: &[TypeDef]) -> Vec<u32> {
    fn children(ty: &Type, out: &mut Vec<u32>) {
        match ty {
            Type::Struct(id) | Type::Enum(id) => out.push(id.0),
            Type::Array { element, .. } | Type::List(element) => children(element, out),
            _ => {}
        }
    }
    let direct = |id: u32| {
        let mut out = Vec::new();
        match types.get(id as usize).map(|definition| &definition.kind) {
            Some(TypeDefKind::Struct { fields }) => {
                for field in fields {
                    children(&field.ty, &mut out);
                }
            }
            Some(TypeDefKind::Enum { variants }) => {
                for payload in variants.iter().flat_map(|variant| &variant.payload) {
                    children(payload, &mut out);
                }
            }
            None => {}
        }
        out
    };
    (0..types.len() as u32)
        .filter(|id| {
            let mut seen = HashSet::new();
            let mut pending = direct(*id);
            while let Some(next) = pending.pop() {
                if next == *id {
                    return true;
                }
                if seen.insert(next) {
                    pending.extend(direct(next));
                }
            }
            false
        })
        .filter(|id| {
            let ty = match &types[*id as usize].kind {
                TypeDefKind::Struct { .. } => Type::Struct(memobits_ir::TypeId(*id)),
                TypeDefKind::Enum { .. } => Type::Enum(memobits_ir::TypeId(*id)),
            };
            type_has_string_storage(types, &ty)
        })
        .collect()
}

/// Keep the table installed for the duration of one encode; dropped on exit.
pub(super) struct Installed;

impl Drop for Installed {
    fn drop(&mut self) {
        TABLE.with(|table| *table.borrow_mut() = None);
        BODY.with(|body| body.set(None));
    }
}

pub(super) fn install(ids: Vec<u32>, base: u32) -> Installed {
    TABLE.with(|table| *table.borrow_mut() = Some(Table { ids, base }));
    Installed
}

/// Wasm function index of the release function of type `id`.
pub(super) fn function_index(id: u32) -> Option<u32> {
    TABLE.with(|table| {
        let table = table.borrow();
        let table = table.as_ref()?;
        let position = table.ids.iter().position(|candidate| *candidate == id)?;
        Some(table.base + position as u32)
    })
}

/// The type whose own release body is being emitted; its top level is inline.
pub(super) fn take_body() -> Option<u32> {
    BODY.with(Cell::take)
}

/// Whether `ty` is a recursive owner type with a release function.
pub(super) fn is_recursive(ty: &Type) -> Option<u32> {
    match ty {
        Type::Struct(id) | Type::Enum(id) => function_index(id.0).map(|_| id.0),
        _ => None,
    }
}

/// The release function body of recursive type `id`: parameter 0 is the
/// address of the value.
pub(super) fn body(
    types: &[TypeDef],
    structs: &[StructLayout],
    id: u32,
    heap_copy_index: Option<u32>,
) -> Result<WasmFunction, String> {
    let ty = match &types[id as usize].kind {
        TypeDefKind::Struct { .. } => Type::Struct(memobits_ir::TypeId(id)),
        TypeDefKind::Enum { .. } => Type::Enum(memobits_ir::TypeId(id)),
    };
    let depth = max_string_array_depth(types, &ty, &mut HashSet::new());
    let local_count = 1 + depth.saturating_mul(2);
    let mut function = WasmFunction::new([(local_count as u32, ValType::I32)]);
    BODY.with(|body| body.set(Some(id)));
    emit_string_storage_cleanup(
        &mut function,
        types,
        structs,
        &ty,
        0,
        0,
        1,
        0,
        heap_copy_index,
        true,
    )?;
    BODY.with(|body| body.set(None));
    function.instruction(&WasmInstruction::End);
    Ok(function)
}
