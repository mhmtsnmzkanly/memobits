//! Out-of-line, iterative release of recursive owner types.
//!
//! A type that reaches itself through a `List` or `Box` element (a tree whose
//! nodes hold boxed children) cannot have its release code emitted inline: the
//! type-directed walk would never end. Each such type gets one Wasm function
//! `release_T(address)` that releases a value of the type at an address; every
//! release site calls it.
//!
//! The release never recurses per node. `release_T` walks the value's own
//! fields inline ("work mode"); a `List` (or box) position whose element
//! mentions a recursive type is not walked but *deferred*: its descriptor is
//! pushed on an intrusive worklist and the shared `drain` function pops and
//! processes the items in a loop.
//!
//! * One worklist (a Wasm global holding the head, 0 when empty) exists per
//!   deferral kind (container + element type).
//! * A deferred List item is its 12-byte descriptor. A heap List block always
//!   has `data == allocation + HEADER_BYTES`, so the `data` word is free to be
//!   the link while the item waits and is restored when it is popped. A
//!   descriptor with no allocation owns nothing and is not pushed.
//! * Releasing never allocates, so the memory of a block freed early (header
//!   words only are touched by the free list) still holds the descriptors
//!   that were deferred out of it.
//! * `drain` runs `loop { pop one item of any kind; walk its elements inline
//!   (pushing deeper items); free its block }` until every list is empty.
//!
//! Call-stack bound: user code -> `release_T` -> `drain`; neither calls
//! another release function or itself, because work mode walks every struct,
//! enum and array inline (by-value recursion is rejected, so those walks
//! end) and defers every recursive position. The depth is constant, and the
//! extra memory is zero (the links live in dead descriptors).

use super::*;
use std::cell::{Cell, RefCell};

struct Table {
    ids: Vec<u32>,
    base: u32,
}

thread_local! {
    static TABLE: RefCell<Option<Table>> = const { RefCell::new(None) };
    static WORK: Cell<bool> = const { Cell::new(false) };
    /// Deferred container kinds (is a box, element type), in registration order.
    static KINDS: RefCell<Vec<(bool, Type)>> = const { RefCell::new(Vec::new()) };
}

/// Index of the first worklist head global (after the five fixed globals).
const FIRST_HEAD_GLOBAL: u32 = 5;

/// Types that reach themselves and hold heap storage, in id order.
pub(super) fn recursive_types(types: &[TypeDef]) -> Vec<u32> {
    fn children(ty: &Type, out: &mut Vec<u32>) {
        match ty {
            Type::Struct(id) | Type::Enum(id) => out.push(id.0),
            Type::Array { element, .. } | Type::List(element) | Type::Box(element) => {
                children(element, out)
            }
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
        WORK.with(|work| work.set(false));
        KINDS.with(|kinds| kinds.borrow_mut().clear());
    }
}

pub(super) fn install(ids: Vec<u32>, base: u32) -> Installed {
    TABLE.with(|table| *table.borrow_mut() = Some(Table { ids, base }));
    WORK.with(|work| work.set(false));
    KINDS.with(|kinds| kinds.borrow_mut().clear());
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

/// Wasm function index of the shared worklist drain function.
pub(super) fn drain_index() -> u32 {
    TABLE.with(|table| {
        let table = table.borrow();
        let table = table.as_ref().expect("installed recursive table");
        table.base + table.ids.len() as u32
    })
}

/// Whether the release walk being emitted is a work-mode walk (inside a
/// release function or the drain function).
pub(super) fn work_mode() -> bool {
    WORK.with(Cell::get)
}

/// Whether `ty` is a recursive owner type with a release function.
pub(super) fn is_recursive(ty: &Type) -> Option<u32> {
    match ty {
        Type::Struct(id) | Type::Enum(id) => function_index(id.0).map(|_| id.0),
        _ => None,
    }
}

/// Whether releasing a List of `element` must defer its elements: the element
/// type mentions a recursive type, so an inline walk could be unbounded.
pub(super) fn defers(types: &[TypeDef], element: &Type) -> bool {
    fn mentions(types: &[TypeDef], ids: &[u32], ty: &Type, visiting: &mut HashSet<u32>) -> bool {
        match ty {
            Type::Struct(id) | Type::Enum(id) => {
                if ids.contains(&id.0) {
                    return true;
                }
                if !visiting.insert(id.0) {
                    return false;
                }
                let found = match types.get(id.0 as usize).map(|definition| &definition.kind) {
                    Some(TypeDefKind::Struct { fields }) => fields
                        .iter()
                        .any(|field| mentions(types, ids, &field.ty, visiting)),
                    Some(TypeDefKind::Enum { variants }) => variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|field| mentions(types, ids, field, visiting)),
                    None => false,
                };
                visiting.remove(&id.0);
                found
            }
            Type::Array { element, .. } | Type::List(element) | Type::Box(element) => {
                mentions(types, ids, element, visiting)
            }
            _ => false,
        }
    }
    TABLE.with(|table| {
        let table = table.borrow();
        let Some(table) = table.as_ref() else {
            return false;
        };
        mentions(types, &table.ids, element, &mut HashSet::new())
    })
}

/// The worklist head global of the kind (box or List) with element `element`.
pub(super) fn head_global(boxed: bool, element: &Type) -> u32 {
    KINDS.with(|kinds| {
        let mut kinds = kinds.borrow_mut();
        let position = kinds
            .iter()
            .position(|(kind_boxed, kind)| *kind_boxed == boxed && kind == element);
        let position = position.unwrap_or_else(|| {
            kinds.push((boxed, element.clone()));
            kinds.len() - 1
        });
        FIRST_HEAD_GLOBAL + position as u32
    })
}

/// Number of worklist head globals the emitted code needs; valid once every
/// release function and the drain function have been emitted.
pub(super) fn head_count() -> u32 {
    KINDS.with(|kinds| kinds.borrow().len() as u32)
}

/// The release function body of recursive type `id`: parameter 0 is the
/// address of the value. Its own fields are walked inline; deferred positions
/// are drained before it returns.
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
    WORK.with(|work| work.set(true));
    let walked = emit_string_storage_cleanup(
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
    );
    WORK.with(|work| work.set(false));
    walked?;
    function.instruction(&WasmInstruction::Call(drain_index()));
    function.instruction(&WasmInstruction::End);
    Ok(function)
}

/// The shared drain function: pops deferred items of every kind until all
/// worklists are empty. Emitted last, because walking an item can register
/// further kinds.
pub(super) fn drain(
    types: &[TypeDef],
    structs: &[StructLayout],
    heap_copy_index: Option<u32>,
) -> Result<WasmFunction, String> {
    let releaser = heap_copy_index.ok_or("missing heap helpers for recursive release")? + 1;
    // Local 0 is the popped descriptor; nested element walks use the rest.
    // The first pass discovers the kinds (and so the depth); the second emits
    // with the final local count.
    let mut local_count = 8u32;
    for _ in 0..2 {
        let mut function = WasmFunction::new([(local_count, ValType::I32)]);
        WORK.with(|work| work.set(true));
        let emitted = (|| {
            function.instruction(&WasmInstruction::Loop(BlockType::Empty));
            let mut index = 0;
            while let Some((boxed, element)) =
                KINDS.with(|kinds| kinds.borrow().get(index).cloned())
            {
                let head = FIRST_HEAD_GLOBAL + index as u32;
                function.instruction(&WasmInstruction::GlobalGet(head));
                function.instruction(&WasmInstruction::LocalTee(0));
                function.instruction(&WasmInstruction::If(BlockType::Empty));
                if boxed {
                    // Item: the block. Unlink through its free-list word; its
                    // content sits after the header.
                    function.instruction(&WasmInstruction::LocalGet(0));
                    function.instruction(&WasmInstruction::I32Load(string_heap::header_field(
                        string_heap::NEXT_OFFSET,
                    )));
                    function.instruction(&WasmInstruction::GlobalSet(head));
                    function.instruction(&WasmInstruction::LocalGet(0));
                    function.instruction(&WasmInstruction::I32Const(box_cell::CONTENT_OFFSET));
                    function.instruction(&WasmInstruction::I32Add);
                    function.instruction(&WasmInstruction::LocalSet(1));
                    emit_string_storage_cleanup(
                        &mut function,
                        types,
                        structs,
                        &element,
                        1,
                        0,
                        2,
                        0,
                        heap_copy_index,
                        true,
                    )?;
                    function.instruction(&WasmInstruction::LocalGet(0));
                } else {
                    // Item: the descriptor. Unlink through its data word and
                    // restore it.
                    function.instruction(&WasmInstruction::LocalGet(0));
                    list_descriptor::load_address(&mut function);
                    function.instruction(&WasmInstruction::GlobalSet(head));
                    function.instruction(&WasmInstruction::LocalGet(0));
                    function.instruction(&WasmInstruction::LocalGet(0));
                    list_descriptor::load_allocation(&mut function);
                    function.instruction(&WasmInstruction::I32Const(string_heap::HEADER_BYTES));
                    function.instruction(&WasmInstruction::I32Add);
                    list_descriptor::store_address(&mut function);
                    emit_list_elements_cleanup(
                        &mut function,
                        types,
                        structs,
                        &element,
                        0,
                        0,
                        2,
                        0,
                        heap_copy_index,
                    )?;
                    function.instruction(&WasmInstruction::LocalGet(0));
                    list_descriptor::load_allocation(&mut function);
                }
                function.instruction(&WasmInstruction::Call(releaser));
                function.instruction(&WasmInstruction::Br(1));
                function.instruction(&WasmInstruction::End);
                index += 1;
            }
            function.instruction(&WasmInstruction::End);
            function.instruction(&WasmInstruction::End);
            Ok::<(), String>(())
        })();
        WORK.with(|work| work.set(false));
        emitted?;
        let depth = KINDS.with(|kinds| {
            kinds
                .borrow()
                .iter()
                .map(|(_, element)| max_string_array_depth(types, element, &mut HashSet::new()))
                .max()
                .unwrap_or(0)
        });
        let needed = 8 + (depth as u32 + 2) * 2;
        if needed <= local_count {
            return Ok(function);
        }
        local_count = needed;
    }
    Err("recursive release local count did not settle".into())
}
