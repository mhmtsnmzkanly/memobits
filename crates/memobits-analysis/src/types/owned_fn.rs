//! Owned function values. Every function type `fn(...) -> R` (and
//! `var fn(...) -> R`) is represented the same way, whatever else the program
//! contains: a wrapper struct `{ call, env }` in the type table. `call` is the
//! scalar callable word (a table slot plus an environment word) and `env` owns
//! the heap environment, a box of the environment enum of the function type.
//! The box is empty (no heap) for a function name, a literal without captures
//! and a second-class closure, so releasing such a value is a no-op check.
//! Both spellings of a signature share one wrapper: `var` is a checker-only
//! property that says the environment may change when the value is called.
use std::cell::RefCell;
use std::rc::Rc;

use memobits_diagnostics::Span;

use super::typetable::TypeTable;
use super::Ty;

thread_local! {
    static TABLE: RefCell<Option<Rc<TypeTable>>> = const { RefCell::new(None) };
}

/// The table of the check that is about to run.
pub(super) fn set_table(table: Rc<TypeTable>) {
    TABLE.with(|state| *state.borrow_mut() = Some(table));
}

/// Forget the table of the finished check.
pub(super) fn finish() {
    TABLE.with(|state| *state.borrow_mut() = None);
}

fn span() -> Span {
    Span {
        source: memobits_diagnostics::SourceId(0),
        start: 0,
        end: 0,
    }
}

/// The wrapper identity of a function type: its signature without `var`.
fn lookup(function: &Ty) -> Option<(Rc<TypeTable>, String, Ty)> {
    let Ty::Function(parameters, result, _) = function else {
        return None;
    };
    let table = TABLE.with(|state| state.borrow().clone())?;
    let plain = Ty::Function(parameters.clone(), result.clone(), false);
    let key = table.stable_identity(&plain);
    Some((table, key, plain))
}

/// The environment variant index for a closure literal of the function type
/// `function`: the wrapper struct, the environment enum and the variant.
pub(super) fn add_variant(function: &Ty, payload: Vec<Ty>) -> Option<(u32, u32, u32)> {
    let (table, key, plain) = lookup(function)?;
    let (wrapper, env) = table.closure_types(&key, &plain, span());
    let variant = table.add_closure_variant(&key, payload);
    Some((wrapper, env, variant))
}

/// The wrapper struct id of the function type `function`.
pub(super) fn wrapper_id(function: &Ty) -> Option<u32> {
    let (table, key, plain) = lookup(function)?;
    Some(table.closure_types(&key, &plain, span()).0)
}

/// Whether the struct `id` is the wrapper of a function type.
pub(super) fn is_wrapper(id: u32) -> bool {
    TABLE.with(|state| {
        state.borrow().as_ref().is_some_and(|table| {
            let info = table.info(id);
            info.module == "\0tuple" && info.name.starts_with("fn(")
        })
    })
}
