//! Owned function types. A function type `fn(...) -> R` is a plain scalar
//! (a table slot plus an environment word) until a closure literal that
//! captures variables by move is written where such a type is expected. From
//! then on every value of that exact function type is represented as a wrapper
//! struct `{ call, env }`: `call` is the scalar callable word and `env` owns
//! the heap environment (an empty box for a plain function). The wrapper and
//! its environment enum live in the type table; this module decides which
//! function types use them. Checking runs in passes: the first pass discovers
//! the owned function types, later passes use the wrapper.
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use memobits_diagnostics::Span;

use super::typetable::TypeTable;
use super::Ty;

#[derive(Default)]
struct State {
    owned: BTreeSet<String>,
    grew: bool,
    table: Option<Rc<TypeTable>>,
}

thread_local! {
    static STATE: RefCell<State> = RefCell::new(State::default());
}

/// Start a checking run: no owned function types are known yet.
pub(super) fn reset() {
    STATE.with(|state| {
        *state.borrow_mut() = State::default();
    });
}

/// Forget the run's state (and the table it holds).
pub(super) fn finish() {
    STATE.with(|state| *state.borrow_mut() = State::default());
}

/// The table of the pass that is about to run.
pub(super) fn set_table(table: Rc<TypeTable>) {
    STATE.with(|state| state.borrow_mut().table = Some(table));
}

/// Whether the last pass found an owned function type that was not known, which
/// means another pass is needed.
pub(super) fn take_grew() -> bool {
    STATE.with(|state| std::mem::take(&mut state.borrow_mut().grew))
}

/// Record that a closure with captures was written for this function type.
pub(super) fn discover(function: &Ty) {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(table) = state.table.clone() else {
            return;
        };
        let key = table.stable_identity(function);
        if state.owned.insert(key) {
            state.grew = true;
        }
    });
}

/// The environment variant index for a closure literal of the owned function
/// type `function`, if that type is owned in this pass.
pub(super) fn add_variant(function: &Ty, payload: Vec<Ty>) -> Option<(u32, u32, u32)> {
    let (table, key) = lookup(function)?;
    let (wrapper, env) = table.closure_types(&key, function, span());
    let variant = table.add_closure_variant(&key, payload);
    Some((wrapper, env, variant))
}

fn span() -> Span {
    Span {
        source: memobits_diagnostics::SourceId(0),
        start: 0,
        end: 0,
    }
}

fn lookup(function: &Ty) -> Option<(Rc<TypeTable>, String)> {
    STATE.with(|state| {
        let state = state.borrow();
        let table = state.table.clone()?;
        let key = table.stable_identity(function);
        state.owned.contains(&key).then_some((table, key))
    })
}

/// The wrapper struct id of `function` when it is an owned function type.
pub(super) fn wrapper_id(function: &Ty) -> Option<u32> {
    let (table, key) = lookup(function)?;
    Some(table.closure_types(&key, function, span()).0)
}

/// Whether the struct `id` is the wrapper of an owned function type.
pub(super) fn is_wrapper(id: u32) -> bool {
    STATE.with(|state| {
        state.borrow().table.as_ref().is_some_and(|table| {
            let info = table.info(id);
            info.module == "\0tuple" && info.name.starts_with("fn(")
        })
    })
}
