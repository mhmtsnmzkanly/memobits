//! Scope zinciri ve binding yönetimi.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::value::Value;

#[derive(Clone, Default)]
pub struct Environment {
    bindings: HashMap<String, Binding>,
    parent: Option<Rc<RefCell<Environment>>>,
}

#[derive(Clone)]
pub struct Binding {
    pub value: Value,
    pub mutable: bool,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_parent(parent: Rc<RefCell<Environment>>) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(parent),
        }
    }

    pub fn define(&mut self, name: impl Into<String>, value: Value, mutable: bool) {
        self.bindings.insert(
            name.into(),
            Binding { value, mutable },
        );
    }

    pub fn set(&mut self, name: &str, value: Value) -> bool {
        if let Some(b) = self.bindings.get_mut(name) {
            if b.mutable {
                b.value = value;
                return true;
            }
            return false;
        }
        if let Some(ref p) = self.parent {
            return p.borrow_mut().set(name, value);
        }
        false
    }

    pub fn get(&self, name: &str) -> Option<Value> {
        self.bindings.get(name).map(|b| b.value.clone()).or_else(|| {
            self.parent
                .as_ref()
                .and_then(|p| p.borrow().get(name))
        })
    }

}
