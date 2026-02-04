//! Scope zinciri ve binding yönetimi.

use alloc::rc::Rc;
use alloc::string::String;
use core::cell::RefCell;
use crate::collections::HashMap;

use crate::value::{EnvRef, Value};

#[derive(Clone, Default)]
pub struct Environment {
    bindings: HashMap<String, Binding>,
    parent: Option<Rc<RefCell<Environment>>>,
    captured: Option<EnvRef>,
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
        let captured = parent.borrow().captured.clone();
        Self {
            bindings: HashMap::new(),
            parent: Some(parent),
            captured,
        }
    }

    pub fn with_captured(captured: EnvRef) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
            captured: Some(captured),
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
        if let Some(ref cap) = self.captured {
            if cap.contains_key(name) {
                return false;
            }
        }
        false
    }

    pub fn get(&self, name: &str) -> Option<Value> {
        if let Some(b) = self.bindings.get(name) {
            return Some(b.value.clone());
        }
        if let Some(ref p) = self.parent {
            if let Some(v) = p.borrow().get(name) {
                return Some(v);
            }
        }
        if let Some(ref cap) = self.captured {
            return cap.get(name).cloned();
        }
        None
    }

    pub fn snapshot(&self) -> EnvRef {
        let mut out = HashMap::new();
        self.fill_snapshot(&mut out);
        Rc::new(out)
    }

    fn fill_snapshot(&self, out: &mut HashMap<String, Value>) {
        if let Some(ref p) = self.parent {
            p.borrow().fill_snapshot(out);
        }
        if let Some(ref cap) = self.captured {
            for (k, v) in cap.iter() {
                out.entry(k.clone()).or_insert_with(|| v.clone());
            }
        }
        for (k, b) in self.bindings.iter() {
            out.insert(k.clone(), b.value.clone());
        }
    }
}
