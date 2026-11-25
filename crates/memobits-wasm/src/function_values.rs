//! Function values. A function value is two 32-bit words packed in one `i64`:
//! the low word is the slot in the module's function table (slot 0 is never
//! filled, so a zero or stale value traps), the high word is the environment
//! pointer: 0 for a function without captures, else the address of the
//! closure's environment record in its creator's frame (one 32-bit capture
//! address per captured place, in capture order). Packing keeps the value a
//! plain scalar everywhere (locals, struct fields, array and List elements,
//! enum payloads).
//!
//! Calling convention (every indirect call, one convention): the callee's
//! Wasm type is the declared parameters, then one `i32` environment pointer,
//! then (for an array/struct result) the hidden result pointer. Table entries
//! are thunks with that type: the thunk of a plain function drops the
//! environment and calls the function; the thunk of a closure loads one
//! capture address per capture from the environment and calls the lifted
//! closure function, whose own parameters are the declared ones followed by
//! one borrow/share reference per capture. Direct calls never see any of it.
//!
//! Before encoding, every function type in the program is erased to `u64`;
//! the signature of each indirect call is recorded on the side, keyed by the
//! call's output value, for `call_indirect`.
use super::*;
use memobits_ir::Signature;

/// The program with function types erased, plus the signature of each
/// indirect call (per function: output value to erased signature).
pub(super) struct Erased {
    pub(super) program: Program,
    pub(super) calls: Vec<HashMap<u32, Signature>>,
}

fn erase_type(ty: &Type) -> Type {
    match ty {
        Type::Function(_) => Type::Primitive(Primitive::U64),
        Type::List(element) => Type::List(Box::new(erase_type(element))),
        Type::Box(element) => Type::Box(Box::new(erase_type(element))),
        Type::Array { element, len } => Type::Array {
            element: Box::new(erase_type(element)),
            len: *len,
        },
        Type::Reference { access, inner } => Type::Reference {
            access: *access,
            inner: Box::new(erase_type(inner)),
        },
        other => other.clone(),
    }
}

pub(super) fn erase_signature(signature: &Signature) -> Signature {
    Signature {
        parameters: signature
            .parameters
            .iter()
            .map(|parameter| memobits_ir::ParameterType {
                access: parameter.access,
                ty: erase_type(&parameter.ty),
            })
            .collect(),
        result: Box::new(erase_type(&signature.result)),
    }
}

pub(super) fn contains_function(ty: &Type) -> bool {
    match ty {
        Type::Function(_) => true,
        Type::List(inner) | Type::Box(inner) | Type::Reference { inner, .. } => {
            contains_function(inner)
        }
        Type::Array { element, .. } => contains_function(element),
        _ => false,
    }
}

/// Whether a signature mentions a function value anywhere.
pub(super) fn signature_has_function(signature: &Signature) -> bool {
    signature
        .parameters
        .iter()
        .any(|parameter| contains_function(&parameter.ty))
        || contains_function(&signature.result)
}

pub(super) fn erase(program: &Program) -> Erased {
    let mut erased = program.clone();
    for definition in &mut erased.types {
        match &mut definition.kind {
            TypeDefKind::Struct { fields } => {
                for field in fields {
                    field.ty = erase_type(&field.ty);
                }
            }
            TypeDefKind::Enum { variants } => {
                for variant in variants {
                    for ty in &mut variant.payload {
                        *ty = erase_type(ty);
                    }
                }
            }
        }
    }
    let mut calls = Vec::with_capacity(program.functions.len());
    for (original, function) in program.functions.iter().zip(&mut erased.functions) {
        let mut indirect = HashMap::new();
        for block in &original.blocks {
            for instruction in &block.instructions {
                let InstructionKind::Call { callee, .. } = &instruction.kind else {
                    continue;
                };
                if matches!(callee.source, Source::Function(_)) {
                    continue;
                }
                let ty = match callee.source {
                    Source::Local(local) => original.locals.get(local.0 as usize).map(|l| &l.ty),
                    Source::Value(value) => original.values.get(value.0 as usize),
                    Source::Function(_) => None,
                };
                if let (Some(Type::Function(signature)), Some(output)) = (ty, instruction.output) {
                    indirect.insert(output.0, erase_signature(signature));
                }
            }
        }
        calls.push(indirect);
        function.signature = erase_signature(&function.signature);
        for local in &mut function.locals {
            local.ty = erase_type(&local.ty);
        }
        for ty in &mut function.values {
            *ty = erase_type(ty);
        }
    }
    Erased {
        program: erased,
        calls,
    }
}

/// The signature of an indirect call or thunk: the declared signature plus the
/// trailing environment pointer.
pub(super) fn with_environment(signature: &Signature) -> Signature {
    let mut parameters = signature.parameters.clone();
    parameters.push(memobits_ir::ParameterType {
        access: memobits_ir::Access::Owned,
        ty: Type::Primitive(Primitive::U32),
    });
    Signature {
        parameters,
        result: signature.result.clone(),
    }
}

/// The declared (value) signature of a function whose last `captures`
/// parameters are closure captures.
pub(super) fn value_signature(function: &Function, captures: usize) -> Signature {
    let declared = function.signature.parameters.len() - captures;
    Signature {
        parameters: function.signature.parameters[..declared].to_vec(),
        result: function.signature.result.clone(),
    }
}

/// Capture count of each function used as a value (0 for a plain function).
pub(super) fn function_captures(
    program: &Program,
    reachable: &BTreeSet<u32>,
) -> BTreeMap<u32, usize> {
    let mut targets = BTreeMap::new();
    for id in reachable {
        for block in &program.functions[*id as usize].blocks {
            for instruction in &block.instructions {
                match &instruction.kind {
                    InstructionKind::Constant(Constant::Function(target)) => {
                        targets.insert(target.0, 0);
                    }
                    InstructionKind::ClosureNew {
                        function: target,
                        captures,
                    } => {
                        targets.insert(target.0, captures.len());
                    }
                    _ => {}
                }
            }
        }
    }
    targets
}

/// Table slot of each function used as a value (slot 0 stays empty).
pub(super) fn function_slots(program: &Program, reachable: &BTreeSet<u32>) -> BTreeMap<u32, u32> {
    function_captures(program, reachable)
        .into_keys()
        .enumerate()
        .map(|(index, id)| (id, index as u32 + 1))
        .collect()
}
