//! Scalar application and library components with a bounded WIT host import.
use memobits_diagnostics::Span;
use memobits_ir::{Access, FunctionId, Primitive, Program, Type};
use std::collections::{BTreeMap, HashMap};
use wasm_encoder::{
    ComponentBuilder, ComponentExportKind, ComponentTypeRef, ComponentValType, ExportKind,
    InstanceType, ModuleArg, PrimitiveValType,
};

pub struct ComponentError {
    pub message: String,
    pub spans: Vec<Span>,
}

impl From<String> for ComponentError {
    fn from(message: String) -> Self {
        Self {
            message,
            spans: Vec::new(),
        }
    }
}

fn at(message: String, span: Span) -> ComponentError {
    ComponentError {
        message,
        spans: vec![span],
    }
}

fn scalar(ty: &Type, unit_result: bool) -> Result<Option<PrimitiveValType>, String> {
    let Type::Primitive(ty) = ty else {
        return Err("component signatures support only scalar or Unit results".into());
    };
    Ok(Some(match ty {
        Primitive::Unit if unit_result => return Ok(None),
        Primitive::Unit => return Err("component parameters cannot use Unit".into()),
        Primitive::Bool => PrimitiveValType::Bool,
        Primitive::Char => PrimitiveValType::Char,
        Primitive::I8 => PrimitiveValType::S8,
        Primitive::I16 => PrimitiveValType::S16,
        Primitive::I32 => PrimitiveValType::S32,
        Primitive::I64 => PrimitiveValType::S64,
        Primitive::U8 => PrimitiveValType::U8,
        Primitive::U16 => PrimitiveValType::U16,
        Primitive::U32 => PrimitiveValType::U32,
        Primitive::U64 => PrimitiveValType::U64,
        Primitive::F32 => PrimitiveValType::F32,
        Primitive::F64 => PrimitiveValType::F64,
    }))
}

fn wit_name(name: &str) -> Result<String, String> {
    if !name.is_ascii() {
        return Err(format!("component identifier '{name}' must be ASCII"));
    }
    let chars: Vec<char> = name.chars().collect();
    let mut result = String::new();
    for (i, &ch) in chars.iter().enumerate() {
        if ch == '_' || ch == '-' {
            if !result.is_empty() && !result.ends_with('-') {
                result.push('-');
            }
            continue;
        }
        if !ch.is_ascii_alphanumeric() {
            return Err(format!("invalid component identifier '{name}'"));
        }
        let prev = i.checked_sub(1).and_then(|j| chars.get(j)).copied();
        let next = chars.get(i + 1).copied();
        let boundary = ch.is_ascii_uppercase()
            && (prev.is_some_and(|p| p.is_ascii_lowercase() || p.is_ascii_digit())
                || (prev.is_some_and(|p| p.is_ascii_uppercase())
                    && next.is_some_and(|n| n.is_ascii_lowercase())));
        if boundary && !result.is_empty() && !result.ends_with('-') {
            result.push('-');
        }
        result.push(ch.to_ascii_lowercase());
    }
    while result.ends_with('-') {
        result.pop();
    }
    if !result.starts_with(|c: char| c.is_ascii_lowercase()) {
        return Err(format!("invalid component identifier '{name}'"));
    }
    Ok(result)
}

pub fn encode(
    core: &[u8],
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    library: bool,
) -> Result<Vec<u8>, ComponentError> {
    let mut console_import = false;
    for payload in wasmparser::Parser::new(0).parse_all(core) {
        if let wasmparser::Payload::ImportSection(imports) = payload.map_err(|e| e.to_string())? {
            for import in imports.into_imports() {
                let import = import.map_err(|e| e.to_string())?;
                if import.module != "memobits:console"
                    || import.name != "write_i32"
                    || !matches!(import.ty, wasmparser::TypeRef::Func(_))
                    || console_import
                {
                    return Err(String::from("unsupported component host import").into());
                }
                console_import = true;
            }
        }
    }
    let mut seen = HashMap::new();
    let mut items = Vec::new();
    for (alias, id) in exports {
        let function = &program.functions[id.0 as usize];
        let name = wit_name(alias).map_err(|message| at(message, function.span))?;
        if let Some((other, span)) = seen.insert(name.clone(), (alias, function.span)) {
            return Err(ComponentError {
                message: format!(
                    "component exports '{other}' and '{alias}' both normalize to '{name}'"
                ),
                spans: vec![span, function.span],
            });
        }
        if !library && !function.signature.parameters.is_empty() {
            return Err(at(
                "component application entry must have no parameters".into(),
                function.span,
            ));
        }
        let mut params = Vec::new();
        let mut names = HashMap::new();
        for (i, param) in function.signature.parameters.iter().enumerate() {
            if param.access != Access::Owned {
                return Err(at(
                    "component parameters cannot use borrow or share".into(),
                    function.span,
                ));
            }
            let local = &function.locals[function.parameter_locals[i].0 as usize];
            let name = wit_name(&local.name).map_err(|message| at(message, local.span))?;
            if let Some((other, span)) = names.insert(name.clone(), (&local.name, local.span)) {
                return Err(ComponentError {
                    message: format!(
                        "parameters '{other}' and '{}' both normalize to '{name}'",
                        local.name
                    ),
                    spans: vec![span, local.span],
                });
            }
            params.push((
                name,
                ComponentValType::Primitive(
                    scalar(&param.ty, false)
                        .map_err(|message| at(message, local.span))?
                        .unwrap(),
                ),
            ));
        }
        items.push((
            alias,
            name,
            params,
            scalar(&function.signature.result, true)
                .map_err(|message| at(message, function.span))?
                .map(ComponentValType::Primitive),
        ));
    }
    let mut component = ComponentBuilder::default();
    let module = component.core_module_raw(None, core);
    let instance = if console_import {
        let mut interface = InstanceType::new();
        interface
            .ty()
            .function()
            .params([("value", PrimitiveValType::S32)])
            .result(None);
        interface.export("write-i32", ComponentTypeRef::Func(0));
        let interface_type = component.type_instance(None, &interface);
        let host = component.import(
            "memobits:console/console",
            ComponentTypeRef::Instance(interface_type),
        );
        let write = component.alias_export(host, "write-i32", ComponentExportKind::Func);
        let lower = component.lower_func(None, write, []);
        let core_host =
            component.core_instantiate_exports(None, [("write_i32", ExportKind::Func, lower)]);
        component.core_instantiate(
            None,
            module,
            [("memobits:console", ModuleArg::Instance(core_host))],
        )
    } else {
        component.core_instantiate(None, module, [])
    };
    for (alias, name, params, result) in items {
        let core_func = component.core_alias_export(None, instance, alias, ExportKind::Func);
        let (ty, mut func) = component.type_function(None);
        func.params(params.iter().map(|(name, ty)| (name.as_str(), *ty)))
            .result(result);
        let lifted = component.lift_func(None, core_func, ty, []);
        component.export(name.as_str(), ComponentExportKind::Func, lifted, None);
    }
    let bytes = component.finish();
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .map_err(|e| ComponentError::from(format!("invalid generated component: {e}")))?;
    Ok(bytes)
}
