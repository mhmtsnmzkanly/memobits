//! Wasmtime execution of scalar components with explicitly enabled host imports.
use super::*;
use wasmtime::component::{
    types::{ComponentItem, Type},
    Component, Linker, Val,
};
use wasmtime::{Config, Engine, Store, Trap};

pub fn run(
    bytes: &[u8],
    export: &str,
    options: &RunOptions,
    capabilities: &[HostCapability],
) -> Result<RunValue, RunError> {
    let mut config = Config::new();
    config.consume_fuel(options.fuel.is_some());
    let engine = Engine::new(&config).map_err(|e| RunError::Instantiate(e.to_string()))?;
    let component =
        Component::new(&engine, bytes).map_err(|e| RunError::Validate(e.to_string()))?;
    let ty = component.component_type();
    for (name, item) in ty.imports(&engine) {
        let valid = name == "memobits:console/console"
            && capabilities.contains(&HostCapability::ConsoleWriteI32)
            && matches!(item, ComponentItem::ComponentInstance(ref interface)
                if interface.exports(&engine).len() == 1
                && matches!(interface.get_export(&engine, "write-i32"), Some(ComponentItem::ComponentFunc(ref function))
                    if matches!(function.params().map(|(_, ty)| ty).collect::<Vec<_>>().as_slice(), [Type::S32])
                    && function.results().len() == 0));
        if !valid {
            return Err(RunError::UnsupportedImport {
                module: "component".into(),
                name: name.into(),
            });
        }
    }
    let function = match ty.get_export(&engine, export) {
        Some(ComponentItem::ComponentFunc(ty)) => ty,
        _ => return Err(RunError::MissingExport(export.into())),
    };
    if function.params().len() != 0 {
        return Err(RunError::Signature(format!(
            "'{export}' takes parameters; this runner accepts no arguments"
        )));
    }
    let results: Vec<_> = function.results().collect();
    let scalar = |ty: &Type| {
        matches!(
            ty,
            Type::Bool
                | Type::S8
                | Type::S16
                | Type::S32
                | Type::S64
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::Float32
                | Type::Float64
        )
    };
    let mut outcome_sections = traps::custom_sections(bytes, "memobits.component.outcome");
    let marker = outcome_sections.next();
    if outcome_sections.next().is_some() {
        return Err(entry::invalid("duplicate component outcome metadata"));
    }
    if marker.is_some_and(|value| value != b"root-error-v1" && value != b"root-optional-error-v1") {
        return Err(entry::invalid(
            "invalid or unsupported component outcome metadata",
        ));
    }
    let optional_outcome = marker == Some(&b"root-optional-error-v1"[..]);
    let root_outcome = match results.as_slice() {
        [Type::Result(result)] if marker.is_some() => {
            (if optional_outcome {
                matches!(result.ok(), Some(Type::Option(ref option)) if scalar(&option.ty()))
            } else {
                matches!(result.ok(), Some(ref ty) if scalar(ty))
            }) && matches!(result.err(), Some(Type::Record(ref record))
                    if record.fields().map(|f| (f.name, f.ty)).collect::<Vec<_>>() == [("code", Type::U32)])
        }
        _ => false,
    };
    if !root_outcome
        && !matches!(
            results.as_slice(),
            [] | [Type::Bool
                | Type::Char
                | Type::S8
                | Type::S16
                | Type::S32
                | Type::S64
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::Float32
                | Type::Float64]
        )
    {
        return Err(RunError::Signature(format!(
            "'{export}' has an unsupported component result"
        )));
    }
    let mut store = Store::new(&engine, ());
    if let Some(fuel) = options.fuel {
        store
            .set_fuel(fuel)
            .map_err(|e| RunError::Instantiate(e.to_string()))?;
    }
    let mut linker = Linker::new(&engine);
    if capabilities.contains(&HostCapability::ConsoleWriteI32) {
        linker
            .instance("memobits:console/console")
            .and_then(|mut instance| {
                instance.func_wrap("write-i32", |_, (value,): (i32,)| {
                    let _ = writeln!(std::io::stdout().lock(), "Host i32: {value}");
                    Ok(())
                })
            })
            .map_err(|e| RunError::Instantiate(e.to_string()))?;
    }
    let instance = linker.instantiate(&mut store, &component).map_err(|e| {
        if e.downcast_ref::<Trap>() == Some(&Trap::OutOfFuel) {
            RunError::FuelExhausted
        } else {
            RunError::Instantiate(e.to_string())
        }
    })?;
    let func = instance
        .get_func(&mut store, export)
        .ok_or_else(|| RunError::MissingExport(export.into()))?;
    let mut result = vec![Val::Bool(false); results.len()];
    func.call(&mut store, &[], &mut result).map_err(|e| {
        if e.downcast_ref::<Trap>() == Some(&Trap::OutOfFuel) {
            RunError::FuelExhausted
        } else {
            component_trap(&e, bytes).unwrap_or_else(|| RunError::Trap(e.to_string()))
        }
    })?;
    func.post_return(&mut store).map_err(|e| {
        if e.downcast_ref::<Trap>() == Some(&Trap::OutOfFuel) {
            RunError::FuelExhausted
        } else {
            RunError::Trap(e.to_string())
        }
    })?;
    Ok(match result.into_iter().next() {
        None => RunValue::Unit,
        Some(Val::Bool(v)) => RunValue::I32(i32::from(v)),
        Some(Val::Char(v)) => RunValue::I32(v as i32),
        Some(Val::S8(v)) => RunValue::I32(v.into()),
        Some(Val::S16(v)) => RunValue::I32(v.into()),
        Some(Val::S32(v)) => RunValue::I32(v),
        Some(Val::U8(v)) => RunValue::I32(v.into()),
        Some(Val::U16(v)) => RunValue::I32(v.into()),
        Some(Val::U32(v)) => RunValue::I32(v as i32),
        Some(Val::S64(v)) => RunValue::I64(v),
        Some(Val::U64(v)) => RunValue::I64(v as i64),
        Some(Val::Float32(v)) => RunValue::F32(v),
        Some(Val::Float64(v)) => RunValue::F64(v),
        Some(Val::Result(Ok(Some(value)))) if root_outcome => {
            let outcome = if optional_outcome {
                match *value {
                    Val::Option(Some(value)) => EntryOutcome::OkSome(component_success(*value)?),
                    Val::Option(None) => EntryOutcome::OkNone,
                    _ => return Err(entry::invalid("invalid component optional outcome success")),
                }
            } else {
                EntryOutcome::Ok(component_success(*value)?)
            };
            RunValue::Outcome(outcome)
        }
        Some(Val::Result(Err(Some(value)))) if root_outcome => {
            let Val::Record(fields) = *value else {
                return Err(entry::invalid("invalid component Error payload"));
            };
            let [(name, Val::U32(code))] = fields.as_slice() else {
                return Err(entry::invalid("invalid component Error fields"));
            };
            if name != "code" {
                return Err(entry::invalid("invalid component Error field name"));
            }
            RunValue::Outcome(EntryOutcome::Err(ReturnedError {
                type_name: "Error".into(),
                code: *code,
            }))
        }
        _ if root_outcome => return Err(entry::invalid("invalid component outcome")),
        _ => unreachable!("validated scalar component result"),
    })
}

fn component_success(value: Val) -> Result<EntrySuccess, RunError> {
    Ok(match value {
        Val::Bool(v) => EntrySuccess::Bool(v),
        Val::S8(v) => EntrySuccess::I8(v),
        Val::S16(v) => EntrySuccess::I16(v),
        Val::S32(v) => EntrySuccess::I32(v),
        Val::S64(v) => EntrySuccess::I64(v),
        Val::U8(v) => EntrySuccess::U8(v),
        Val::U16(v) => EntrySuccess::U16(v),
        Val::U32(v) => EntrySuccess::U32(v),
        Val::U64(v) => EntrySuccess::U64(v),
        Val::Float32(v) => EntrySuccess::F32(v),
        Val::Float64(v) => EntrySuccess::F64(v),
        _ => return Err(entry::invalid("invalid component outcome success")),
    })
}

/// Recover compiler-emitted trap records only when the actual faulting Wasm
/// instruction is immediately preceded by the verified recording sequence.
/// No guest state is read or resumed after a component trap.
fn component_trap(error: &wasmtime::Error, component: &[u8]) -> Option<RunError> {
    use wasmparser::{ExternalKind, Operator, Parser, Payload};

    let trap = *error.downcast_ref::<Trap>()?;
    let offset = error
        .downcast_ref::<wasmtime::WasmBacktrace>()?
        .frames()
        .first()?
        .module_offset()?;
    // Select only the unnested core module whose byte range contains the
    // actual Wasmtime fault offset. Never guess when a range is absent or
    // ambiguous, and reject nested components.
    let mut selected = None;
    for payload in Parser::new(0).parse_all(component) {
        match payload.ok()? {
            Payload::ModuleSection {
                unchecked_range, ..
            } => {
                if unchecked_range.contains(&(offset as u64))
                    && selected.replace(unchecked_range).is_some()
                {
                    return None;
                }
            }
            Payload::ComponentSection { .. } => return None,
            _ => {}
        }
    }
    let range = selected?;
    let start = usize::try_from(range.start).ok()?;
    let end = usize::try_from(range.end).ok()?;
    let core = component.get(start..end)?;
    let offset = offset.checked_sub(start)?;
    let mut trap_global = None;
    let mut overflow_global = None;
    for payload in Parser::new(0).parse_all(core) {
        if let Payload::ExportSection(exports) = payload.ok()? {
            for export in exports {
                let export = export.ok()?;
                if export.kind != ExternalKind::Global {
                    continue;
                }
                if export.name == traps::TRAP_EXPORT {
                    trap_global = Some(export.index);
                }
                if export.name == STACK_OVERFLOW_EXPORT {
                    overflow_global = Some(export.index);
                }
            }
        }
    }
    #[derive(Clone, Copy)]
    enum Op {
        Const(i32),
        Set(u32),
        Get,
        Other,
    }
    for payload in Parser::new(0).parse_all(core) {
        if let Payload::CodeSectionEntry(body) = payload.ok()? {
            let mut reader = body.get_operators_reader().ok()?;
            let mut last = [Op::Other; 4];
            while !reader.eof() {
                let position = usize::try_from(reader.original_position()).ok()?;
                let op = reader.read().ok()?;
                if position == offset {
                    let recorded = match (&op, last) {
                        (Operator::Unreachable, [_, _, Op::Const(value), Op::Set(global)]) => {
                            Some((value, global))
                        }
                        (
                            Operator::I32DivS
                            | Operator::I32DivU
                            | Operator::I32RemS
                            | Operator::I32RemU
                            | Operator::I64DivS
                            | Operator::I64DivU
                            | Operator::I64RemS
                            | Operator::I64RemU,
                            [Op::Const(value), Op::Set(global), Op::Get, Op::Get],
                        ) => Some((value, global)),
                        _ => None,
                    }?;
                    if matches!(op, Operator::Unreachable)
                        && recorded.0 == 1
                        && Some(recorded.1) == overflow_global
                    {
                        return Some(RunError::StackOverflow);
                    }
                    if Some(recorded.1) != trap_global {
                        return None;
                    }
                    let packed = recorded.0 as u32;
                    let reason = match (trap, (packed & 0xff) as u8) {
                        (Trap::UnreachableCodeReached, code) => {
                            TrapReason::from_explicit_code(code)
                        }
                        (Trap::IntegerDivisionByZero, 5) => Some(TrapReason::DivisionByZero),
                        (Trap::IntegerDivisionByZero, 6) => Some(TrapReason::RemainderByZero),
                        (Trap::IntegerOverflow, 5) => Some(TrapReason::DivisionOverflow),
                        _ => None,
                    }?;
                    let table = custom_section(core, TRAP_SECTION).and_then(TrapTable::decode)?;
                    return Some(RunError::Checked {
                        reason,
                        location: table.get(packed >> 8).cloned(),
                    });
                }
                last.rotate_left(1);
                last[3] = match op {
                    Operator::I32Const { value } => Op::Const(value),
                    Operator::GlobalSet { global_index } => Op::Set(global_index),
                    Operator::LocalGet { .. } => Op::Get,
                    _ => Op::Other,
                };
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_encoder::{
        CodeSection, ComponentBuilder, ComponentExportKind, ComponentValType, ConstExpr,
        ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType,
        Instruction, Module, TypeSection, ValType,
    };

    fn trapped_component(insert_nop: bool, second_module: bool) -> Vec<u8> {
        let mut core = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], []);
        let mut functions = FunctionSection::new();
        functions.function(0);
        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(0),
        );
        let mut exports = ExportSection::new();
        exports.export("main", ExportKind::Func, 0);
        exports.export(traps::TRAP_EXPORT, ExportKind::Global, 0);
        let mut body = Function::new([]);
        body.instruction(&Instruction::I32Const((1 << 8) | 12));
        body.instruction(&Instruction::GlobalSet(0));
        if insert_nop {
            body.instruction(&Instruction::Nop);
        }
        body.instruction(&Instruction::Unreachable);
        body.instruction(&Instruction::End);
        let mut code = CodeSection::new();
        code.function(&body);
        core.section(&types)
            .section(&functions)
            .section(&globals)
            .section(&exports)
            .section(&code);
        let table = TrapTable {
            locations: vec![SourceLocation {
                file: "example.mb".into(),
                line: 2,
                column: 3,
                width: 1,
                text: "assert(false)".into(),
            }],
        };
        let core = with_trap_table(&core.finish(), &table);
        let mut component = ComponentBuilder::default();
        let module = component.core_module_raw(None, &core);
        if second_module {
            component.core_module_raw(None, &core);
        }
        let instance = component.core_instantiate(None, module, []);
        let main = component.core_alias_export(None, instance, "main", ExportKind::Func);
        let (ty, mut func) = component.type_function(None);
        func.params([] as [(&str, ComponentValType); 0])
            .result(None);
        let lift = component.lift_func(None, main, ty, []);
        component.export("main", ComponentExportKind::Func, lift, None);
        component.finish()
    }

    #[test]
    fn rejects_mismatched_wit_host_signatures_before_instantiation() {
        use wasm_encoder::{ComponentTypeRef, InstanceType, PrimitiveValType};
        let mut component = ComponentBuilder::default();
        let mut interface = InstanceType::new();
        interface
            .ty()
            .function()
            .params([("value", PrimitiveValType::U32)])
            .result(None);
        interface.export("write-i32", ComponentTypeRef::Func(0));
        let ty = component.type_instance(None, &interface);
        component.import("memobits:console/console", ComponentTypeRef::Instance(ty));
        let bytes = component.finish();
        let result = run(
            &bytes,
            "main",
            &RunOptions::default(),
            &[HostCapability::ConsoleWriteI32],
        );
        assert_eq!(
            result,
            Err(RunError::UnsupportedImport {
                module: "component".into(),
                name: "memobits:console/console".into()
            })
        );
    }

    #[test]
    fn trap_attribution_requires_an_adjacent_record_in_the_faulting_module() {
        let options = RunOptions::default();
        assert!(matches!(
            run(&trapped_component(false, false), "main", &options, &[]),
            Err(RunError::Checked {
                reason: TrapReason::AssertionFailed,
                ..
            })
        ));
        assert!(matches!(
            run(&trapped_component(true, false), "main", &options, &[]),
            Err(RunError::Trap(_))
        ));
        assert!(matches!(
            run(&trapped_component(false, true), "main", &options, &[]),
            Err(RunError::Checked {
                reason: TrapReason::AssertionFailed,
                ..
            })
        ));
    }
}
