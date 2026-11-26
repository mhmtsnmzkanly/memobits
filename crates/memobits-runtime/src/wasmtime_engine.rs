//! Wasmtime adapter for the existing core module execution contract.
use super::*;
use wasmtime::{Config, Engine, ExternType, Linker, Module, Store, Trap, Val, ValType};

pub fn run_with_capabilities(
    bytes: &[u8],
    export: &str,
    options: &RunOptions,
    capabilities: &[HostCapability],
) -> Result<RunValue, RunError> {
    let mut config = Config::new();
    config.consume_fuel(options.fuel.is_some());
    let engine = Engine::new(&config).map_err(|e| RunError::Instantiate(e.to_string()))?;
    let module = Module::new(&engine, bytes).map_err(|e| RunError::Validate(e.to_string()))?;
    for import in module.imports() {
        let enabled = import.module() == "memobits:console"
            && import.name() == "write_i32"
            && capabilities.contains(&HostCapability::ConsoleWriteI32)
            && matches!(import.ty(), ExternType::Func(ty)
                if matches!(ty.params().collect::<Vec<_>>().as_slice(), [ValType::I32])
                    && ty.results().len() == 0);
        if !enabled {
            return Err(RunError::UnsupportedImport {
                module: import.module().into(),
                name: import.name().into(),
            });
        }
    }
    let metadata = if export == entry_abi::ENTRY_EXPORT {
        let mut sections = traps::custom_sections(bytes, entry_abi::SECTION);
        let metadata = sections
            .next()
            .map(|section| {
                entry_abi::Metadata::decode(section)
                    .ok_or_else(|| entry::invalid("invalid or unsupported entry metadata"))
            })
            .transpose()?;
        if sections.next().is_some() {
            return Err(entry::invalid("duplicate entry metadata"));
        }
        metadata
    } else {
        None
    };
    let function_type = match module.get_export(export) {
        Some(ExternType::Func(ty)) => ty,
        _ => return Err(RunError::MissingExport(export.into())),
    };
    let params: Vec<_> = function_type.params().collect();
    let result_types: Vec<_> = function_type.results().collect();
    if metadata.is_some() {
        if !params.is_empty() || !matches!(result_types.as_slice(), [ValType::I32, ValType::I32]) {
            return Err(entry::invalid("unexpected entry function signature"));
        }
        if !matches!(module.get_export(entry_abi::MEMORY_EXPORT), Some(ExternType::Memory(m)) if !m.is_64())
        {
            return Err(entry::invalid("missing 32-bit entry memory export"));
        }
    } else {
        if !params.is_empty() {
            return Err(RunError::Signature(format!(
                "'{export}' takes {} parameter(s); this runner accepts no arguments",
                params.len()
            )));
        }
        match result_types.as_slice() {
            [] | [ValType::I32 | ValType::I64 | ValType::F32 | ValType::F64] => {}
            [ty] => {
                return Err(RunError::Signature(format!(
                    "'{export}' returns an unsupported Wasm type {ty:?}"
                )))
            }
            _ => {
                return Err(RunError::Signature(format!(
                    "'{export}' returns multiple values"
                )))
            }
        }
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
            .func_wrap("memobits:console", "write_i32", |value: i32| {
                let _ = writeln!(std::io::stdout().lock(), "Host i32: {value}");
            })
            .map_err(|e| RunError::Instantiate(e.to_string()))?;
    }
    let instance = linker.instantiate(&mut store, &module).map_err(|e| {
        if e.downcast_ref::<Trap>() == Some(&Trap::OutOfFuel) {
            RunError::FuelExhausted
        } else if e.downcast_ref::<Trap>().is_some() {
            RunError::Trap(e.to_string())
        } else {
            RunError::Instantiate(e.to_string())
        }
    })?;
    let function = instance
        .get_func(&mut store, export)
        .ok_or_else(|| RunError::MissingExport(export.into()))?;
    let mut results: Vec<_> = result_types
        .iter()
        .map(|ty| Val::default_for_ty(ty).expect("validated scalar result"))
        .collect();
    if let Err(error) = function.call(&mut store, &[], &mut results) {
        let trap = error.downcast_ref::<Trap>().copied();
        if trap == Some(Trap::OutOfFuel) {
            return Err(RunError::FuelExhausted);
        }
        let overflowed = instance
            .get_global(&mut store, STACK_OVERFLOW_EXPORT)
            .and_then(|g| g.get(&mut store).i32())
            == Some(1);
        if overflowed {
            return Err(RunError::StackOverflow);
        }
        let record = instance
            .get_global(&mut store, traps::TRAP_EXPORT)
            .and_then(|g| g.get(&mut store).i32())
            .unwrap_or(0) as u32;
        let reason = match (trap, (record & 0xff) as u8) {
            (Some(Trap::UnreachableCodeReached), code) => TrapReason::from_explicit_code(code),
            (Some(Trap::IntegerDivisionByZero), 5) => Some(TrapReason::DivisionByZero),
            (Some(Trap::IntegerDivisionByZero), 6) => Some(TrapReason::RemainderByZero),
            (Some(Trap::IntegerOverflow), 5) => Some(TrapReason::DivisionOverflow),
            _ => None,
        };
        if let (Some(reason), Some(table)) = (
            reason,
            custom_section(bytes, TRAP_SECTION).and_then(TrapTable::decode),
        ) {
            return Err(RunError::Checked {
                reason,
                location: table.get(record >> 8).cloned(),
            });
        }
        return Err(RunError::Trap(error.to_string()));
    }
    if let Some(metadata) = metadata {
        let [Val::I32(address), Val::I32(size)] = results.as_slice() else {
            unreachable!()
        };
        let memory = instance
            .get_memory(&mut store, entry_abi::MEMORY_EXPORT)
            .ok_or_else(|| entry::invalid("missing entry memory"))?;
        return entry::decode(metadata, memory.data(&store), *address as u32, *size as u32)
            .map(RunValue::Outcome);
    }
    match results.into_iter().next() {
        None => Ok(RunValue::Unit),
        Some(Val::I32(v)) => Ok(RunValue::I32(v)),
        Some(Val::I64(v)) => Ok(RunValue::I64(v)),
        Some(Val::F32(v)) => Ok(RunValue::F32(f32::from_bits(v))),
        Some(Val::F64(v)) => Ok(RunValue::F64(f64::from_bits(v))),
        _ => unreachable!("validated scalar result"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_encoder::{
        CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction,
        Module as EncodedModule, TypeSection, ValType as EncodedValType,
    };

    fn scalar_guest() -> Vec<u8> {
        let mut module = EncodedModule::new();
        let mut types = TypeSection::new();
        types.ty().function([], [EncodedValType::I32]);
        let mut functions = FunctionSection::new();
        functions.function(0);
        let mut exports = ExportSection::new();
        exports.export("main", ExportKind::Func, 0);
        let mut code = CodeSection::new();
        let mut f = Function::new([]);
        f.instruction(&Instruction::I32Const(42));
        f.instruction(&Instruction::End);
        code.function(&f);
        module
            .section(&types)
            .section(&functions)
            .section(&exports)
            .section(&code);
        module.finish()
    }
    #[test]
    fn same_core_bytes_produce_same_scalar_and_validation_categories() {
        let bytes = scalar_guest();
        let options = RunOptions::default();
        assert_eq!(
            run_with_capabilities(&bytes, "main", &options, &[]),
            super::super::run_with(&bytes, "main", &options)
        );
        assert_eq!(
            run_with_capabilities(&bytes, "missing", &options, &[]),
            super::super::run_with(&bytes, "missing", &options)
        );
        assert!(matches!(
            run_with_capabilities(b"not wasm", "main", &options, &[]),
            Err(RunError::Validate(_))
        ));
        assert!(matches!(
            super::super::run_with(b"not wasm", "main", &options),
            Err(RunError::Validate(_))
        ));
        assert_eq!(
            run_with_capabilities(&bytes, "main", &RunOptions { fuel: None }, &[]),
            Ok(RunValue::I32(42))
        );
    }
}
