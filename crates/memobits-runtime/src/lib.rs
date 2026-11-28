//! Small, fuel-limited WebAssembly runner for zero-argument exports.
//! Bare Wasm exports use scalar results. Memobits application artifacts can
//! also carry a versioned adapter for compiler-known outcomes.

#[cfg(feature = "wasmtime")]
mod component_engine;
#[cfg(feature = "wasmtime")]
mod wasmtime_engine;
#[cfg(feature = "wasmtime")]
pub fn exec_with_capabilities(
    bytes: &[u8],
    export: &str,
    options: &RunOptions,
    capabilities: &[HostCapability],
) -> Result<RunValue, RunError> {
    if bytes.starts_with(b"\0asm\x0d\0\x01\0") {
        component_engine::run(bytes, export, options, capabilities)
    } else {
        wasmtime_engine::run_with_capabilities(bytes, export, options, capabilities)
    }
}

mod entry;
pub use entry::{EntryOutcome, EntrySuccess, ReturnedError};
use memobits_entry_abi as entry_abi;

mod traps;
pub use traps::{
    custom_section, with_custom_section, with_trap_table, SourceLocation, TrapReason, TrapTable,
    TRAP_SECTION,
};

use std::io::Write as IoWrite;
use wasmi::{
    Config, Engine, Error as WasmiError, ExternType, Linker, Module, Store, TrapCode, Val, ValType,
};

/// Export name of the backend's stack-exhaustion flag global (the value of
/// `memobits_wasm::STACK_OVERFLOW_EXPORT`; the runtime does not depend on the
/// backend crate).
const STACK_OVERFLOW_EXPORT: &str = "__mb_stack_overflow";

/// The default instruction fuel budget for a call: ten billion units.
///
/// Ordinary programs finish far below it, while runaway loops still end.
pub const DEFAULT_FUEL: u64 = 10_000_000_000;

/// Execution options for [`run_with`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunOptions {
    /// The instruction fuel budget for module start-up and the call, or `None`
    /// for unlimited execution. Unlimited execution disables fuel metering
    /// entirely, so guest loops are not counted at all.
    pub fuel: Option<u64>,
}

/// Typed host capabilities that a caller explicitly enables for one run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HostCapability {
    /// `memobits:console.write_i32(i32) -> unit` writes one signed integer to
    /// the host's standard output.
    ConsoleWriteI32,
}

impl Default for RunOptions {
    /// Metered execution with [`DEFAULT_FUEL`].
    fn default() -> Self {
        Self {
            fuel: Some(DEFAULT_FUEL),
        }
    }
}

/// A scalar Wasm result or a decoded Memobits entry outcome.
#[derive(Clone, Debug, PartialEq)]
pub enum RunValue {
    /// The function returned no Wasm values.
    Unit,
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Outcome(EntryOutcome),
    /// A standalone primitive optional application entry.
    Option(Option<EntrySuccess>),
}

/// An error while validating, instantiating, or calling a module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunError {
    /// The module could not be parsed or validated.
    Validate(String),
    /// The module requires a host import that was not explicitly enabled.
    UnsupportedImport { module: String, name: String },
    /// The module could not be instantiated.
    Instantiate(String),
    /// The requested name is absent or does not refer to a function.
    MissingExport(String),
    /// The function has parameters or an unsupported result signature.
    Signature(String),
    /// Entry adapter metadata, signature, or returned storage is malformed.
    EntryAbi(String),
    /// The guest exhausted the execution fuel budget.
    FuelExhausted,
    /// The guest trapped while running.
    Trap(String),
    /// The guest ran out of its configured stack (`[build].stack_size`).
    StackOverflow,
    /// A checked operation failed (overflow, division by zero, array bounds).
    /// `location` is known when the module carries a `memobits.traps` table.
    Checked {
        reason: TrapReason,
        location: Option<SourceLocation>,
    },
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Validate(message) => write!(f, "invalid WebAssembly module: {message}"),
            Self::UnsupportedImport { module, name } => {
                write!(f, "unsupported WebAssembly import '{module}.{name}'")
            }
            Self::Instantiate(message) => {
                write!(f, "could not instantiate WebAssembly module: {message}")
            }
            Self::MissingExport(name) => write!(f, "missing function export '{name}'"),
            Self::Signature(message) => write!(f, "unsupported function signature: {message}"),
            Self::EntryAbi(message) => write!(f, "invalid Memobits entry adapter: {message}"),
            Self::FuelExhausted => f.write_str("WebAssembly execution fuel exhausted"),
            Self::Trap(message) => write!(f, "WebAssembly execution trapped: {message}"),
            Self::Checked { reason, location } => {
                f.write_str(reason.message())?;
                match location {
                    Some(location) => {
                        write!(f, " at {}:{}:{}", location.file, location.line, location.column)
                    }
                    None => Ok(()),
                }
            }
            Self::StackOverflow => f.write_str(
                "stack overflow: the program exhausted its stack; raise [build].stack_size or reduce recursion depth",
            ),
        }
    }
}

impl std::error::Error for RunError {}

/// The names of a module's function exports, in module order.
pub fn exported_functions(bytes: &[u8]) -> Result<Vec<String>, RunError> {
    let engine = Engine::new(&Config::default());
    let module =
        Module::new(&engine, bytes).map_err(|error| RunError::Validate(error.to_string()))?;
    Ok(module
        .exports()
        .filter(|export| matches!(export.ty(), ExternType::Func(_)))
        .map(|export| export.name().to_owned())
        .collect())
}

/// Validate, instantiate, and call a zero-parameter Wasm function export.
///
/// Validate, instantiate, and call a zero-parameter Wasm function export with
/// the default options: metered execution under [`DEFAULT_FUEL`].
pub fn run(bytes: &[u8], export: &str) -> Result<RunValue, RunError> {
    run_with(bytes, export, &RunOptions::default())
}

/// Validate, instantiate, and call a zero-parameter Wasm function export.
///
/// With `options.fuel == Some(n)` the module is compiled with fuel metering
/// and start-up plus the call share `n` fuel units. With `None` fuel metering
/// is not enabled at all. Modules with imports are rejected before
/// instantiation.
pub fn run_with(bytes: &[u8], export: &str, options: &RunOptions) -> Result<RunValue, RunError> {
    run_with_capabilities(bytes, export, options, &[])
}

/// Run a module with the explicitly enabled, typed host capabilities.
pub fn run_with_capabilities(
    bytes: &[u8],
    export: &str,
    options: &RunOptions,
    capabilities: &[HostCapability],
) -> Result<RunValue, RunError> {
    let mut config = Config::default();
    config.consume_fuel(options.fuel.is_some());
    config.ignore_custom_sections(true);
    let engine = Engine::new(&config);
    let module =
        Module::new(&engine, bytes).map_err(|error| RunError::Validate(error.to_string()))?;

    for import in module.imports() {
        let enabled = import.module() == "memobits:console"
            && import.name() == "write_i32"
            && capabilities.contains(&HostCapability::ConsoleWriteI32)
            && matches!(import.ty(), ExternType::Func(ty)
                if ty.params() == &[ValType::I32] && ty.results().is_empty());
        if !enabled {
            return Err(RunError::UnsupportedImport {
                module: import.module().to_owned(),
                name: import.name().to_owned(),
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
    let export_type = module
        .get_export(export)
        .ok_or_else(|| RunError::MissingExport(export.to_owned()))?;
    let function_type = match export_type {
        ExternType::Func(function_type) => function_type,
        _ => return Err(RunError::MissingExport(export.to_owned())),
    };
    if metadata.is_some() {
        if !function_type.params().is_empty()
            || function_type.results() != [ValType::I32, ValType::I32]
        {
            return Err(entry::invalid("unexpected entry function signature"));
        }
        if !matches!(
            module.get_export(entry_abi::MEMORY_EXPORT),
            Some(ExternType::Memory(memory)) if !memory.is_64()
        ) {
            return Err(entry::invalid("missing 32-bit entry memory export"));
        }
    } else {
        if !function_type.params().is_empty() {
            return Err(RunError::Signature(format!(
                "'{export}' takes {} parameter(s); this runner accepts no arguments",
                function_type.params().len()
            )));
        }
        match function_type.results() {
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
            .map_err(|error| RunError::Instantiate(error.to_string()))?;
    }
    let mut linker = Linker::new(&engine);
    if capabilities.contains(&HostCapability::ConsoleWriteI32) {
        linker
            .func_wrap("memobits:console", "write_i32", |value: i32| {
                let _ = writeln!(std::io::stdout().lock(), "Host i32: {value}");
            })
            .map_err(|error| RunError::Instantiate(error.to_string()))?;
    }
    let instance = linker
        .instantiate_and_start(&mut store, &module)
        .map_err(classify_instantiation)?;
    let function = instance
        .get_func(&store, export)
        .ok_or_else(|| RunError::MissingExport(export.to_owned()))?;
    let mut results = function_type
        .results()
        .iter()
        .copied()
        .map(Val::default_for_ty)
        .collect::<Vec<_>>();
    if let Err(error) = function.call(&mut store, &[], &mut results) {
        // Stack exhaustion sets an exported flag global before trapping, which
        // is how it is told apart from other `unreachable` traps.
        let overflowed = instance
            .get_global(&store, STACK_OVERFLOW_EXPORT)
            .is_some_and(|flag| flag.get(&store).i32() == Some(1));
        let record = instance
            .get_global(&store, traps::TRAP_EXPORT)
            .and_then(|global| global.get(&store).i32())
            .unwrap_or(0);
        return Err(
            if overflowed && error.as_trap_code() != Some(TrapCode::OutOfFuel) {
                RunError::StackOverflow
            } else {
                checked_trap(&error, record, bytes).unwrap_or_else(|| classify_call(error))
            },
        );
    }
    if let Some(metadata) = metadata {
        let [Val::I32(address), Val::I32(size)] = results.as_slice() else {
            unreachable!("validated entry adapter signature");
        };
        let memory = instance
            .get_memory(&store, entry_abi::MEMORY_EXPORT)
            .ok_or_else(|| entry::invalid("missing entry memory"))?;
        return entry::decode(metadata, memory.data(&store), *address as u32, *size as u32);
    }
    match results.into_iter().next() {
        None => Ok(RunValue::Unit),
        Some(Val::I32(value)) => Ok(RunValue::I32(value)),
        Some(Val::I64(value)) => Ok(RunValue::I64(value)),
        Some(Val::F32(value)) => Ok(RunValue::F32(value.to_float())),
        Some(Val::F64(value)) => Ok(RunValue::F64(value.to_float())),
        Some(value) => Err(RunError::Signature(format!(
            "'{export}' returns unsupported Wasm type {:?}",
            value.ty()
        ))),
    }
}

/// Interpret the trap record after a trap. Explicit checks trap with
/// `unreachable`; division sites record their code and let Wasm trap natively.
fn checked_trap(error: &WasmiError, record: i32, module: &[u8]) -> Option<RunError> {
    let record = record as u32;
    let (code, location) = ((record & 0xff) as u8, record >> 8);
    let reason = match (error.as_trap_code()?, code) {
        (TrapCode::UnreachableCodeReached, code) => TrapReason::from_explicit_code(code)?,
        (TrapCode::IntegerDivisionByZero, 5) => TrapReason::DivisionByZero,
        (TrapCode::IntegerDivisionByZero, 6) => TrapReason::RemainderByZero,
        (TrapCode::IntegerOverflow, 5) => TrapReason::DivisionOverflow,
        _ => return None,
    };
    // Without the location table (stripped, or built by an older compiler) the
    // record cannot be trusted to mean anything: keep the generic trap.
    let table = custom_section(module, TRAP_SECTION).and_then(TrapTable::decode)?;
    Some(RunError::Checked {
        reason,
        location: table.get(location).cloned(),
    })
}

fn classify_instantiation(error: WasmiError) -> RunError {
    if error.as_trap_code() == Some(TrapCode::OutOfFuel) {
        RunError::FuelExhausted
    } else if error.as_trap_code().is_some() {
        RunError::Trap(error.to_string())
    } else {
        RunError::Instantiate(error.to_string())
    }
}

fn classify_call(error: WasmiError) -> RunError {
    if error.as_trap_code() == Some(TrapCode::OutOfFuel) {
        RunError::FuelExhausted
    } else {
        RunError::Trap(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        custom_section, run_with, with_trap_table, RunError, RunOptions, RunValue, SourceLocation,
        TrapReason, TrapTable, TRAP_SECTION,
    };
    use wasm_encoder::{
        BlockType, CodeSection, EntityType, ExportKind, ExportSection, Function, FunctionSection,
        ImportSection, Instruction, Module, StartSection, TypeSection, ValType,
    };

    fn run_with_fuel(bytes: &[u8], export: &str, fuel: u64) -> Result<RunValue, RunError> {
        run_with(bytes, export, &RunOptions { fuel: Some(fuel) })
    }

    fn module(result: Option<(ValType, Instruction<'static>)>) -> Vec<u8> {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], result.as_ref().map(|(ty, _)| *ty));
        module.section(&types);

        let mut functions = FunctionSection::new();
        functions.function(0);
        module.section(&functions);

        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        module.section(&exports);

        let mut code = CodeSection::new();
        let mut function = Function::new([]);
        if let Some((_, instruction)) = result {
            function.instruction(&instruction);
        }
        function.instruction(&Instruction::End);
        code.function(&function);
        module.section(&code);
        module.finish()
    }

    #[cfg(feature = "wasmtime")]
    #[test]
    fn engines_agree_on_scalar_unit_signature_and_fuel() {
        let options = RunOptions { fuel: Some(100) };
        for result in [
            None,
            Some((ValType::I32, Instruction::I32Const(42))),
            Some((ValType::I64, Instruction::I64Const(-7))),
            Some((ValType::F32, Instruction::F32Const(1.25.into()))),
            Some((ValType::F64, Instruction::F64Const(2.5.into()))),
        ] {
            let bytes = module(result);
            assert_eq!(
                super::exec_with_capabilities(&bytes, "entry", &options, &[]),
                run_with(&bytes, "entry", &options)
            );
        }
        let mut bytes = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], []);
        let mut functions = FunctionSection::new();
        functions.function(0);
        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        let mut function = Function::new([]);
        function.instruction(&Instruction::Loop(BlockType::Empty));
        function.instruction(&Instruction::Br(0));
        function.instruction(&Instruction::End);
        function.instruction(&Instruction::End);
        let mut code = CodeSection::new();
        code.function(&function);
        bytes
            .section(&types)
            .section(&functions)
            .section(&exports)
            .section(&code);
        let bytes = bytes.finish();
        assert_eq!(
            run_with(&bytes, "entry", &options),
            Err(RunError::FuelExhausted)
        );
        assert_eq!(
            super::exec_with_capabilities(&bytes, "entry", &options, &[]),
            Err(RunError::FuelExhausted)
        );
    }

    #[test]
    fn returns_supported_scalar_values_and_unit() {
        assert_eq!(
            run_with_fuel(
                &module(Some((ValType::I32, Instruction::I32Const(42)))),
                "entry",
                100
            ),
            Ok(RunValue::I32(42))
        );
        assert_eq!(
            run_with_fuel(
                &module(Some((ValType::I64, Instruction::I64Const(-7)))),
                "entry",
                100
            ),
            Ok(RunValue::I64(-7))
        );
        assert_eq!(
            run_with_fuel(
                &module(Some((ValType::F32, Instruction::F32Const(1.25.into())))),
                "entry",
                100
            ),
            Ok(RunValue::F32(1.25))
        );
        assert_eq!(
            run_with_fuel(
                &module(Some((ValType::F64, Instruction::F64Const(2.5.into())))),
                "entry",
                100
            ),
            Ok(RunValue::F64(2.5))
        );
        assert_eq!(
            run_with_fuel(&module(None), "entry", 100),
            Ok(RunValue::Unit)
        );
    }

    #[test]
    fn reports_invalid_module_and_missing_export() {
        assert!(matches!(
            run_with_fuel(b"bad", "entry", 100),
            Err(RunError::Validate(_))
        ));
        assert!(matches!(
            run_with_fuel(&module(None), "missing", 100),
            Err(RunError::MissingExport(_))
        ));
    }

    #[cfg(feature = "wasmtime")]
    #[test]
    fn engines_reject_mismatched_host_import_and_parameterized_entry() {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([ValType::I64], []);
        let mut imports = ImportSection::new();
        imports.import("memobits:console", "write_i32", EntityType::Function(0));
        module.section(&types).section(&imports);
        let bytes = module.finish();
        let capability = [super::HostCapability::ConsoleWriteI32];
        let options = RunOptions::default();
        assert_eq!(
            super::run_with_capabilities(&bytes, "entry", &options, &capability),
            super::exec_with_capabilities(&bytes, "entry", &options, &capability)
        );
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([ValType::I32], []);
        let mut functions = FunctionSection::new();
        functions.function(0);
        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        let mut code = CodeSection::new();
        let mut function = Function::new([]);
        function.instruction(&Instruction::End);
        code.function(&function);
        module
            .section(&types)
            .section(&functions)
            .section(&exports)
            .section(&code);
        let bytes = module.finish();
        assert_eq!(
            super::run_with_capabilities(&bytes, "entry", &options, &[]),
            super::exec_with_capabilities(&bytes, "entry", &options, &[])
        );
    }

    #[test]
    fn rejects_imports_with_their_names() {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], []);
        module.section(&types);
        let mut imports = ImportSection::new();
        imports.import("env", "host_call", EntityType::Function(0));
        module.section(&imports);

        assert_eq!(
            run_with_fuel(&module.finish(), "entry", 100),
            Err(RunError::UnsupportedImport {
                module: "env".into(),
                name: "host_call".into()
            })
        );
    }

    #[test]
    fn rejects_nonzero_parameter_exports_before_calling() {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([ValType::I32], []);
        module.section(&types);
        let mut functions = FunctionSection::new();
        functions.function(0);
        module.section(&functions);
        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        module.section(&exports);
        let mut code = CodeSection::new();
        let mut function = Function::new([]);
        function.instruction(&Instruction::End);
        code.function(&function);
        module.section(&code);

        assert!(matches!(
            run_with_fuel(&module.finish(), "entry", 100),
            Err(RunError::Signature(_))
        ));
    }

    #[test]
    fn reports_guest_traps_and_fuel_exhaustion() {
        let trap = module(Some((ValType::I32, Instruction::Unreachable)));
        assert!(matches!(
            run_with_fuel(&trap, "entry", 100),
            Err(RunError::Trap(_))
        ));

        let mut infinite_loop = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], []);
        infinite_loop.section(&types);
        let mut functions = FunctionSection::new();
        functions.function(0);
        infinite_loop.section(&functions);
        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        infinite_loop.section(&exports);
        let mut code = CodeSection::new();
        let mut function = Function::new([]);
        function.instruction(&Instruction::Loop(BlockType::Empty));
        function.instruction(&Instruction::Br(0));
        function.instruction(&Instruction::End);
        function.instruction(&Instruction::End);
        code.function(&function);
        infinite_loop.section(&code);
        let infinite_loop = infinite_loop.finish();
        assert_eq!(
            run_with_fuel(&infinite_loop, "entry", 100),
            Err(RunError::FuelExhausted)
        );
    }

    #[test]
    fn unlimited_runs_are_unmetered_while_fuel_limits_apply() {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], [ValType::I32]);
        module.section(&types);
        let mut functions = FunctionSection::new();
        functions.function(0);
        module.section(&functions);
        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        module.section(&exports);
        let limit = 100_000;
        let mut code = CodeSection::new();
        let mut function = Function::new([(1, ValType::I32)]);
        function.instruction(&Instruction::Loop(BlockType::Empty));
        function.instruction(&Instruction::LocalGet(0));
        function.instruction(&Instruction::I32Const(1));
        function.instruction(&Instruction::I32Add);
        function.instruction(&Instruction::LocalTee(0));
        function.instruction(&Instruction::I32Const(limit));
        function.instruction(&Instruction::I32LtS);
        function.instruction(&Instruction::BrIf(0));
        function.instruction(&Instruction::End);
        function.instruction(&Instruction::LocalGet(0));
        function.instruction(&Instruction::End);
        code.function(&function);
        module.section(&code);
        let bytes = module.finish();

        assert_eq!(
            run_with(&bytes, "entry", &RunOptions { fuel: None }),
            Ok(RunValue::I32(limit))
        );
        assert_eq!(
            run_with(&bytes, "entry", &RunOptions { fuel: Some(1000) }),
            Err(RunError::FuelExhausted)
        );
        assert_eq!(
            run_with(
                &bytes,
                "entry",
                &RunOptions {
                    fuel: Some(10_000_000)
                }
            ),
            Ok(RunValue::I32(limit))
        );
    }

    #[test]
    fn classifies_start_function_traps() {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], []);
        module.section(&types);
        let mut functions = FunctionSection::new();
        functions.function(0);
        module.section(&functions);
        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        module.section(&exports);
        module.section(&StartSection { function_index: 0 });
        let mut code = CodeSection::new();
        let mut function = Function::new([]);
        function.instruction(&Instruction::Unreachable);
        function.instruction(&Instruction::End);
        code.function(&function);
        module.section(&code);

        assert!(matches!(
            run_with_fuel(&module.finish(), "entry", 100),
            Err(RunError::Trap(_))
        ));
    }

    #[test]
    fn flagged_unreachable_traps_report_stack_overflow() {
        use wasm_encoder::{ConstExpr, GlobalSection, GlobalType};
        for (flag, overflow) in [(1, true), (0, false)] {
            let mut module = Module::new();
            let mut types = TypeSection::new();
            types.ty().function([], []);
            module.section(&types);
            let mut functions = FunctionSection::new();
            functions.function(0);
            module.section(&functions);
            let mut globals = GlobalSection::new();
            globals.global(
                GlobalType {
                    val_type: ValType::I32,
                    mutable: true,
                    shared: false,
                },
                &ConstExpr::i32_const(flag),
            );
            module.section(&globals);
            let mut exports = ExportSection::new();
            exports.export("entry", ExportKind::Func, 0);
            exports.export("__mb_stack_overflow", ExportKind::Global, 0);
            module.section(&exports);
            let mut code = CodeSection::new();
            let mut function = Function::new([]);
            function.instruction(&Instruction::Unreachable);
            function.instruction(&Instruction::End);
            code.function(&function);
            module.section(&code);
            let result = run_with_fuel(&module.finish(), "entry", 1000);
            if overflow {
                assert_eq!(result, Err(RunError::StackOverflow));
            } else {
                assert!(matches!(result, Err(RunError::Trap(_))));
            }
        }
    }

    /// A module whose `entry` stores `record` into the exported `__mb_trap`
    /// global and then runs `body`.
    fn trapping_module(record: i32, body: &[Instruction<'static>]) -> Vec<u8> {
        use wasm_encoder::{ConstExpr, GlobalSection, GlobalType};
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], []);
        module.section(&types);
        let mut functions = FunctionSection::new();
        functions.function(0);
        module.section(&functions);
        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(0),
        );
        module.section(&globals);
        let mut exports = ExportSection::new();
        exports.export("entry", ExportKind::Func, 0);
        exports.export("__mb_trap", ExportKind::Global, 0);
        module.section(&exports);
        let mut code = CodeSection::new();
        let mut function = Function::new([]);
        function.instruction(&Instruction::I32Const(record));
        function.instruction(&Instruction::GlobalSet(0));
        for instruction in body {
            function.instruction(instruction);
        }
        function.instruction(&Instruction::End);
        code.function(&function);
        module.section(&code);
        module.finish()
    }

    fn table() -> TrapTable {
        TrapTable {
            locations: vec![SourceLocation {
                file: "src/app.mb".into(),
                line: 3,
                column: 7,
                width: 5,
                text: "let x := a[9];".into(),
            }],
        }
    }

    #[test]
    fn trap_table_round_trips_through_a_custom_section() {
        let module = with_trap_table(&trapping_module(0, &[]), &table());
        let payload = custom_section(&module, TRAP_SECTION).unwrap();
        assert_eq!(TrapTable::decode(payload), Some(table()));
        assert_eq!(custom_section(&module, "other"), None);
        wasmi::Module::new(&wasmi::Engine::default(), &module[..]).unwrap();
        assert_eq!(TrapTable::decode(b"nonsense"), None);
        assert_eq!(table().get(0), None);
        assert_eq!(table().get(2), None);
    }

    #[test]
    fn explicit_checked_traps_report_reason_and_location() {
        let module = with_trap_table(
            &trapping_module((1 << 8) | 8, &[Instruction::Unreachable]),
            &table(),
        );
        let error = run_with_fuel(&module, "entry", 1000).unwrap_err();
        assert_eq!(
            error,
            RunError::Checked {
                reason: TrapReason::IndexOutOfBounds,
                location: table().get(1).cloned(),
            }
        );
        assert_eq!(
            error.to_string(),
            "array index out of bounds at src/app.mb:3:7"
        );
        // The same record without a table keeps the generic trap.
        assert!(matches!(
            run_with_fuel(
                &trapping_module((1 << 8) | 8, &[Instruction::Unreachable]),
                "entry",
                1000
            ),
            Err(RunError::Trap(_))
        ));
        // An unknown code is not a checked trap.
        let unknown = with_trap_table(&trapping_module(99, &[Instruction::Unreachable]), &table());
        assert!(matches!(
            run_with_fuel(&unknown, "entry", 1000),
            Err(RunError::Trap(_))
        ));
    }

    #[test]
    fn native_division_traps_are_refined_by_the_recorded_site() {
        let divide_by_zero = [
            Instruction::I32Const(1),
            Instruction::I32Const(0),
            Instruction::I32DivS,
            Instruction::Drop,
        ];
        let overflow = [
            Instruction::I32Const(i32::MIN),
            Instruction::I32Const(-1),
            Instruction::I32DivS,
            Instruction::Drop,
        ];
        for (record, body, reason) in [
            ((1 << 8) | 5, &divide_by_zero, TrapReason::DivisionByZero),
            ((1 << 8) | 6, &divide_by_zero, TrapReason::RemainderByZero),
            ((1 << 8) | 5, &overflow, TrapReason::DivisionOverflow),
        ] {
            let module = with_trap_table(&trapping_module(record, body), &table());
            let Err(RunError::Checked {
                reason: found,
                location,
            }) = run_with_fuel(&module, "entry", 1000)
            else {
                panic!("expected a checked trap");
            };
            assert_eq!(found, reason);
            assert_eq!(location, table().get(1).cloned());
        }
        // A division code left over from a successful division must not label
        // an unrelated `unreachable`.
        let stale = with_trap_table(
            &trapping_module((1 << 8) | 5, &[Instruction::Unreachable]),
            &table(),
        );
        assert!(matches!(
            run_with_fuel(&stale, "entry", 1000),
            Err(RunError::Trap(_))
        ));
    }
}
