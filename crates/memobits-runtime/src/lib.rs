//! Small, fuel-limited WebAssembly runner for zero-argument exports.
//!
//! This crate runs modules with no imports and accepts only scalar Wasm
//! results. It preserves Wasm's numeric representation; it has no source type
//! metadata to distinguish signed from unsigned integers.

use wasmi::{
    Config, Engine, Error as WasmiError, ExternType, Instance, Module, Store, TrapCode, Val,
    ValType,
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

impl Default for RunOptions {
    /// Metered execution with [`DEFAULT_FUEL`].
    fn default() -> Self {
        Self {
            fuel: Some(DEFAULT_FUEL),
        }
    }
}

/// A scalar result in the WebAssembly representation.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RunValue {
    /// The function returned no Wasm values.
    Unit,
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
}

/// An error while validating, instantiating, or calling a module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunError {
    /// The module could not be parsed or validated.
    Validate(String),
    /// The module requires a host import, which this runner does not provide.
    UnsupportedImport { module: String, name: String },
    /// The module could not be instantiated.
    Instantiate(String),
    /// The requested name is absent or does not refer to a function.
    MissingExport(String),
    /// The function has parameters or an unsupported result signature.
    Signature(String),
    /// The guest exhausted the execution fuel budget.
    FuelExhausted,
    /// The guest trapped while running.
    Trap(String),
    /// The guest ran out of its configured stack (`[build].stack_size`).
    StackOverflow,
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
            Self::FuelExhausted => f.write_str("WebAssembly execution fuel exhausted"),
            Self::Trap(message) => write!(f, "WebAssembly execution trapped: {message}"),
            Self::StackOverflow => f.write_str(
                "stack overflow: the program exhausted its stack; raise [build].stack_size or reduce recursion depth",
            ),
        }
    }
}

impl std::error::Error for RunError {}

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
    let mut config = Config::default();
    config.consume_fuel(options.fuel.is_some());
    let engine = Engine::new(&config);
    let module =
        Module::new(&engine, bytes).map_err(|error| RunError::Validate(error.to_string()))?;

    if let Some(import) = module.imports().next() {
        return Err(RunError::UnsupportedImport {
            module: import.module().to_owned(),
            name: import.name().to_owned(),
        });
    }

    let export_type = module
        .get_export(export)
        .ok_or_else(|| RunError::MissingExport(export.to_owned()))?;
    let function_type = match export_type {
        ExternType::Func(function_type) => function_type,
        _ => return Err(RunError::MissingExport(export.to_owned())),
    };
    if !function_type.params().is_empty() {
        return Err(RunError::Signature(format!(
            "'{export}' takes {} parameter(s); this runner accepts no arguments",
            function_type.params().len()
        )));
    }
    if function_type.results().len() > 1 {
        return Err(RunError::Signature(format!(
            "'{export}' returns multiple values"
        )));
    }
    let result_type = function_type.results().first().copied();
    if result_type.is_some_and(|ty| {
        !matches!(
            ty,
            ValType::I32 | ValType::I64 | ValType::F32 | ValType::F64
        )
    }) {
        return Err(RunError::Signature(format!(
            "'{export}' returns an unsupported Wasm type {:?}",
            result_type.expect("checked Some")
        )));
    }

    let mut store = Store::new(&engine, ());
    if let Some(fuel) = options.fuel {
        store
            .set_fuel(fuel)
            .map_err(|error| RunError::Instantiate(error.to_string()))?;
    }
    let instance = Instance::new(&mut store, &module, &[]).map_err(classify_instantiation)?;
    let function = instance
        .get_func(&store, export)
        .ok_or_else(|| RunError::MissingExport(export.to_owned()))?;
    let mut results = result_type
        .map(Val::default_for_ty)
        .into_iter()
        .collect::<Vec<_>>();
    if let Err(error) = function.call(&mut store, &[], &mut results) {
        // Stack exhaustion sets an exported flag global before trapping, which
        // is how it is told apart from other `unreachable` traps.
        let overflowed = instance
            .get_global(&store, STACK_OVERFLOW_EXPORT)
            .is_some_and(|flag| flag.get(&store).i32() == Some(1));
        return Err(
            if overflowed && error.as_trap_code() != Some(TrapCode::OutOfFuel) {
                RunError::StackOverflow
            } else {
                classify_call(error)
            },
        );
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
    use super::{run_with, RunError, RunOptions, RunValue};
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
}
