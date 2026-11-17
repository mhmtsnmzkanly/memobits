use memobits_diagnostics::{
    render, render_with, write_location, Category, Diagnostic, DiagnosticCode, Severity,
    SourceFile, SourceId, Span,
};
use memobits_ir::{FunctionId, Primitive, Program, Type};
use memobits_project::{DependencyKind, Error, Project};
use memobits_resolve::{resolve, Target};
use std::{
    collections::BTreeMap,
    ffi::OsString,
    fmt::Write,
    fs::{self, OpenOptions},
    io::Write as IoWrite,
    path::{Path, PathBuf},
    process::ExitCode,
    sync::atomic::{AtomicU64, Ordering},
};

const HELP: &str = "Memobits project tools\n\nUsage: mb project [--project PATH]\n       mb syntax FILE\n       mb analyze FILE\n       mb ownership FILE\n       mb resolve [--project PATH] [--lib]\n       mb analyze-project [--project PATH] [--lib]\n       mb ownership-project [--project PATH] [--lib]\n       mb build [--project PATH] [--lib] [--output PATH]\n       mb run [--project PATH] [--fuel N | --no-fuel-limit]\n       mb run FILE.wasm [--entry NAME] [--fuel N | --no-fuel-limit]\n       mb --help\n\nCommands:\n  syntax FILE      Parse one source file (no semantic checking)\n  analyze FILE     Check standalone primitive types and loop control\n  ownership FILE   Check primitive moves and loans in one source file\n  analyze-project  Check primitive types across reachable local modules\n  ownership-project Check primitive moves and loans across reachable local modules\n  build            Compile the selected target to WebAssembly\n  run              Run the application entry or a Wasm artifact\n  project          Display the manifest and sorted source-module inventory\n  resolve          Resolve reachable local modules and names from the target root\n\nOptions:\n  --project PATH   Select a manifest file (default: ./project.toml)\n  --lib            Resolve library exports instead of the application entry\n  --output PATH    Write the Wasm artifact at PATH\n  --entry NAME     Select an export in a Wasm artifact (default: main)\n  --fuel N         Run with at most N fuel units (positive integer; default 10000000000)\n  --no-fuel-limit  Run without an execution fuel limit\n  -h, --help       Show this help\n\nBuild defaults to target/memobits/app.wasm or target/memobits/library.wasm beside the selected manifest. Build supports the primitive Wasm subset and exported functions only. Run uses the same WebAssembly runtime for project source and artifacts, applies a bounded default fuel budget (see --fuel), and prints scalar results without using them as the process exit code. The project ownership command checks the supported primitive subset; success is not a borrow-safety guarantee. The standalone ownership command checks primitive moves and loans; internal primitive references execute in Wasm; external reference signatures remain unsupported, and success is not a complete safety guarantee. check is not supported yet.\n";

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

fn diagnostic(number: u16, message: impl Into<String>) -> String {
    render(
        &Diagnostic::new(
            DiagnosticCode::new(Category::Project, number).expect("static PE code"),
            Severity::Error,
            message,
        ),
        None,
    )
}

fn backend_options(project: &Project) -> memobits_wasm::CompileOptions {
    memobits_wasm::CompileOptions {
        stack_size: project.manifest.stack_size(),
    }
}

fn project_error(error: Error) -> String {
    let code = match &error {
        Error::Io { .. } => 1,
        Error::Toml(_) => 2,
        Error::Invalid(_) => 3,
        Error::Build(_) => 7,
    };
    diagnostic(code, error.to_string())
}

fn render_in(diagnostic: &Diagnostic, resolution: &memobits_resolve::Resolution) -> String {
    render_with(diagnostic, &|id| {
        resolution
            .modules
            .values()
            .find(|module| module.id == id)
            .map(|module| SourceFile {
                id: module.id,
                name: module.path.to_str().unwrap_or("<source>"),
                text: &module.text,
            })
    })
}

fn render_source_diagnostics(
    diagnostics: &[Diagnostic],
    resolution: &memobits_resolve::Resolution,
) -> String {
    diagnostics
        .iter()
        .map(|diagnostic| render_in(diagnostic, resolution))
        .collect()
}

fn canonical_function_id(program: &Program, target: &str) -> Option<FunctionId> {
    let target = target.strip_prefix("self::").unwrap_or(target);
    let (module, name) = target.rsplit_once("::")?;
    program
        .functions
        .iter()
        .position(|function| {
            function.path.module.join("::") == module && function.path.name == name
        })
        .map(|index| FunctionId(index as u32))
}

fn is_type_export(resolution: &memobits_resolve::Resolution, target: &str) -> bool {
    let target = target.strip_prefix("self::").unwrap_or(target);
    let Some((module, name)) = target.rsplit_once("::") else {
        return false;
    };
    resolution.modules.get(module).is_some_and(|source| {
        source.syntax.items.iter().any(|item| {
            matches!(&item.kind, memobits_syntax::ItemKind::Type { name: type_name, .. } if type_name == name)
        })
    })
}

fn build_exports(
    project: &Project,
    resolution: &memobits_resolve::Resolution,
    program: &Program,
    library: bool,
) -> Result<BTreeMap<String, FunctionId>, String> {
    let mut exports = BTreeMap::new();
    if library {
        for (alias, target) in &project.manifest.export {
            let Some(function) = canonical_function_id(program, target) else {
                if is_type_export(resolution, target) {
                    return Err(diagnostic(
                        6,
                        format!("type export '{alias}' is unsupported by the Wasm backend"),
                    ));
                }
                return Err(diagnostic(
                    6,
                    format!("library export '{alias}' does not identify a lowered function"),
                ));
            };
            exports.insert(alias.clone(), function);
        }
    } else {
        let entry = project
            .manifest
            .package
            .entry
            .as_deref()
            .ok_or_else(|| diagnostic(6, "application build requires package.entry"))?;
        let function = canonical_function_id(program, entry).ok_or_else(|| {
            diagnostic(
                6,
                format!("application entry '{entry}' is not a lowered function"),
            )
        })?;
        exports.insert("main".into(), function);
    }
    Ok(exports)
}

fn default_build_output(project: &Project, library: bool) -> PathBuf {
    project
        .manifest_path
        .parent()
        .unwrap_or(Path::new("."))
        .join("target")
        .join("memobits")
        .join(if library { "library.wasm" } else { "app.wasm" })
}

fn write_atomically(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent)
        .map_err(|error| diagnostic(1, format!("{}: {error}", parent.display())))?;
    let mut temp_path = None;
    let mut temp_file = None;
    for _ in 0..16 {
        let sequence = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let candidate = parent.join(format!(
            ".memobits-build-{}-{sequence}.tmp",
            std::process::id()
        ));
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&candidate)
        {
            Ok(file) => {
                temp_path = Some(candidate);
                temp_file = Some(file);
                break;
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(diagnostic(1, format!("{}: {error}", candidate.display()))),
        }
    }
    let Some(temp_path) = temp_path else {
        return Err(diagnostic(1, "could not allocate a temporary build output"));
    };
    let mut temp_file = temp_file.expect("temporary file path and handle are paired");
    if let Err(error) = temp_file
        .write_all(bytes)
        .and_then(|()| temp_file.sync_all())
    {
        let _ = fs::remove_file(&temp_path);
        return Err(diagnostic(1, format!("{}: {error}", temp_path.display())));
    }
    drop(temp_file);
    if let Err(error) = fs::rename(&temp_path, path) {
        let _ = fs::remove_file(&temp_path);
        return Err(diagnostic(1, format!("{}: {error}", path.display())));
    }
    Ok(())
}

fn runtime_error(error: memobits_runtime::RunError) -> String {
    use memobits_runtime::RunError;
    let code = match &error {
        RunError::Validate(_) => 1,
        RunError::UnsupportedImport { .. } => 2,
        RunError::Instantiate(_) => 3,
        RunError::MissingExport(_) => 4,
        RunError::Signature(_) => 5,
        RunError::FuelExhausted => 6,
        RunError::Trap(_) => 7,
        RunError::StackOverflow => 8,
        RunError::Checked { .. } => 7,
    };
    let message = match &error {
        RunError::FuelExhausted => format!(
            "{error}; raise the budget with --fuel N or run without a limit using --no-fuel-limit"
        ),
        _ => error.to_string(),
    };
    if let RunError::Checked {
        reason,
        location: Some(location),
    } = &error
    {
        let mut output = format!("error[RE{code:03}]: {}\n", reason.message());
        write_location(
            &mut output,
            &location.file,
            location.line as usize,
            location.column as usize,
            location.width as usize,
            &location.text,
        );
        return output;
    }
    let message = match &error {
        RunError::Checked { reason, .. } => reason.message().to_owned(),
        _ => message,
    };
    render(
        &Diagnostic::new(
            DiagnosticCode::new(Category::Runtime, code).expect("static RE code"),
            Severity::Error,
            message,
        ),
        None,
    )
}

/// Resolve a trap-site span to a position with its source line.
fn locate(
    span: Span,
    resolution: &memobits_resolve::Resolution,
) -> memobits_runtime::SourceLocation {
    let blank = memobits_runtime::SourceLocation {
        file: String::new(),
        line: 0,
        column: 0,
        width: 1,
        text: String::new(),
    };
    let Some(module) = resolution.modules.values().find(|m| m.id == span.source) else {
        return blank;
    };
    let text = &module.text;
    if span.start > span.end
        || span.end > text.len()
        || !text.is_char_boundary(span.start)
        || !text.is_char_boundary(span.end)
    {
        return blank;
    }
    let line_start = text[..span.start].rfind('\n').map_or(0, |n| n + 1);
    let line_end = text[span.start..]
        .find('\n')
        .map_or(text.len(), |n| span.start + n);
    memobits_runtime::SourceLocation {
        file: module.path.to_str().unwrap_or("<source>").to_owned(),
        line: (text[..span.start].bytes().filter(|&b| b == b'\n').count() + 1) as u32,
        column: (text[line_start..span.start].chars().count() + 1) as u32,
        width: text[span.start..span.end.min(line_end)]
            .chars()
            .count()
            .max(1) as u32,
        text: text[line_start..line_end].trim_end_matches('\r').to_owned(),
    }
}

/// Compile and attach the trap location table as the `memobits.traps` custom
/// section, so source runs and built artifacts report trap locations alike.
fn compile_with_locations(
    program: &Program,
    exports: &BTreeMap<String, FunctionId>,
    options: &memobits_wasm::CompileOptions,
    resolution: &memobits_resolve::Resolution,
) -> Result<Vec<u8>, String> {
    let compiled = memobits_wasm::compile_traced(program, exports, options)
        .map_err(|diagnostics| render_source_diagnostics(&diagnostics, resolution))?;
    if compiled.trap_sites.is_empty() {
        return Ok(compiled.bytes);
    }
    let table = memobits_runtime::TrapTable {
        locations: compiled
            .trap_sites
            .iter()
            .map(|span| locate(*span, resolution))
            .collect(),
    };
    Ok(memobits_runtime::with_trap_table(&compiled.bytes, &table))
}

/// The `--fuel N` and `--no-fuel-limit` options shared by both run forms.
#[derive(Default)]
struct FuelArgs {
    limit: Option<u64>,
    unlimited: bool,
}

impl FuelArgs {
    /// Consumes `arg` (and its value, if any) when it is a fuel option.
    fn take(
        &mut self,
        arg: &OsString,
        args: &mut impl Iterator<Item = OsString>,
    ) -> Result<bool, String> {
        match arg.to_str() {
            Some("--no-fuel-limit") => {
                if self.unlimited {
                    return Err(diagnostic(4, "--no-fuel-limit may only be specified once"));
                }
                self.unlimited = true;
                Ok(true)
            }
            Some("--fuel") => {
                if self.limit.is_some() {
                    return Err(diagnostic(4, "--fuel may only be specified once"));
                }
                let value = args
                    .next()
                    .ok_or_else(|| diagnostic(4, "--fuel requires a positive integer"))?;
                let text = value.to_string_lossy();
                let limit = text
                    .parse::<u64>()
                    .ok()
                    .filter(|limit| *limit > 0)
                    .ok_or_else(|| {
                        diagnostic(
                            4,
                            format!("--fuel requires a positive integer, found '{text}'"),
                        )
                    })?;
                self.limit = Some(limit);
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn options(&self) -> Result<memobits_runtime::RunOptions, String> {
        if self.unlimited && self.limit.is_some() {
            return Err(diagnostic(
                4,
                "--fuel and --no-fuel-limit cannot be used together",
            ));
        }
        Ok(memobits_runtime::RunOptions {
            fuel: if self.unlimited {
                None
            } else {
                Some(self.limit.unwrap_or(memobits_runtime::DEFAULT_FUEL))
            },
        })
    }
}

fn display_run_value(value: memobits_runtime::RunValue, ty: Option<&Type>) -> String {
    use memobits_runtime::RunValue;
    match (value, ty) {
        (RunValue::Unit, _) | (RunValue::I32(_), Some(Type::Primitive(Primitive::Unit))) => {
            "Unit".into()
        }
        (RunValue::I32(value), Some(Type::Primitive(Primitive::Bool))) => {
            format!("Bool({})", value != 0)
        }
        (RunValue::I32(value), Some(Type::Primitive(Primitive::I8))) => {
            format!("i8({})", value as i8)
        }
        (RunValue::I32(value), Some(Type::Primitive(Primitive::I16))) => {
            format!("i16({})", value as i16)
        }
        (RunValue::I32(value), Some(Type::Primitive(Primitive::U8))) => {
            format!("u8({})", value as u8)
        }
        (RunValue::I32(value), Some(Type::Primitive(Primitive::U16))) => {
            format!("u16({})", value as u16)
        }
        (RunValue::I32(value), Some(Type::Primitive(Primitive::U32))) => {
            format!("u32({})", value as u32)
        }
        (RunValue::I64(value), Some(Type::Primitive(Primitive::I64))) => {
            format!("i64({value})")
        }
        (RunValue::I64(value), Some(Type::Primitive(Primitive::U64))) => {
            format!("u64({})", value as u64)
        }
        (RunValue::F32(value), Some(Type::Primitive(Primitive::F32))) => {
            format!("f32({value:?})")
        }
        (RunValue::F64(value), Some(Type::Primitive(Primitive::F64))) => {
            format!("f64({value:?})")
        }
        (RunValue::I32(value), _) => format!("i32({value})"),
        (RunValue::I64(value), _) => format!("i64({value})"),
        (RunValue::F32(value), _) => format!("f32({value:?})"),
        (RunValue::F64(value), _) => format!("f64({value:?})"),
    }
}

fn run_command(arguments: Vec<OsString>) -> Result<String, String> {
    if arguments
        .first()
        .is_some_and(|arg| arg == "--help" || arg == "-h")
    {
        if arguments.len() != 1 {
            return Err(diagnostic(4, "unexpected arguments after --help"));
        }
        return Ok(HELP.into());
    }
    if arguments
        .first()
        .is_some_and(|arg| !arg.to_string_lossy().starts_with('-'))
    {
        let wasm_path = PathBuf::from(&arguments[0]);
        let mut entry = "main".to_owned();
        let mut explicit_entry = false;
        let mut fuel = FuelArgs::default();
        let mut args = arguments.into_iter().skip(1);
        while let Some(arg) = args.next() {
            if arg == "--help" || arg == "-h" {
                if args.next().is_some() {
                    return Err(diagnostic(4, "unexpected arguments after --help"));
                }
                return Ok(HELP.into());
            }
            if fuel.take(&arg, &mut args)? {
                continue;
            }
            if arg != "--entry" {
                return Err(diagnostic(
                    4,
                    format!(
                        "unexpected run argument '{}'; artifact mode accepts only --entry, --fuel, and --no-fuel-limit",
                        arg.to_string_lossy()
                    ),
                ));
            }
            if explicit_entry {
                return Err(diagnostic(4, "--entry may only be specified once"));
            }
            entry = args
                .next()
                .filter(|value| !value.is_empty() && !value.to_string_lossy().starts_with('-'))
                .map(|value| value.to_string_lossy().into_owned())
                .ok_or_else(|| diagnostic(4, "--entry requires an export name"))?;
            explicit_entry = true;
        }
        let run_options = fuel.options()?;
        let bytes = fs::read(&wasm_path)
            .map_err(|error| diagnostic(1, format!("{}: {error}", wasm_path.display())))?;
        let value =
            memobits_runtime::run_with(&bytes, &entry, &run_options).map_err(runtime_error)?;
        return Ok(format!("Result: {}\n", display_run_value(value, None)));
    }

    let mut selected = None;
    let mut fuel = FuelArgs::default();
    let mut args = arguments.into_iter();
    while let Some(arg) = args.next() {
        if arg == "--help" || arg == "-h" {
            if args.next().is_some() {
                return Err(diagnostic(4, "unexpected arguments after --help"));
            }
            return Ok(HELP.into());
        }
        if fuel.take(&arg, &mut args)? {
            continue;
        }
        if arg != "--project" {
            return Err(diagnostic(
                4,
                format!(
                    "source run accepts only --project, --fuel, and --no-fuel-limit, found '{}'",
                    arg.to_string_lossy()
                ),
            ));
        }
        if selected.is_some() {
            return Err(diagnostic(4, "--project may only be specified once"));
        }
        selected = Some(
            args.next()
                .filter(|value| !value.is_empty() && !value.to_string_lossy().starts_with('-'))
                .map(PathBuf::from)
                .ok_or_else(|| diagnostic(4, "--project requires a manifest path"))?,
        );
    }
    let run_options = fuel.options()?;
    let project = Project::load(".", selected.as_deref()).map_err(project_error)?;
    let resolution = resolve(&project, Target::Application);
    if !resolution.diagnostics.is_empty() {
        return Err(render_source_diagnostics(
            &resolution.diagnostics,
            &resolution,
        ));
    }
    let program = memobits_analysis::lower_resolved(&project, &resolution)
        .map_err(|diagnostics| render_source_diagnostics(&diagnostics, &resolution))?;
    let exports = build_exports(&project, &resolution, &program, false)?;
    let entry = exports["main"];
    let result_type = program.functions[entry.0 as usize]
        .signature
        .result
        .as_ref();
    let options = backend_options(&project);
    let bytes = compile_with_locations(&program, &exports, &options, &resolution)?;
    let value = memobits_runtime::run_with(&bytes, "main", &run_options).map_err(runtime_error)?;
    Ok(format!(
        "Result: {}\n",
        display_run_value(value, Some(result_type))
    ))
}

fn run(args: impl IntoIterator<Item = OsString>) -> Result<String, String> {
    let mut args = args.into_iter();
    let command = args
        .next()
        .ok_or_else(|| diagnostic(4, "expected a command; use mb --help"))?;
    if command == "--help" || command == "-h" {
        if args.next().is_some() {
            return Err(diagnostic(4, "unexpected arguments after --help"));
        }
        return Ok(HELP.into());
    }
    if command == "run" {
        return run_command(args.collect());
    }
    if command == "syntax" || command == "analyze" || command == "ownership" {
        let path = args
            .next()
            .ok_or_else(|| diagnostic(4, "source command requires a source file"))?;
        if path == "--help" || path == "-h" {
            if args.next().is_some() {
                return Err(diagnostic(4, "unexpected arguments after --help"));
            }
            return Ok(HELP.into());
        }
        if args.next().is_some() {
            return Err(diagnostic(
                4,
                "source command accepts exactly one source file",
            ));
        }
        let path = PathBuf::from(path);
        let text = std::fs::read_to_string(&path)
            .map_err(|e| diagnostic(1, format!("{}: {e}", path.display())))?;
        let mut parsed = memobits_syntax::parse(SourceId(0), &text);
        if command == "analyze" && parsed.diagnostics.is_empty() {
            parsed
                .diagnostics
                .extend(memobits_analysis::check_control_flow(&parsed.module));
            parsed
                .diagnostics
                .extend(memobits_analysis::check_types(&parsed.module));
        }
        if !parsed.diagnostics.is_empty() {
            let name = path.display().to_string();
            let source = SourceFile {
                id: SourceId(0),
                name: &name,
                text: &text,
            };
            return Err(parsed
                .diagnostics
                .iter()
                .map(|d| render(d, Some(source)))
                .collect::<String>());
        }
        if command == "ownership" {
            let program =
                memobits_analysis::lower_module(&parsed.module, "standalone", &["source".into()])
                    .map_err(|diagnostics| {
                    let name = path.display().to_string();
                    let source = SourceFile {
                        id: SourceId(0),
                        name: &name,
                        text: &text,
                    };
                    diagnostics
                        .iter()
                        .map(|d| render(d, Some(source)))
                        .collect::<String>()
                })?;
            let diagnostics = memobits_ownership::check_ownership(&program);
            if !diagnostics.is_empty() {
                let name = path.display().to_string();
                let source = SourceFile {
                    id: SourceId(0),
                    name: &name,
                    text: &text,
                };
                return Err(diagnostics
                    .iter()
                    .map(|d| render(d, Some(source)))
                    .collect());
            }
            return Ok(format!("Ownership check passed: {} (owned moves checked; primitive loans checked; internal primitive references supported)\n", path.display()));
        }
        if command == "analyze" {
            return Ok(format!("Primitive analysis passed: {} (standalone types and loop control checked; ownership not checked)\n", path.display()));
        }
        return Ok(format!(
            "Syntax valid: {} ({} declarations; semantics not checked)\n",
            path.display(),
            parsed.module.items.len()
        ));
    }
    if command == "check" {
        return Err(diagnostic(
            5,
            format!(
                "command '{}' is unsupported; use project, syntax, resolve, analyze, ownership, analyze-project, or ownership-project",
                command.to_string_lossy()
            ),
        ));
    }
    if command != "project"
        && command != "resolve"
        && command != "analyze-project"
        && command != "ownership-project"
        && command != "build"
    {
        return Err(diagnostic(
            4,
            format!(
                "unknown command '{}'; use mb --help",
                command.to_string_lossy()
            ),
        ));
    }
    let mut selected = None;
    let mut library = false;
    let mut output = None;
    while let Some(arg) = args.next() {
        if arg == "--help" || arg == "-h" {
            if args.next().is_some() {
                return Err(diagnostic(4, "unexpected arguments after --help"));
            }
            return Ok(HELP.into());
        }
        if arg == "--lib"
            && (command == "resolve"
                || command == "analyze-project"
                || command == "ownership-project"
                || command == "build")
        {
            if library {
                return Err(diagnostic(4, "--lib may only be specified once"));
            }
            library = true;
            continue;
        }
        if arg == "--output" && command == "build" {
            if output.is_some() {
                return Err(diagnostic(4, "--output may only be specified once"));
            }
            let value = args
                .next()
                .filter(|value| !value.is_empty() && !value.to_string_lossy().starts_with('-'))
                .ok_or_else(|| diagnostic(4, "--output requires a file path"))?;
            output = Some(PathBuf::from(value));
            continue;
        }
        if arg != "--project" {
            return Err(diagnostic(
                4,
                format!(
                    "unexpected argument '{}'; use mb --help",
                    arg.to_string_lossy()
                ),
            ));
        }
        if selected.is_some() {
            return Err(diagnostic(4, "--project may only be specified once"));
        }
        let value = args
            .next()
            .filter(|v| !v.is_empty() && !v.to_string_lossy().starts_with('-'))
            .ok_or_else(|| diagnostic(4, "--project requires a manifest path"))?;
        selected = Some(PathBuf::from(value));
    }
    let project = Project::load(".", selected.as_deref()).map_err(project_error)?;
    if command == "resolve"
        || command == "analyze-project"
        || command == "ownership-project"
        || command == "build"
    {
        let target = if library {
            Target::Library
        } else {
            Target::Application
        };
        let mut result = resolve(&project, target);
        if command == "build" && result.diagnostics.is_empty() && library {
            if let Some((alias, _target)) = project
                .manifest
                .export
                .iter()
                .find(|(_, target)| is_type_export(&result, target))
            {
                return Err(diagnostic(
                    6,
                    format!("type export '{alias}' is unsupported by the Wasm backend"),
                ));
            }
        }
        if command == "analyze-project" && result.diagnostics.is_empty() {
            let mut diagnostics = memobits_analysis::check_resolved_types(&project, &result);
            for module in result.modules.values() {
                diagnostics.extend(memobits_analysis::check_control_flow(&module.syntax));
            }
            result.diagnostics.extend(diagnostics);
        }
        if command == "ownership-project" && result.diagnostics.is_empty() {
            let program =
                memobits_analysis::lower_resolved(&project, &result).map_err(|diagnostics| {
                    diagnostics
                        .iter()
                        .map(|d| render_in(d, &result))
                        .collect::<String>()
                })?;
            result
                .diagnostics
                .extend(memobits_ownership::check_ownership(&program));
        }
        if command == "build" && result.diagnostics.is_empty() {
            let program = memobits_analysis::lower_resolved(&project, &result)
                .map_err(|diagnostics| render_source_diagnostics(&diagnostics, &result))?;
            let exports = build_exports(&project, &result, &program, library)?;
            let options = backend_options(&project);
            let bytes = compile_with_locations(&program, &exports, &options, &result)?;
            let output_path = output
                .clone()
                .unwrap_or_else(|| default_build_output(&project, library));
            write_atomically(&output_path, &bytes)?;
            return Ok(format!(
                "Built {}: {} export(s), {} bytes\n",
                output_path.display(),
                exports.len(),
                bytes.len()
            ));
        }
        if !result.diagnostics.is_empty() {
            return Err(result
                .diagnostics
                .iter()
                .map(|d| render_in(d, &result))
                .collect::<String>());
        }
        let target_name = if library {
            "library exports"
        } else {
            "application entry"
        };
        if command == "analyze-project" {
            return Ok(format!("Primitive project analysis passed: {target_name} ({} reachable modules; ownership not checked)\n", result.modules.len()));
        }
        if command == "ownership-project" {
            return Ok(format!("Ownership project check passed: {target_name} ({} reachable modules; supported primitive moves and loans checked; borrow safety not guaranteed)\n", result.modules.len()));
        }
        let mut output = format!(
            "Resolved {target_name}: {} reachable module(s) (names checked; further semantics, types, and ownership not checked)\n",
            result.modules.len()
        );
        for (name, module) in result.modules {
            let relative = module
                .path
                .strip_prefix(&project.source_root)
                .unwrap_or(&module.path);
            let _ = writeln!(output, "  {name} -> {}", relative.display());
        }
        return Ok(output);
    }
    let manifest = &project.manifest;
    let mut output = format!(
        "Manifest: {}\nPackage: {}\n",
        project.manifest_path.display(),
        manifest.package.name
    );
    if let Some(version) = &manifest.package.version {
        let _ = writeln!(output, "Version: {version}");
    }
    if let Some(entry) = &manifest.package.entry {
        let _ = writeln!(output, "Entry: {entry}");
    }
    let _ = writeln!(output, "Source root: {}", project.source_root.display());
    for (title, entries) in [
        ("Exports", &manifest.export),
        ("Prelude", &manifest.prelude),
    ] {
        let _ = writeln!(output, "{title} ({}):", entries.len());
        for (alias, target) in entries {
            let _ = writeln!(output, "  {alias} -> {target}");
        }
    }
    let _ = writeln!(output, "Dependencies ({}):", manifest.dependencies.len());
    for (name, dependency) in &manifest.dependencies {
        let kind = match dependency.kind {
            DependencyKind::Source => "source",
            DependencyKind::Binary => "binary",
        };
        let _ = writeln!(
            output,
            "  {name}: type={kind}, src={:?}, import={:?}, external={}",
            dependency.src, dependency.import, dependency.external
        );
    }
    let _ = writeln!(output, "Modules ({}):", project.modules.len());
    for module in &project.modules {
        let relative = module
            .path
            .strip_prefix(&project.source_root)
            .unwrap_or(&module.path);
        let _ = writeln!(output, "  {} -> {}", module.name, relative.display());
    }
    Ok(output)
}

fn main() -> ExitCode {
    match run(std::env::args_os().skip(1)) {
        Ok(output) => {
            print!("{output}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprint!("{error}");
            ExitCode::FAILURE
        }
    }
}
