//! The trap record protocol: which sites exist and what a check stores.
use memobits_analysis::lower_module;
use memobits_diagnostics::SourceId;
use memobits_ir::FunctionId;
use memobits_syntax::parse;
use memobits_wasm::{compile_traced, CompileOptions, TrapReason, TRAP_EXPORT};
use std::collections::BTreeMap;
use wasmi::{Engine, Linker, Module, Store};

fn compile(source: &str) -> memobits_wasm::Compiled {
    let parsed = parse(SourceId(0), source);
    assert!(parsed.diagnostics.is_empty());
    let program = lower_module(&parsed.module, "test", &["main".into()]).unwrap();
    let main = program.functions.len() as u32 - 1;
    let exports = BTreeMap::from([("main".to_string(), FunctionId(main))]);
    compile_traced(&program, &exports, &CompileOptions::default()).unwrap()
}

/// Run `main` and return the packed trap record after it traps.
fn record_after_trap(bytes: &[u8]) -> i32 {
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    let main = instance.get_typed_func::<(), i32>(&store, "main").unwrap();
    assert!(main.call(&mut store, ()).is_err());
    instance
        .get_global(&store, TRAP_EXPORT)
        .unwrap()
        .get(&store)
        .i32()
        .unwrap()
}

#[test]
fn a_failed_check_stores_reason_and_location_before_trapping() {
    let source = "fn main() -> i32 { var a := 2147483647; a + 1 }";
    let compiled = compile(source);
    assert_eq!(compiled.trap_sites.len(), 1);
    let span = compiled.trap_sites[0];
    assert_eq!(&source[span.start..span.end], "a + 1");
    let record = record_after_trap(&compiled.bytes);
    assert_eq!(record & 0xff, i32::from(TrapReason::Add.code()));
    assert_eq!(record >> 8, 1);
}

#[test]
fn each_checking_site_gets_its_own_location_id() {
    let source = "fn main() -> i32 { var a := 2147483647; var b := 1; let c := a - b; c * 2 + 1 }";
    let compiled = compile(source);
    assert_eq!(compiled.trap_sites.len(), 3);
    let record = record_after_trap(&compiled.bytes);
    // `a - b` succeeds and `c * 2` is the first failure: location 2.
    assert_eq!(record & 0xff, i32::from(TrapReason::Multiply.code()));
    assert_eq!(record >> 8, 2);
}

#[test]
fn programs_without_checks_carry_no_trap_record() {
    let compiled = compile("fn main() -> i32 { 7 }");
    assert!(compiled.trap_sites.is_empty());
    let engine = Engine::default();
    let module = Module::new(&engine, &compiled.bytes[..]).unwrap();
    assert!(module.get_export(TRAP_EXPORT).is_none());
}
