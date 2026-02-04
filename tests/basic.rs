use memobits::{Interpreter, NativeRegistry, SyntaxAnalyzer, TypeChecker};

fn parse(src: &str) -> memobits::Program {
    let mut sa = SyntaxAnalyzer::new(src);
    sa.analyz().expect("parse failed")
}

#[test]
fn typecheck_success() {
    let src = r#"
        let x = 1;
        let y = x + 2;
        y;
    "#;
    let program = parse(src);
    let mut tc = TypeChecker::new();
    assert!(tc.check_program(&program).is_ok());
}

#[test]
fn typecheck_error() {
    let src = r#"
        let x: Int = "no";
    "#;
    let program = parse(src);
    let mut tc = TypeChecker::new();
    assert!(tc.check_program(&program).is_err());
}

#[test]
fn run_map_index_and_assign() {
    let src = r#"
        var m = {"a" => 1};
        m["b"] = 2;
        let v = m["b"];
        native::print(v);
    "#;
    let program = parse(src);
    let mut tc = TypeChecker::new();
    assert!(tc.check_program(&program).is_ok());
    let mut interp = Interpreter::new(NativeRegistry::new());
    interp.set_source(src);
    assert!(interp.run(&program).is_ok());
}

#[test]
fn string_concat_and_eq() {
    let src = r#"
        let s = "a" + "b";
        let ok = s == "ab";
        native::print(ok);
    "#;
    let program = parse(src);
    let mut tc = TypeChecker::new();
    assert!(tc.check_program(&program).is_ok());
    let mut interp = Interpreter::new(NativeRegistry::new());
    interp.set_source(src);
    assert!(interp.run(&program).is_ok());
}
