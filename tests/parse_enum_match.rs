use memobits::SyntaxAnalyzer;

#[test]
fn parse_enum_match_should_work() {
    let src = r#"
        enum MaybeInt { Nothing, Just(Int) }
        let maybe = MaybeInt::Just(7);
        match maybe {
            MaybeInt::Nothing => native::print("no"),
            MaybeInt::Just(x) => native::print(`yes {x}`)
        }
    "#;
    let mut sa = SyntaxAnalyzer::new(src);
    let res = sa.analyz();
    assert!(res.is_ok(), "{:?}", res.err());
}
