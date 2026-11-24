//! Combined generic array type/const substitution and interface evidence forwarding.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "memobits-generic-const-evidence-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        fixture.write(
            "project.toml",
            "[package]\nname='generic-const-evidence'\nentry='app::main'\n",
        );
        fixture
    }

    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_mb"))
            .current_dir(&self.0)
            .args(args)
            .output()
            .unwrap()
    }

    fn result(&self, source: &str) -> String {
        self.write("src/app.mb", source);
        let source_run = self.run(&["run"]);
        assert!(
            source_run.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&source_run.stderr)
        );

        let build = self.run(&["build"]);
        assert!(
            build.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&build.stderr)
        );
        let wasm_run = self.run(&["run", "target/memobits/app.wasm"]);
        assert!(
            wasm_run.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&wasm_run.stderr)
        );
        assert_eq!(source_run.stdout, wasm_run.stdout, "{source}");
        String::from_utf8(source_run.stdout)
            .unwrap()
            .trim()
            .to_owned()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn generic_array_type_const_and_evidence_forward_through_nested_specializations() {
    let f = Fixture::new();
    f.write(
        "src/common.mb",
        r#"
        pub interface SelectIndex { fn index(borrow self) -> u32; }
        pub type Item { pub value: i32 }

        pub fn inspect<T, const N: u32>(items: array<T, N>) -> array<T, N>
        where T: SelectIndex {
            let index := items[0].borrow().index() of SelectIndex;
            var output := items;
            output[index].value = output[index].value + 10;
            output
        }

        pub fn relay<T, const N: u32>(items: array<T, N>) -> array<T, N>
        where T: SelectIndex {
            inspect(items)
        }
        "#,
    );
    f.write(
        "src/left.mb",
        r#"
        use common;
        extend common::Item of common::SelectIndex {
            fn index(borrow self) -> u32 { 0 }
        }
        pub fn run() -> i32 {
            let pair: array<common::Item, 2> = [
                common::Item { value: 1 }, common::Item { value: 1 }
            ];
            let single: array<common::Item, 1> = [common::Item { value: 29 }];
            let changed_pair := common::relay(pair);
            let changed_single := common::relay(single);
            changed_pair[0].value + changed_pair[1].value + changed_single[0].value
        }
        "#,
    );
    f.write(
        "src/right.mb",
        r#"
        use common;
        extend common::Item of common::SelectIndex {
            fn index(borrow self) -> u32 { 1 }
        }
        pub fn run() -> i32 {
            let pair: array<common::Item, 2> = [
                common::Item { value: 1 }, common::Item { value: 1 }
            ];
            let changed_pair := common::relay(pair);
            changed_pair[0].value + changed_pair[1].value
        }
        "#,
    );
    assert_eq!(
        f.result(
            r#"
            use left;
            use right;
            fn main() -> i32 { left::run() + right::run() }
            "#
        ),
        "Result: i32(63)"
    );
}

#[test]
fn generic_compound_assign_evidence_forwards_to_owned_locals_and_array_places() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            r#"
            use core::ops::RemAssign;
            use core::ops::BitAndAssign;
            use core::ops::BitOrAssign;
            use core::ops::BitXorAssign;
            use core::ops::ShlAssign;

            type RemCell { value: u32 }
            type RemArg { value: u32 }
            type RemHolder { items: array<RemCell, 1> }
            extend RemCell of RemAssign {
                type Rhs = RemArg;
                fn rem_assign(share self, rhs: RemArg) { self.value %= rhs.value; }
            }
            type AndCell { value: u32 }
            type AndArg { value: u32 }
            extend AndCell of BitAndAssign {
                type Rhs = AndArg;
                fn bitand_assign(share self, rhs: AndArg) { self.value &= rhs.value; }
            }
            type OrCell { value: u32 }
            type OrArg { value: u32 }
            extend OrCell of BitOrAssign {
                type Rhs = OrArg;
                fn bitor_assign(share self, rhs: OrArg) { self.value |= rhs.value; }
            }
            type XorCell { value: u32 }
            type XorArg { value: u32 }
            extend XorCell of BitXorAssign {
                type Rhs = XorArg;
                fn bitxor_assign(share self, rhs: XorArg) { self.value ^= rhs.value; }
            }
            type ShlCell { value: u32 }
            type ShlArg { value: u32 }
            extend ShlCell of ShlAssign {
                type Rhs = ShlArg;
                fn shl_assign(share self, rhs: ShlArg) { self.value <<= rhs.value; }
            }

            fn rem_local<T>(target: T, rhs: T::Rhs) -> T where T: RemAssign {
                var value := target;
                value %= rhs;
                value
            }
            fn rem_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: RemAssign {
                values[index] %= rhs;
                values
            }
            fn forward_rem<T>(target: T, rhs: T::Rhs) -> T where T: RemAssign {
                rem_local(target, rhs)
            }
            fn forward_rem_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: RemAssign {
                rem_array(values, index, rhs)
            }
            fn rem_projected<T>(var holder: RemHolder, witness: T, rhs: T::Rhs) -> RemHolder
                where T: RemAssign {
                holder.items[0] %= rhs;
                holder
            }
            fn forward_rem_projected<T>(var holder: RemHolder, witness: T, rhs: T::Rhs) -> RemHolder
                where T: RemAssign {
                rem_projected(holder, witness, rhs)
            }

            fn and_local<T>(target: T, rhs: T::Rhs) -> T where T: BitAndAssign {
                var value := target; value &= rhs; value
            }
            fn and_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: BitAndAssign {
                values[index] &= rhs; values
            }
            fn forward_and<T>(target: T, rhs: T::Rhs) -> T where T: BitAndAssign {
                and_local(target, rhs)
            }
            fn forward_and_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: BitAndAssign {
                and_array(values, index, rhs)
            }

            fn or_local<T>(target: T, rhs: T::Rhs) -> T where T: BitOrAssign {
                var value := target; value |= rhs; value
            }
            fn or_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: BitOrAssign {
                values[index] |= rhs; values
            }
            fn forward_or<T>(target: T, rhs: T::Rhs) -> T where T: BitOrAssign {
                or_local(target, rhs)
            }
            fn forward_or_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: BitOrAssign {
                or_array(values, index, rhs)
            }

            fn xor_local<T>(target: T, rhs: T::Rhs) -> T where T: BitXorAssign {
                var value := target; value ^= rhs; value
            }
            fn xor_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: BitXorAssign {
                values[index] ^= rhs; values
            }
            fn forward_xor<T>(target: T, rhs: T::Rhs) -> T where T: BitXorAssign {
                xor_local(target, rhs)
            }
            fn forward_xor_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: BitXorAssign {
                xor_array(values, index, rhs)
            }

            fn shl_local<T>(target: T, rhs: T::Rhs) -> T where T: ShlAssign {
                var value := target; value <<= rhs; value
            }
            fn shl_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: ShlAssign {
                values[index] <<= rhs; values
            }
            fn forward_shl<T>(target: T, rhs: T::Rhs) -> T where T: ShlAssign {
                shl_local(target, rhs)
            }
            fn forward_shl_array<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N>
                where T: ShlAssign {
                shl_array(values, index, rhs)
            }

            fn main() -> i32 {
                let rem := forward_rem(RemCell { value: 29 }, RemArg { value: 5 });
                let rem_items := forward_rem_array([RemCell { value: 29 }], 0, RemArg { value: 5 });
                let rem_holder := forward_rem_projected(
                    RemHolder { items: [RemCell { value: 29 }] }, RemCell { value: 0 }, RemArg { value: 5 }
                );
                let and := forward_and(AndCell { value: 7 }, AndArg { value: 3 });
                let and_items := forward_and_array([AndCell { value: 7 }], 0, AndArg { value: 3 });
                let or := forward_or(OrCell { value: 8 }, OrArg { value: 3 });
                let or_items := forward_or_array([OrCell { value: 8 }], 0, OrArg { value: 3 });
                let xor := forward_xor(XorCell { value: 12 }, XorArg { value: 5 });
                let xor_items := forward_xor_array([XorCell { value: 12 }], 0, XorArg { value: 5 });
                let shl := forward_shl(ShlCell { value: 3 }, ShlArg { value: 2 });
                let shl_items := forward_shl_array([ShlCell { value: 3 }], 0, ShlArg { value: 2 });
                (rem.value + rem_items[0].value + rem_holder.items[0].value + and.value + and_items[0].value
                    + or.value + or_items[0].value + xor.value + xor_items[0].value
                    + shl.value + shl_items[0].value) as i32
            }
            "#
        ),
        "Result: i32(82)"
    );
}

#[test]
fn generic_array_compounds_forward_add_sub_mul_div_and_shr_evidence() {
    let f = Fixture::new();
    let families = [
        ("add", "AddAssign", "add_assign", "+=", 10, 5),
        ("sub", "SubAssign", "sub_assign", "-=", 10, 3),
        ("mul", "MulAssign", "mul_assign", "*=", 3, 4),
        ("div", "DivAssign", "div_assign", "/=", 81, 3),
        ("shr", "ShrAssign", "shr_assign", ">>=", 48, 2),
    ];
    let mut source = String::new();
    for (_, interface, _, _, _, _) in families {
        source.push_str(&format!("use core::ops::{interface};\n"));
    }
    for (name, interface, method, operator, _, _) in families {
        let type_name = format!("{}Cell", name.to_ascii_uppercase());
        let rhs_name = format!("{}Arg", name.to_ascii_uppercase());
        source.push_str(&format!(
            "type {type_name} {{ value: u32 }} type {rhs_name} {{ value: u32 }}\n"
        ));
        source.push_str(&format!(
            "extend {type_name} of {interface} {{ type Rhs = {rhs_name}; fn {method}(share self, rhs: {rhs_name}) {{ self.value {operator} rhs.value; }} }}\n"
        ));
        source.push_str(&format!(
            "fn apply_{name}<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N> where T: {interface} {{ values[index] {operator} rhs; values }}\n"
        ));
        source.push_str(&format!(
            "fn forward_{name}<T, const N: u32>(var values: array<T, N>, index: u32, rhs: T::Rhs) -> array<T, N> where T: {interface} {{ apply_{name}(values, index, rhs) }}\n"
        ));
    }
    source.push_str("fn main() -> i32 {\n");
    let mut terms = Vec::new();
    for (name, _, _, _, lhs, rhs) in families {
        let type_name = format!("{}Cell", name.to_ascii_uppercase());
        let rhs_name = format!("{}Arg", name.to_ascii_uppercase());
        source.push_str(&format!(
            "let {name} := forward_{name}([{type_name} {{ value: {lhs} }}], 0, {rhs_name} {{ value: {rhs} }});\n"
        ));
        terms.push(format!("{name}[0].value as i32"));
    }
    source.push_str(&format!("{}\n}}\n", terms.join(" + ")));

    assert_eq!(f.result(&source), "Result: i32(73)");
}

#[test]
fn generic_array_add_assign_captures_index_once_mutates_rhs_and_checks_loans() {
    let f = Fixture::new();
    let source = r#"
        use core::ops::AddAssign;
        type Cell { value: u32 }
        extend Cell of AddAssign {
            type Rhs = Cell;
            fn add_assign(share self, rhs: Cell) { self.value += rhs.value; }
        }
        fn update<T, const N: u32>(var values: array<T, N>, var index: u32, var rhs: T::Rhs) -> array<T, N>
            where T: AddAssign {
            values[{ index += 1; index }] += { rhs.value += 1; rhs };
            values
        }
        fn main() -> i32 {
            let result := update(
                [Cell { value: 11 }, Cell { value: 20 }], 0, Cell { value: 2 }
            );
            (result[0].value + result[1].value + 8) as i32
        }
    "#;
    assert_eq!(f.result(source), "Result: i32(42)");

    let disjoint = r#"
        use core::ops::AddAssign;
        type Cell { value: u32 }
        extend Cell of AddAssign {
            type Rhs = Cell;
            fn add_assign(share self, rhs: Cell) { self.value += rhs.value; }
        }
        fn copy_cell(value: borrow Cell) -> Cell { Cell { value: value.value } }
        fn update<T, const N: u32>(var values: array<T, N>) -> array<T, N>
            where T: AddAssign {
            values[0] += copy_cell(values[1].borrow());
            values
        }
        fn main() -> i32 {
            let result := update([Cell { value: 10 }, Cell { value: 5 }]);
            (result[0].value + result[1].value + 5) as i32
        }
    "#;
    // The disjoint source element remains 5; the target becomes 10 + 5,
    // followed by the explicit +5 in main.
    assert_eq!(f.result(disjoint), "Result: i32(25)");

    let overlapping = r#"
        use core::ops::AddAssign;
        type Cell { value: u32 }
        extend Cell of AddAssign {
            type Rhs = Cell;
            fn add_assign(share self, rhs: Cell) { self.value += rhs.value; }
        }
        fn copy_cell(value: borrow Cell) -> Cell { Cell { value: value.value } }
        fn update<T, const N: u32>(var values: array<T, N>) -> array<T, N>
            where T: AddAssign {
            values[0] += copy_cell(values[0].borrow());
            values
        }
        fn main() -> i32 { let result := update([Cell { value: 10 }]); result[0].value as i32 }
    "#;
    f.write("src/app.mb", overlapping);
    let output = f.run(&["run"]);
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("BE005"), "{stderr}");
    assert!(stderr.contains("values[0]"), "{stderr}");
    assert!(stderr.contains("shared"), "{stderr}");
}

#[test]
fn generic_array_compound_rhs_early_return_skips_bounds_check_and_method() {
    let f = Fixture::new();
    let source = r#"
        use core::ops::AddAssign;
        type Cell { value: u32 }
        extend Cell of AddAssign {
            type Rhs = Cell;
            fn add_assign(share self, rhs: Cell) {
                self.value += 1 / rhs.value;
            }
        }
        fn early<T, const N: u32>(
            var values: array<T, N>,
            fallback: array<T, N>,
            other: array<T, N>,
            var index: u32
        ) -> array<T, N> where T: AddAssign {
            values[{ index += 1; index }] += {
                if index == 1 { return fallback; }
                return other;
                Cell { value: 0 }
            };
            values
        }
        fn main() -> i32 {
            let result := early(
                [Cell { value: 42 }], [Cell { value: 41 }], [Cell { value: 40 }], 0
            );
            result[0].value as i32
        }
    "#;
    assert_eq!(f.result(source), "Result: i32(41)");
}

const COMPOUND_FAMILIES: [(&str, &str, &str, &str, u32, u32, u32); 10] = [
    ("Add", "AddAssign", "add_assign", "+=", 12, 3, 15),
    ("Sub", "SubAssign", "sub_assign", "-=", 12, 3, 9),
    ("Mul", "MulAssign", "mul_assign", "*=", 12, 3, 36),
    ("Div", "DivAssign", "div_assign", "/=", 12, 3, 4),
    ("Rem", "RemAssign", "rem_assign", "%=", 12, 3, 0),
    ("And", "BitAndAssign", "bitand_assign", "&=", 12, 3, 0),
    ("Or", "BitOrAssign", "bitor_assign", "|=", 12, 3, 15),
    ("Xor", "BitXorAssign", "bitxor_assign", "^=", 12, 3, 15),
    ("Shl", "ShlAssign", "shl_assign", "<<=", 12, 3, 96),
    ("Shr", "ShrAssign", "shr_assign", ">>=", 12, 3, 1),
];

#[test]
fn generic_compound_families_allow_disjoint_projected_index_loans() {
    let f = Fixture::new();
    let mut source = String::new();
    for (_, interface, _, _, _, _, _) in COMPOUND_FAMILIES {
        source.push_str(&format!("use core::ops::{interface};\n"));
    }
    for (name, interface, method, operator, _, _, _) in COMPOUND_FAMILIES {
        let ty = format!("{name}Cell");
        let holder = format!("{name}Holder");
        source.push_str(&format!(
            "type {ty} {{ value: u32 }}\n\
             type {holder} {{ items: array<{ty}, 2> }}\n\
             extend {ty} of {interface} {{ type Rhs = {ty}; \
             fn {method}(share self, rhs: {ty}) {{ self.value {operator} rhs.value; }} }}\n\
             fn copy_{name}(value: borrow {ty}) -> {ty} {{ {ty} {{ value: value.value }} }}\n\
             fn update_{name}<T>(var holder: {holder}, witness: T) -> {holder} \
             where T: {interface} {{ \
                 holder.items[0] {operator} copy_{name}(holder.items[1].borrow()); \
                 holder \
             }}\n"
        ));
    }
    source.push_str("fn main() -> i32 {\n");
    let mut terms = Vec::new();
    for (name, _, _, _, lhs, rhs, _) in COMPOUND_FAMILIES {
        let ty = format!("{name}Cell");
        let holder = format!("{name}Holder");
        source.push_str(&format!(
            "let result_{name} := update_{name}({holder} {{ items: \
             [{ty} {{ value: {lhs} }}, {ty} {{ value: {rhs} }}] }}, \
             {ty} {{ value: 0 }});\n"
        ));
        terms.push(format!("result_{name}.items[0].value as i32"));
    }
    source.push_str(&format!("{}\n}}\n", terms.join(" + ")));
    let expected_total = COMPOUND_FAMILIES.iter().map(|family| family.6).sum::<u32>();
    assert_eq!(f.result(&source), format!("Result: i32({expected_total})"));
}

#[test]
fn generic_compound_families_order_index_before_rhs_and_skip_bounds_and_method_on_return() {
    let f = Fixture::new();
    let mut source = String::new();
    for (_, interface, _, _, _, _, _) in COMPOUND_FAMILIES {
        source.push_str(&format!("use core::ops::{interface};\n"));
    }
    for (name, interface, method, operator, _, _, _) in COMPOUND_FAMILIES {
        let ty = format!("{name}Cell");
        source.push_str(&format!(
            "type {ty} {{ value: u32 }}\n\
             extend {ty} of {interface} {{ type Rhs = {ty}; \
             fn {method}(share self, rhs: {ty}) {{ self.value += 1 / rhs.value; }} }}\n\
             fn early_{name}<T, const N: u32>(var values: array<T, N>, \
                 fallback: array<T, N>, alternative: array<T, N>, \
                 var index: u32) -> array<T, N> \
             where T: {interface} {{ \
                 values[{{ index += 1; index }}] {operator} {{ \
                     if index == 1 {{ return fallback; }} \
                     return alternative; \
                     {ty} {{ value: 0 }} \
                 }}; \
                 values \
             }}\n"
        ));
    }
    source.push_str("fn main() -> i32 {\n");
    let mut terms = Vec::new();
    for (name, _, _, _, _, _, _) in COMPOUND_FAMILIES {
        let ty = format!("{name}Cell");
        source.push_str(&format!(
            "let values_{name} := [{ty} {{ value: 42 }}];\n\
             let fallback_{name} := [{ty} {{ value: 41 }}];\n\
             let alternative_{name} := [{ty} {{ value: 40 }}];\n\
             let result_{name} := early_{name}(values_{name}, \
                 fallback_{name}, alternative_{name}, 0);\n"
        ));
        terms.push(format!("result_{name}[0].value as i32"));
    }
    source.push_str(&format!("{}\n}}\n", terms.join(" + ")));
    assert_eq!(f.result(&source), "Result: i32(410)");
}

#[test]
fn overloaded_sub_mul_div_rem_evaluate_operands_left_to_right_in_source_and_wasm() {
    let f = Fixture::new();
    let families = [
        ("Sub", "Sub", "sub", "-", 16),
        ("Mul", "Mul", "mul", "*", 80),
        ("Div", "Div", "div", "/", 5),
        ("Rem", "Rem", "rem", "%", 0),
    ];
    let mut source = String::new();
    for (_, interface, _, _, _) in families {
        source.push_str(&format!("use core::ops::{interface};\n"));
    }
    for (name, interface, method, operator, _) in families {
        source.push_str(&format!(
            "type {name}Left {{ value: i32 }} type {name}Right {{ value: i32 }} \
             type {name}Output {{ value: i32 }}\n\
             extend {name}Left of {interface} {{ type Rhs = {name}Right; \
             type Output = {name}Output; fn {method}(self, rhs: {name}Right) \
             -> {name}Output {{ {name}Output {{ value: self.value {operator} rhs.value }} }} }}\n"
        ));
    }
    source.push_str("fn main() -> i32 { var order: u32 = 0; var total: i32 = 0;\n");
    for (name, _, _, operator, _) in families {
        source.push_str(&format!(
            "order = 0; let result_{name} := \
             {{ order = order * 10 + 1; {name}Left {{ value: 20 }} }} {operator} \
             {{ if order % 10 != 1 {{ return 0; }} order = order * 10 + 2; \
                {name}Right {{ value: 4 }} }}; \
             if order % 100 != 12 {{ return 0; }} total += result_{name}.value;\n"
        ));
    }
    source.push_str("total\n}\n");
    let expected_total = families.iter().map(|family| family.4).sum::<i32>();
    assert_eq!(f.result(&source), format!("Result: i32({expected_total})"));
}

#[test]
fn overloaded_add_shift_and_bitand_equality_keep_operator_precedence() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            r#"
            use core::ops::Add;
            use core::ops::Shl;
            use core::ops::BitAnd;
            use core::ops::PartialEq;
            type X { value: u32 }
            type Y { value: u32 }
            type Sum { value: u32 }
            type Count { value: u32 }
            type Shifted { value: u32 }
            extend X of Add {
                type Rhs = Y; type Output = Sum;
                fn add(self, rhs: Y) -> Sum { Sum { value: self.value + rhs.value } }
            }
            extend Sum of Shl {
                type Rhs = Count; type Output = Shifted;
                fn shl(self, rhs: Count) -> Shifted { Shifted { value: self.value << rhs.value } }
            }
            type A { value: u32 }
            type B { value: u32 }
            type Masked { value: u32 }
            type Expected { value: u32 }
            extend A of BitAnd {
                type Rhs = B; type Output = Masked;
                fn bitand(self, rhs: B) -> Masked { Masked { value: self.value & rhs.value } }
            }
            extend Masked of PartialEq {
                type Rhs = Expected;
                fn eq(borrow self, rhs: Expected) -> bool { self.value == rhs.value }
            }
            fn main() -> i32 {
                let shifted := X { value: 3 } + Y { value: 2 } << Count { value: 2 };
                let masked_equal := A { value: 6 } & B { value: 3 } == Expected { value: 2 };
                if shifted.value == 20 && masked_equal { 42 } else { 0 }
            }
            "#
        ),
        "Result: i32(42)"
    );
}

#[test]
fn short_circuit_skips_rhs_effects_in_source_and_wasm() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            r#"
            fn touch(calls: share u32) -> bool { calls += 1; true }
            fn main() -> i32 {
                var calls: u32 = 0;
                if false && touch(calls.share()) { return 0; }
                if true || touch(calls.share()) {
                    if calls == 0 { 42 } else { 0 }
                } else { 0 }
            }
            "#
        ),
        "Result: i32(42)"
    );
}

#[test]
fn primitive_signed_shifts_are_rejected() {
    let f = Fixture::new();
    for shift in ["<<", ">>"] {
        f.write(
            "src/app.mb",
            &format!(
                "fn main() -> i32 {{ let value: i32 = 1; let count: u32 = 1; value {shift} count }}"
            ),
        );
        let output = f.run(&["build"]);
        assert!(!output.status.success(), "{shift}: {output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("TE002"), "{shift}: {stderr}");
        assert!(
            stderr.contains("expected u32, found i32"),
            "{shift}: {stderr}"
        );
    }
}

#[test]
fn assignment_and_short_circuit_operators_resist_user_overloads() {
    let f = Fixture::new();
    assert_eq!(
        f.result(
            r#"
            use core::ops::AddAssign;
            type Cell { value: u32 }
            extend Cell of AddAssign {
                type Rhs = Cell;
                fn add_assign(share self, rhs: Cell) { self.value += 1 / rhs.value; }
            }
            fn main() -> i32 {
                var target := Cell { value: 7 };
                target = Cell { value: 42 };
                target.value as i32
            }
            "#
        ),
        "Result: i32(42)"
    );

    for (operator, interface, method) in [("&&", "BitAnd", "bitand"), ("||", "BitOr", "bitor")] {
        f.write(
            "src/app.mb",
            &format!(
                "use core::ops::{interface}; \
                 type Left {{}} type Right {{}} type Output {{ value: bool }} \
                 extend Left of {interface} {{ type Rhs = Right; type Output = Output; \
                     fn {method}(self, rhs: Right) -> Output {{ Output {{ value: true }} }} }} \
                 fn main() -> bool {{ Left {{}} {operator} Right {{}} }}"
            ),
        );
        let output = f.run(&["build"]);
        assert!(!output.status.success(), "{operator}: {output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("TE002"), "{operator}: {stderr}");
        assert!(stderr.contains("expected bool"), "{operator}: {stderr}");
        assert!(
            !stderr.contains(&format!("no visible {interface} implementation")),
            "{operator} selected an overload instead of enforcing builtin bool operands: {stderr}"
        );
    }
}
