# Runnable language guide

The guide walks through the executable language with small checked examples,
split into topic modules under [`src/`](src/): `numbers`, `text`, `tuples`,
`aggregates`, `ownership`, `collections`, `enums_outcomes`, `generics` and
`operators`. [`src/main.mb`](src/main.mb) holds `main`, which runs every check,
returns `Ok(42)` when all pass, and returns a distinct `Err` code for each failed
check. It is the reference for
current syntax, together with the accepted rules in
[decisions](../../docs/design/decisions.md).

From the repository root, run the source and build the standalone artifact in
a temporary directory:

```sh
cargo run -p memobits-cli -- run --project examples/guide/project.toml
artifact_dir=$(mktemp -d)
cargo run -p memobits-cli -- build --project examples/guide/project.toml --output "$artifact_dir/guide.wasm"
cargo run -p memobits-cli -- run "$artifact_dir/guide.wasm"
```

## Check codes

`main` runs every topic check in order. A failing check returns
`Err(Error { code })`; the hundreds digit names the module that defines the
check (1xx `numbers`, 2xx `text`, 3xx `tuples`, 4xx `aggregates`,
5xx `ownership`, 6xx `collections`, 7xx `enums_outcomes`, 8xx `generics`,
9xx `operators`). New checks take the next free code in their module's range.

| Code | Module | Check |
| --- | --- | --- |
| 101 | `numbers` | `numbers` |
| 102 | `numbers` | `widenings` |
| 103 | `numbers` | `numeric_casts` |
| 104 | `numbers` | `wrapping_arithmetic` |
| 105 | `numbers` | `bit_operations` |
| 201 | `text` | `character_literals` |
| 202 | `text` | `fixed_text` |
| 203 | `text` | `text_boundaries` |
| 204 | `text` | `text_bytes` |
| 205 | `text` | `text_scalars` |
| 206 | `text` | `walk_text` |
| 207 | `text` | `text_loop` |
| 208 | `text` | `text_concat` |
| 209 | `text` | `static_text_result, heap_text_result` |
| 301 | `tuples` | `tuple_values` |
| 401 | `aggregates` | `anonymous_shapes` |
| 402 | `aggregates` | `shared_string_field_replacement` |
| 501 | `ownership` | `explicit_drop` |
| 502 | `ownership` | `local_string_fields, local_heap_string_fields` |
| 503 | `ownership` | `borrow_string_struct` |
| 504 | `ownership` | `owned_string_struct_argument` |
| 505 | `ownership` | `temporary_string_fields` |
| 506 | `ownership` | `replace_local_string_field` |
| 601 | `collections` | `stations` |
| 602 | `collections` | `fixed_bytes` |
| 603 | `collections` | `primitive_lists` |
| 604 | `collections` | `fixed_iteration` |
| 605 | `collections` | `list_iteration` |
| 701 | `enums_outcomes` | `trailing_enum_extension` |
| 702 | `enums_outcomes` | `optional_sugar` |
| 703 | `enums_outcomes` | `enums` |
| 704 | `enums_outcomes` | `optional_borrow` |
| 705 | `enums_outcomes` | `outcomes` |
| 706 | `enums_outcomes` | `nested_result_storage` |
| 801 | `generics` | `generic_structs` |
| 802 | `generics` | `nested_generic_methods` |
| 803 | `generics` | `generic_functions` |
| 804 | `generics` | `generic_array_forwarding` |
| 805 | `generics` | `generic_interface_forwarding` |
| 901 | `operators` | `user_defined_add` |
| 902 | `operators` | `user_defined_sub` |
| 903 | `operators` | `user_defined_mul` |
| 904 | `operators` | `user_defined_div` |
| 905 | `operators` | `user_defined_rem` |
| 906 | `operators` | `user_defined_bitand` |
| 907 | `operators` | `user_defined_bitor` |
| 908 | `operators` | `user_defined_bitxor` |
| 909 | `operators` | `user_defined_negation` |
| 910 | `operators` | `user_defined_equality` |
| 911 | `operators` | `user_defined_ordering` |
| 912 | `operators` | `user_defined_add_assign` |
| 913 | `operators` | `user_defined_sub_assign` |
| 914 | `operators` | `user_defined_mul_assign` |
| 915 | `operators` | `user_defined_div_assign` |
| 916 | `operators` | `user_defined_rem_assign` |
| 917 | `operators` | `user_defined_bitand_assign` |
| 918 | `operators` | `user_defined_bitor_assign` |
| 919 | `operators` | `user_defined_bitxor_assign` |
| 920 | `operators` | `user_defined_shl` |
| 921 | `operators` | `user_defined_shl_assign` |
| 922 | `operators` | `user_defined_shr_assign` |
| 923 | `operators` | `generic_compound_assignments` |
| 924 | `operators` | `user_defined_shr` |

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(42))
```
