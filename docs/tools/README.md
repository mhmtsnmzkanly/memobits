# Development tools

Helper scripts used while developing the compiler. They are not part of the
`mb` tool and are not run by the test suite.

| Script | Purpose |
| --- | --- |
| `equivalence.sh` | Captures the output of `mb check/run/test/build`, standalone Wasm runs and `syntax/analyze/ownership` for every example project, plus Wasm hashes. Run it with two compiler builds (`MBBIN=<other mb>`) and `diff -r -x build.log` the outputs to prove a change is behavior-preserving. |
| `fmt-snapshot.sh` | Records check/test/run output of every example and analysis input; used to show `mb fmt` changed no behavior. |
| `migrate_types.py` | Token-aware rewriter used for the built-in type spelling migration (`Bool`→`bool`, `Option<T>`→`T?`, `Result<T, E>`→`T ! E`, …), including Memobits sources embedded in Rust tests. `--check` prints a diff. |
| `migrate_alloc_list.py` | Adds `use alloc::List;` to sources that use `List` (alloc layer migration). |

Run the snapshot tools from the repository root. For example:

```sh
cargo build -j1 -p memobits-cli
docs/tools/fmt-snapshot.sh /tmp/memobits-fmt-snapshot
MBBIN="$PWD/target/debug/mb" docs/tools/equivalence.sh /tmp/memobits-equivalence
```

`equivalence.sh` removes and recreates `target/equivalence-work` during its
run; do not store files there. It records individual command exit statuses in
its output, so inspect those results as well as the directory diff.

The old spellings these migrations target are now compile errors, so the
migration scripts are kept as references for future spelling changes.
