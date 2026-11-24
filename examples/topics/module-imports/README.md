# Direct module imports

`use math;` loads `math` and records an explicit direct module edge. Call its
public items with their qualified names, such as `math::add`. A symbol import
such as `use math::add;` and a `[prelude]` alias do not create this edge.

From the repository root, run the source project or build a standalone Wasm
artifact:

```sh
cargo run -p memobits-cli -- run --project examples/topics/module-imports/project.toml
cargo run -p memobits-cli -- build --project examples/topics/module-imports/project.toml --output /tmp/module-imports.wasm
cargo run -p memobits-cli -- run /tmp/module-imports.wasm
```

The public inherent `doubled` and `Draw` extensions live in `math`. The direct
`use math;` edge makes them available to `main`; the receiver explicitly
selects the interface method with `point.draw() of Draw`. The generic
`exercise<T>` wrapper calls both methods, demonstrating that specialization
uses extensions activated in its declaring module. The example runs
identically from source and standalone Wasm. A symbol import or prelude alias
can load `math` names, but does not activate its extensions.

The grouped import in `math` (`use self::main::{Point, Draw};`) imports only
those symbols. `math` can refer to the local extension declaration, while
`main` sees it through its explicit direct module edge. Transitive module loads
do not activate extensions. The current project loader handles modules in one
project; loading another package is outside this feature slice.

## Tests

`test fn` items check this project. `mb test` runs each one in a fresh instance; `mb build` and `mb run` leave them out of the artifact.

```sh
cargo run -p memobits-cli -- test --project examples/topics/module-imports/project.toml
```

The report ends with this summary line (checked by `crates/memobits-cli/tests/examples_documented.rs`):

```text
test result: ok. 1 passed; 0 failed; 0 filtered out
```

## Expected output

Source and standalone Wasm runs print exactly the following on stdout, with empty stderr (this is checked by `crates/memobits-cli/tests/examples_documented.rs`).

```text
Result: Ok(i32(42))
```
