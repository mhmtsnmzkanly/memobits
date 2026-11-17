# memobits-resolve

Loads reachable local modules from an application entry or library export roots.
It checks imports and preludes, module visibility, lexical names and shadowing,
annotation names, duplicate declarations/members, and enum variant paths.
Diagnostics retain source spans for the CLI renderer. Application entries must
refer to functions; library roots must be public.

Reachability is currently module-level. Unrelated modules are inventoried by the
project crate but their contents are not parsed. All declarations inside a
reachable module are checked, including unused functions.

Enum variant paths in expressions and in `match` patterns are checked through local aliases
(`type S = Shape;`, chains included, NE004 for an unknown variant); a path through an alias of an
imported enum is expanded and checked by the module loader (ME006/ME007). Pattern bindings are
scoped to their arm.

This is not a type or ownership checker. Dependency loading, reexports and complete
public-signature visibility
closure are not implemented. Direct exposure of private local types in public
functions, aliases, fields, and enum payloads is rejected (ME010). Imported annotation targets must be types, but
complete value/type namespace validation remains for semantic analysis.

```sh
cargo test -p memobits-resolve
```
