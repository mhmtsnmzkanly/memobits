# memobits-project

Parses project manifests and inventories module candidates without reading,
executing, or compiling source files. The default manifest is `project.toml`;
`Project::load` accepts another manifest path (relative to its directory argument,
or absolute). Relative source paths resolve against the selected manifest.

```toml
[package]
name = "example"
version = "0.1.0" # optional metadata, not yet semver-validated
entry = "main::run" # optional for libraries with exports
src = "./src" # optional; default shown

[export]
PublicName = "geometry::internal_name"

[prelude]
Point = "geometry::Point"

[dependencies.geometry]
type = "binary" # source or binary
src = "./geometry.wasm"
import = [] # mandatory; empty selects all public exports
external = false # optional; default shown
```

An entry or at least one export is required. Unknown fields are rejected.
`[package].src` is the initial schema placement of the accepted source-root
setting. Export and prelude keys are ASCII identifiers, with `::`-separated
identifier targets. Dependency `type`, `src`, and `import` are mandatory.
Source locations are retained as strings; the crate does not access dependencies.

`src/math/vector.mb` maps to `math::vector`; `mod.mb` has no special meaning.
Candidates sort by module name. Paths are canonical absolute paths; symlink
entries inside the source tree are rejected to prevent loops and aliases.
Non-`.mb` files are ignored. Directories may contain non-module assets; only
paths leading to a `.mb` file must have identifier components.

This initial layer does not resolve definitions, prove exports public, select
reachable modules, fetch dependencies, validate source-package manifests, detect
package dependency cycles, or build artifacts. Missing definition targets are
therefore left for name resolution. Discovery includes unreachable candidates,
without implying that every candidate will be compiled.
