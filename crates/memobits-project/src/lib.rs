//! Project manifests and deterministic source-module discovery.
//!
//! Discovery inventories paths only; it does not read or compile source files.
use serde::Deserialize;
use std::{
    collections::BTreeMap,
    fmt, fs,
    path::{Path, PathBuf},
};

pub const DEFAULT_MANIFEST: &str = "project.toml";

/// Default `[build].stack_size`: 1 MiB.
pub const DEFAULT_STACK_SIZE: u32 = 1024 * 1024;
/// Smallest accepted `[build].stack_size`: 4 KiB.
pub const MIN_STACK_SIZE: u32 = 4 * 1024;
/// Largest accepted `[build].stack_size`: 256 MiB. Together with the reserved
/// low addresses this stays far below the 4 GiB limit of a 32-bit memory and
/// leaves room for static data and the heap.
pub const MAX_STACK_SIZE: u32 = 256 * 1024 * 1024;
/// `[build].stack_size` must be a multiple of this many bytes.
pub const STACK_SIZE_ALIGNMENT: u32 = 16;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub package: Package,
    #[serde(default)]
    pub export: BTreeMap<String, String>,
    #[serde(default)]
    pub prelude: BTreeMap<String, String>,
    #[serde(default)]
    pub dependencies: BTreeMap<String, Dependency>,
    #[serde(default)]
    pub build: Build,
    #[serde(default)]
    pub host: Option<Host>,
}

/// Optional `[host]` table. The CLI profile currently admits one typed console
/// import; every other setting remains rejected by `deny_unknown_fields`.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Host {
    pub profile: Option<String>,
    #[serde(default)]
    pub imports: Vec<HostImport>,
}

/// One typed host function import enabled by the selected profile.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct HostImport {
    pub module: String,
    pub name: String,
    pub params: Vec<HostValueType>,
    pub result: HostValueType,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum HostValueType {
    I32,
    I64,
    F32,
    F64,
    Unit,
}

/// Optional `[build]` table.
#[derive(Debug, Clone, Default, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Build {
    /// Size of the stack in bytes. Kept signed so a negative value reaches
    /// validation with a clear message; see [`Manifest::stack_size`].
    pub stack_size: Option<i64>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Package {
    pub name: String,
    pub version: Option<String>,
    pub entry: Option<String>,
    #[serde(default = "default_src")]
    pub src: PathBuf,
}
fn default_src() -> PathBuf {
    PathBuf::from("./src")
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Dependency {
    #[serde(rename = "type")]
    pub kind: DependencyKind,
    pub src: String,
    /// An empty list selects every public export; omission is an error.
    pub import: Vec<String>,
    #[serde(default)]
    pub external: bool,
}

/// Source dependencies identify manifest-bearing packages; binary dependencies
/// identify compiled artifacts. Locations remain opaque until dependency loading.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum DependencyKind {
    Source,
    Binary,
}

#[derive(Debug)]
pub enum Error {
    Io {
        path: PathBuf,
        source: std::io::Error,
    },
    Toml(toml::de::Error),
    Invalid(String),
    /// A `[build]` setting is out of range or malformed.
    Build(String),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Toml(source) => write!(f, "invalid project manifest: {source}"),
            Self::Invalid(message) | Self::Build(message) => f.write_str(message),
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Toml(source) => Some(source),
            _ => None,
        }
    }
}
fn io(path: &Path, source: std::io::Error) -> Error {
    Error::Io {
        path: path.to_owned(),
        source,
    }
}
fn invalid(message: impl Into<String>) -> Error {
    Error::Invalid(message.into())
}
fn identifier(s: &str) -> bool {
    let mut chars = s.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}
fn definition(s: &str) -> bool {
    !s.is_empty() && s.split("::").all(identifier)
}
impl Manifest {
    pub fn parse(text: &str) -> Result<Self, Error> {
        let manifest: Self = toml::from_str(text).map_err(Error::Toml)?;
        manifest.validate()?;
        Ok(manifest)
    }
    /// The validated stack size in bytes, or the 1 MiB default.
    pub fn stack_size(&self) -> u32 {
        self.build
            .stack_size
            .and_then(|size| u32::try_from(size).ok())
            .unwrap_or(DEFAULT_STACK_SIZE)
    }
    pub fn validate(&self) -> Result<(), Error> {
        if let Some(size) = self.build.stack_size {
            let range = format!("{MIN_STACK_SIZE} to {MAX_STACK_SIZE}");
            if size <= 0 {
                return Err(Error::Build(format!(
                    "build.stack_size must be a positive number of bytes ({range}), got {size}"
                )));
            }
            if size < i64::from(MIN_STACK_SIZE) || size > i64::from(MAX_STACK_SIZE) {
                return Err(Error::Build(format!(
                    "build.stack_size {size} is outside the supported range of {range} bytes"
                )));
            }
            if size % i64::from(STACK_SIZE_ALIGNMENT) != 0 {
                return Err(Error::Build(format!(
                    "build.stack_size {size} must be a multiple of {STACK_SIZE_ALIGNMENT} bytes"
                )));
            }
        }
        if let Some(host) = &self.host {
            match host.profile.as_deref() {
                None => return Err(invalid("host.profile is required; supported profile: cli")),
                Some("cli") => {}
                Some(profile) => {
                    return Err(invalid(format!(
                        "unknown host profile {profile:?}; supported profile: cli"
                    )))
                }
            }
            let mut seen = std::collections::BTreeSet::new();
            for import in &host.imports {
                let key = (&import.module, &import.name);
                if !seen.insert(key) {
                    return Err(invalid(format!(
                        "duplicate host import '{}.{}'",
                        import.module, import.name
                    )));
                }
                if import.module != "memobits:console"
                    || import.name != "write_i32"
                    || import.params.as_slice() != &[HostValueType::I32]
                    || import.result != HostValueType::Unit
                {
                    return Err(invalid(format!(
                        "unsupported host import '{}.{}'; supported signature is memobits:console.write_i32(i32) -> unit",
                        import.module, import.name
                    )));
                }
            }
        }
        if self.package.name.trim().is_empty() {
            return Err(invalid("package.name must not be empty"));
        }
        if self
            .package
            .version
            .as_ref()
            .is_some_and(|v| v.trim().is_empty())
        {
            return Err(invalid("package.version must not be empty"));
        }
        if self.package.src.as_os_str().is_empty() {
            return Err(invalid("package.src must not be empty"));
        }
        if self.package.entry.as_ref().is_some_and(|v| !definition(v)) {
            return Err(invalid("package.entry must be a definition path"));
        }
        if self.package.entry.is_none() && self.export.is_empty() {
            return Err(invalid("package requires an entry or at least one export"));
        }
        for (table, mappings) in [("export", &self.export), ("prelude", &self.prelude)] {
            for (alias, target) in mappings {
                if !identifier(alias) || !definition(target) {
                    return Err(invalid(format!(
                        "invalid {table} mapping {alias:?} -> {target:?}"
                    )));
                }
            }
        }
        for (name, dependency) in &self.dependencies {
            if !identifier(name) {
                return Err(invalid(format!("invalid dependency name {name:?}")));
            }
            if dependency.src.trim().is_empty() {
                return Err(invalid(format!(
                    "dependency {name:?} requires nonempty type and src"
                )));
            }
            let mut selected = std::collections::BTreeSet::new();
            for name in &dependency.import {
                if !definition(name) || !selected.insert(name) {
                    return Err(invalid("dependency import paths must be valid and unique"));
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    /// Source-root-relative module name, for example `math::vector`.
    pub name: String,
    /// Canonical source path.
    pub path: PathBuf,
}
#[derive(Debug)]
pub struct Project {
    pub manifest_path: PathBuf,
    pub source_root: PathBuf,
    pub manifest: Manifest,
    pub modules: Vec<Module>,
}
impl Project {
    /// Resolve a relative override against `directory`; source paths are relative
    /// to the selected manifest's parent, independently of the process directory.
    pub fn load(
        directory: impl AsRef<Path>,
        manifest_override: Option<&Path>,
    ) -> Result<Self, Error> {
        let selected = directory
            .as_ref()
            .join(manifest_override.unwrap_or(Path::new(DEFAULT_MANIFEST)));
        let manifest_path = fs::canonicalize(&selected).map_err(|e| io(&selected, e))?;
        let text = fs::read_to_string(&manifest_path).map_err(|e| io(&manifest_path, e))?;
        let manifest = Manifest::parse(&text)?;
        let source = manifest_path
            .parent()
            .expect("canonical manifest has a parent")
            .join(&manifest.package.src);
        let source_root = fs::canonicalize(&source).map_err(|e| io(&source, e))?;
        let modules = discover_modules(&source_root)?;
        Ok(Self {
            manifest_path,
            source_root,
            manifest,
            modules,
        })
    }
}

/// Inventory `.mb` files recursively. Every path component must be an ASCII
/// identifier. Symlinks are rejected to avoid loops, aliases and root escapes.
/// `a.mb` and `a/b.mb` map to `a` and `a::b`; there is no special `mod.mb` rule.
pub fn discover_modules(root: impl AsRef<Path>) -> Result<Vec<Module>, Error> {
    let supplied = root.as_ref();
    let root = fs::canonicalize(supplied).map_err(|e| io(supplied, e))?;
    if !root.is_dir() {
        return Err(invalid(format!(
            "source root is not a directory: {}",
            root.display()
        )));
    }
    let mut modules = Vec::new();
    visit(&root, &root, &mut modules)?;
    modules.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(modules)
}
fn visit(root: &Path, directory: &Path, modules: &mut Vec<Module>) -> Result<(), Error> {
    let mut entries = fs::read_dir(directory)
        .map_err(|e| io(directory, e))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| io(directory, e))?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        let kind = entry.file_type().map_err(|e| io(&path, e))?;
        if kind.is_symlink() {
            return Err(invalid(format!(
                "source symlinks are unsupported: {}",
                path.display()
            )));
        }
        if kind.is_dir() {
            visit(root, &path, modules)?;
        } else if kind.is_file() && path.extension().is_some_and(|e| e == "mb") {
            let relative = path
                .strip_prefix(root)
                .expect("visited path is within source root")
                .with_extension("");
            let parts = relative
                .iter()
                .map(|p| p.to_str().filter(|s| identifier(s)))
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| invalid(format!("invalid module path: {}", path.display())))?;
            modules.push(Module {
                name: parts.join("::"),
                path,
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn mandatory_dependency_fields_and_defaults() {
        let text = "[package]\nname='demo'\nentry='main::run'\n[dependencies.math]\ntype='binary'\nsrc='math.wasm'\nimport=[]\n";
        let m = Manifest::parse(text).unwrap();
        assert_eq!(m.package.src, Path::new("./src"));
        assert!(!m.dependencies["math"].external);
        for field in ["type='binary'\n", "src='math.wasm'\n", "import=[]\n"] {
            assert!(Manifest::parse(&text.replace(field, "")).is_err());
        }
    }
    #[test]
    fn dependency_imports_accept_qualified_names() {
        let text = "[package]\nname='demo'\nentry='main::run'\n[dependencies.math]\ntype='binary'\nsrc='math.wasm'\nimport=['cmp::Compare']\n";
        assert!(Manifest::parse(text).is_ok());
        assert!(Manifest::parse(&text.replace("cmp::Compare", "cmp::")).is_err());
        assert!(Manifest::parse(&text.replace("binary", "unknown")).is_err());
    }
    #[test]
    fn validates_roots_aliases_and_typos() {
        assert!(Manifest::parse("[package]\nname='demo'").is_err());
        assert!(Manifest::parse("[package]\nname='demo'\n[export]\nVector='math::Vec'").is_ok());
        assert!(Manifest::parse("[package]\nname='demo'\nentry='main::' ").is_err());
        assert!(Manifest::parse("[package]\nname='demo'\nentry='main::run'\nscr='src'").is_err());
    }
    #[test]
    fn build_stack_size_defaults_and_validates() {
        let base = "[package]\nname='demo'\nentry='main::run'\n";
        assert_eq!(Manifest::parse(base).unwrap().stack_size(), 1_048_576);
        let with = |v: &str| Manifest::parse(&format!("{base}[build]\nstack_size={v}\n"));
        assert_eq!(with("4194304").unwrap().stack_size(), 4_194_304);
        assert_eq!(with("4096").unwrap().stack_size(), 4096);
        assert_eq!(with("268435456").unwrap().stack_size(), MAX_STACK_SIZE);
        for bad in ["0", "-16", "4080", "4100", "268435472", "99999999999"] {
            assert!(matches!(with(bad), Err(Error::Build(_))), "{bad}");
        }
        assert!(matches!(with("'big'"), Err(Error::Toml(_))));
        assert!(matches!(with("1.5"), Err(Error::Toml(_))));
        assert!(Manifest::parse(&format!("{base}[build]\nstack=1\n")).is_err());
        assert_eq!(
            Manifest::parse(&format!("{base}[build]\n"))
                .unwrap()
                .stack_size(),
            DEFAULT_STACK_SIZE
        );
    }
}
