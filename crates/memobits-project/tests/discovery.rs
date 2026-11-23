use memobits_project::{discover_modules, Manifest, Project};
use std::{
    fs,
    path::Path,
    sync::atomic::{AtomicU64, Ordering},
};
static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(std::path::PathBuf);
impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "memobits-project-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        Self(root)
    }
    fn write(&self, path: &str, text: &str) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn override_resolves_source_from_manifest_and_inventories_without_parsing() {
    let f = Fixture::new();
    f.write("nested/custom.toml", "[package]\nname='demo'\nentry='main::run'\nsrc='../code'\n[export]\nPublic='nested::z::value'\n[prelude]\nValue='nested::z::value'\n");
    f.write(
        "code/nested/z.mb",
        "invalid syntax is intentionally not parsed",
    );
    f.write("code/main.mb", "");
    f.write("code/README.txt", "ignored");
    let p = Project::load(&f.0, Some(Path::new("nested/custom.toml"))).unwrap();
    assert_eq!(
        p.modules
            .iter()
            .map(|m| m.name.as_str())
            .collect::<Vec<_>>(),
        ["main", "nested::z"]
    );
    assert_eq!(p.source_root, fs::canonicalize(f.0.join("code")).unwrap());
    assert!(p.modules.iter().all(|m| m.path.is_absolute()));
    assert_eq!(p.manifest.export["Public"], "nested::z::value");
}
#[test]
fn default_manifest_and_source_root() {
    let f = Fixture::new();
    f.write(
        "project.toml",
        "[package]\nname='library'\n[export]\nrun='lib::run'",
    );
    f.write("src/lib.mb", "");
    let p = Project::load(&f.0, None).unwrap();
    assert_eq!(p.modules[0].name, "lib");
}
#[test]
fn missing_root_and_invalid_module_paths_are_errors() {
    let f = Fixture::new();
    assert!(discover_modules(f.0.join("absent")).is_err());
    f.write("bad-name.mb", "");
    assert!(discover_modules(&f.0)
        .unwrap_err()
        .to_string()
        .contains("invalid module path"));
}

#[test]
fn manifest_host_profile_is_parsed_and_validated() {
    let valid =
        Manifest::parse("[package]\nname='hosted'\nentry='main::run'\n[host]\nprofile='cli'\n")
            .unwrap();
    assert_eq!(valid.host.unwrap().profile.as_deref(), Some("cli"));

    let missing =
        Manifest::parse("[package]\nname='hosted'\nentry='main::run'\n[host]\n").unwrap_err();
    assert!(missing.to_string().contains("host.profile is required"));

    let unknown =
        Manifest::parse("[package]\nname='hosted'\nentry='main::run'\n[host]\nprofile='browser'\n")
            .unwrap_err();
    assert!(unknown.to_string().contains("unknown host profile"));

    let capability = Manifest::parse(
        "[package]\nname='hosted'\nentry='main::run'\n[host]\nprofile='cli'\ncapability='clock'\n",
    )
    .unwrap_err();
    assert!(capability.to_string().contains("invalid project manifest"));

    let typed_import = Manifest::parse(
        "[package]\nname='hosted'\nentry='main::run'\n[host]\nprofile='cli'\n[[host.imports]]\nmodule='memobits:console'\nname='write_i32'\nparams=['i32']\nresult='unit'\n",
    )
    .unwrap();
    assert_eq!(typed_import.host.unwrap().imports.len(), 1);

    let wrong_signature = Manifest::parse(
        "[package]\nname='hosted'\nentry='main::run'\n[host]\nprofile='cli'\n[[host.imports]]\nmodule='memobits:console'\nname='write_i32'\nparams=['i64']\nresult='unit'\n",
    )
    .unwrap_err();
    assert!(wrong_signature
        .to_string()
        .contains("unsupported host import"));
}

#[cfg(unix)]
#[test]
fn rejects_symlink_cycles() {
    let f = Fixture::new();
    std::os::unix::fs::symlink(&f.0, f.0.join("cycle")).unwrap();
    assert!(discover_modules(&f.0)
        .unwrap_err()
        .to_string()
        .contains("symlinks"));
}
