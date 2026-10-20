#![cfg(not(windows))]
// set by `build.rs` if we are running rust stable
#![cfg(RUN_UI_TESTS)]
// With `async`, the template body is generated twice, so rustc errors in it are reported twice.
#![cfg(not(feature = "async"))]

use std::os::unix::fs::symlink;
use std::path::PathBuf;

use trybuild::TestCases;

#[test]
fn ui() {
    let t = TestCases::new();
    t.compile_fail("tests/ui/*.rs");

    // To be able to use existing templates, we create a link to the `templates` folder.
    let manifest_dir = match std::env::var("CARGO_MANIFEST_DIR") {
        Ok(manifest_dir) => PathBuf::from(manifest_dir),
        Err(_) => panic!("you need to run tests with `cargo`"),
    };

    let target_crate_root = manifest_dir.join("../target/tests/trybuild/askama_testing");
    if !target_crate_root.exists()
        && let Err(err) = std::fs::create_dir_all(&target_crate_root)
    {
        panic!(
            "failed to create folder `{}`: {err:?}",
            target_crate_root.display()
        );
    }
    let target_crate_root = target_crate_root.canonicalize().unwrap();

    let symlink = |name: &str| {
        let target = target_crate_root.join(name);
        if !target.exists() {
            let original = manifest_dir.join(name);
            assert!(
                symlink(&original, &target).is_ok(),
                "failed to create to create link on `{}` as `{}`",
                original.display(),
                target.display(),
            );
        }
    };

    // soft-link the templates folder
    symlink("templates");

    // soft-link toml configs
    for entry in manifest_dir.read_dir().unwrap().filter_map(Result::ok) {
        if let Some(name) = entry.file_name().to_str()
            && (name != "Cargo.toml" || !name.ends_with(".toml"))
        {
            symlink(name);
        }
    }
}
