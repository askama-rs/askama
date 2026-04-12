use std::path::{Path, PathBuf};
use std::process::Command;

// This test ensures that when `askama` template is rendered from a macro from a different crate,
// it still works.
// This is a regression test for <https://github.com/askama-rs/askama/issues/706>.
#[test]
fn test_macro_include() {
    fn run_test(current_dir: PathBuf) {
        let exit_status = Command::new("cargo")
            .args(["check"])
            .current_dir(current_dir)
            .spawn()
            .unwrap()
            .wait()
            .unwrap();
        assert!(exit_status.success());
    }

    let Ok(cargo_home) = std::env::var("CARGO_MANIFEST_DIR") else {
        panic!(">> cannot get `CARGO_MANIFEST_DIR` env variable");
    };

    run_test(Path::new(&cargo_home).join("tests/macro-include/b"));
    run_test(Path::new(&cargo_home).join("tests/macro-include/c"));
}
