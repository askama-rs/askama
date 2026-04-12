use std::path::Path;
use std::process::Command;

#[test]
fn test_print_config() {
    let Ok(cargo_home) = std::env::var("CARGO_MANIFEST_DIR") else {
        panic!(">> cannot get `CARGO_MANIFEST_DIR` env variable");
    };
    let output = Command::new("cargo")
        .arg("check")
        .current_dir(Path::new(&cargo_home).join("tests/print"))
        .output()
        .unwrap();

    let content = String::from_utf8_lossy(&output.stderr);

    if !output.status.success() {
        panic!("Failed to build `tests/print`: {content}");
    }

    // There should be two of each (one for "all" and one for "ast"/"code").
    assert_eq!(content.split("== Askama AST ==").count(), 3);
    assert_eq!(content.split("== Askama code ==").count(), 3);
}
