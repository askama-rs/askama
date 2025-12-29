#![cfg(not(windows))]

use std::path::PathBuf;
use std::process::Command;

#[test]
fn clippy_lints() {
    let manifest_dir = match std::env::var("CARGO_MANIFEST_DIR") {
        Ok(manifest_dir) => PathBuf::from(manifest_dir),
        Err(_) => panic!("you need to run tests with `cargo`"),
    };

    let clippy = Command::new("cargo")
        .arg("clippy")
        .current_dir(manifest_dir.join("tests/clippy_lints"))
        .output()
        .expect("failed to run `cargo`");
    if !clippy.status.success() {
        panic!(
            "`clippy` failed.\n\n=== STDOUT ===\n\n{}\n=== STDERR ===\n\n{}\n",
            String::from_utf8_lossy(&clippy.stdout),
            String::from_utf8_lossy(&clippy.stderr),
        );
    }
}
