// Test askama outputs that is not handled by `trybuild`.

use std::ffi::OsStr;
use std::fs::{create_dir_all, read_dir, read_to_string, remove_dir_all};
use std::path::{Path, PathBuf};
use std::process::Command;

#[test]
fn test_custom_ui() {
    if !cfg!(target_os = "linux") {
        return;
    }
    let Ok(cargo_home) = std::env::var("CARGO_MANIFEST_DIR") else {
        panic!(">> cannot get `CARGO_MANIFEST_DIR` env variable");
    };
    let bless = std::env::var("TRYBUILD").as_deref() == Ok("overwrite");
    let mut errors = 0;

    go_through_entries(&cargo_home, bless, &mut errors);
    assert!(errors == 0);
}

fn go_through_entries(cargo_home: &str, bless: bool, errors: &mut usize) {
    let cargo_home_path = Path::new(cargo_home).parent().unwrap();
    let test_dir = cargo_home_path.join("target/tests/custom_ui");

    // We don't check whether it succeeds or not.
    let _ = remove_dir_all(&test_dir);
    create_dir_all(&test_dir).expect("failed to create test dir");

    make_link(
        &cargo_home_path.join("testing/templates"),
        &test_dir.join("templates"),
    );
    make_link(&cargo_home_path.join("target"), &test_dir.join("target"));

    let custom_ui_folder = cargo_home_path.join("testing/tests/custom_ui");
    std::fs::write(
        test_dir.join("Cargo.toml"),
        format!(
            r#"
[package]
name = "askama_test"
version = "0.0.1"
edition = "2024"

[workspace]

[dependencies]
askama = {{ path = {:?} }}

[[bin]]
name = "main"
path = "main.rs"
"#,
            cargo_home_path.join("askama").display(),
        ),
    )
    .unwrap();

    for entry in read_dir(&custom_ui_folder).unwrap() {
        let entry = entry.unwrap();
        let test_path = entry.path();
        if !test_path.is_dir() && test_path.extension() == Some(OsStr::new("rs")) {
            print!("> {}...", test_path.file_name().unwrap().display());
            if !run_test(bless, &test_path, &test_dir) {
                *errors += 1;
            }
        }
    }
}

fn run_test(bless: bool, test_path: &Path, test_dir: &Path) -> bool {
    let tmp_file = test_dir.join("main.rs");
    std::fs::copy(test_path, &tmp_file).unwrap();

    let stderr = run_cargo(test_dir);

    let mut stderr_file_path = PathBuf::from(test_path);
    stderr_file_path.set_extension("stderr");
    match read_to_string(&stderr_file_path) {
        Ok(content) if content == stderr => {
            println!(" OK");
            true
        }
        _ if bless => {
            println!(" FAILED");
            std::fs::write(&stderr_file_path, stderr.as_bytes()).unwrap();
            true
        }
        content => {
            eprintln!(
                " FAILED
======== {} ========
Output differs from expected:

=== FOUND ===
{}

{}",
                test_path.file_name().unwrap().display(),
                stderr,
                match content {
                    Ok(content) => format!("=== EXPECTED ===\n{}", content),
                    _ => "No stderr exist yet. Use `TRYBUILD=overwrite` to bless the output"
                        .to_string(),
                },
            );
            false
        }
    }
}

fn run_cargo(test_dir: &Path) -> String {
    let out = Command::new(env!("CARGO"))
        .args(["check", "--bin", "main", "--color", "never"])
        .current_dir(test_dir)
        .output()
        .expect("failed to execute process");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let mut index = 0;
    let mut start = None;
    let mut end = None;

    for line in stderr.split('\n') {
        if start.is_none() && line.trim_start().starts_with("Checking askama_test v0.0.1") {
            start = Some(index + line.len() + 1);
        } else if end.is_none() && line.trim_start().starts_with("Finished `dev` profile [") {
            end = Some(index);
        }
        if start.is_some() && end.is_some() {
            break;
        }
        index += line.len() + 1; // +1 is for the '\n'.
    }
    match (start, end) {
        (Some(start), None) => stderr[start..].to_string(),
        (Some(start), Some(end)) => stderr[start..end].to_string(),
        _ => {
            let stdout = String::from_utf8_lossy(&out.stdout);
            panic!("didn't find `askama_test` start line, stderr:\n{stderr}\n\nstdout:\n{stdout}")
        }
    }
}

fn make_link(original: &Path, destination: &Path) {
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(original, destination).unwrap();
    }
    #[cfg(windows)]
    {
        std::os::windows::fs::symlink_dir(original, destination).unwrap();
    }
}
