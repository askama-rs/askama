use askama::Template;

#[test]
fn test_same_dir() {
    // Templates should be searched for in directory path of the declaration.

    #[derive(Template)]
    #[template(path = "lookup-same-path.html")]
    struct HelloWorld;

    assert_eq!(HelloWorld.to_string(), "(1) Hello world in same path.");
}

#[test]
fn test_subdir() {
    // Templates should be searched for in the subdirectory of the caller location.

    #[derive(Template)]
    #[template(path = "lookup/subdir.html")]
    struct HelloWorld;

    assert_eq!(HelloWorld.to_string(), "(2) Hello world in relative path.");
}

#[test]
fn test_configured_then_same_dir() {
    // The caller directory should be accessible even when called from configured directories.

    #[derive(Template)]
    #[template(path = "lookup-configured-then-same-dir.html")]
    struct HelloWorld;

    assert_eq!(
        HelloWorld.to_string(),
        "(3) Hello world in configured paths, then same dir."
    );
}
