use askama::Template;

// This test ensures that template paths work even when created from another file.
#[test]
fn cross_file_paths() {
    macro_rules! define_template {
        () => {
            #[derive(askama::Template)]
            #[template(path = "base-decl.txt")]
            struct Empty {}
        };
    }

    #[path = "./auxiliary/paths.rs"]
    mod a;
}

/// When a template is accessed via a symlink (e.g. in content-addressable storage where files
/// lose their extensions), the HTML escaper must be selected based on the symlink's own
/// extension, not the extension-less target file.
#[test]
fn symlink_preserves_extension_for_escaping() {
    #[derive(Template)]
    #[template(path = "symlink-escape.html")]
    struct SymlinkEscapeTemplate<'a> {
        name: &'a str,
    }

    let s = SymlinkEscapeTemplate { name: "<>&\"'" };
    assert_eq!(s.render().unwrap(), "Hello, &#60;&#62;&#38;&#34;&#39;!");
}
