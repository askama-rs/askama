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
