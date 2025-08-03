use std::path::{Component, Path, PathBuf};

// The function [`clean()`] was copied from the project [`path_clean`] in version 1.0.1 (rev. [`d8948ae`]).
// License: MIT OR Apache-2.0.
// Authors: Dan Reeves <hey@danreev.es>, Alex Guerra <alex@heyimalex.com>, Adam Reichold
//
// The function [`diff_paths()`] was copied in from the project [`pathdiff`] in version 0.2.3 (rev. [`5180ff5`]).
// License: MIT OR Apache-2.0.
// Copyright 2012-2015 The Rust Project Developers.
//
// Please see their commit history for more information.
//
// [`path_clean`]: <https://github.com/danreeves/path-clean>
// [`pathdiff`]: <https://github.com/Manishearth/pathdiff>
// [`d8948ae`]: <https://github.com/danreeves/path-clean/blob/d8948ae69d349ec33dfe6d6b9c6a0fe30288a117/src/lib.rs#L50-L86>
// [`5180ff5`]: <https://github.com/Manishearth/pathdiff/blob/5180ff5b23d9d7eef0a14de13a3d814eb5d8d65c/src/lib.rs#L18-L86>

/// The core implementation. It performs the following, lexically:
/// 1. Reduce multiple slashes to a single slash.
/// 2. Eliminate `.` path name elements (the current directory).
/// 3. Eliminate `..` path name elements (the parent directory) and the non-`.` non-`..`, element that precedes them.
/// 4. Eliminate `..` elements that begin a rooted path, that is, replace `/..` by `/` at the beginning of a path.
/// 5. Leave intact `..` elements that begin a non-rooted path.
///
/// If the result of this process is an empty string, return the string `"."`, representing the current directory.
pub(crate) fn clean(path: &Path) -> PathBuf {
    let mut out = Vec::new();
    for comp in path.components() {
        match comp {
            Component::CurDir => (),
            Component::ParentDir => match out.last() {
                Some(Component::RootDir) => (),
                Some(Component::Normal(_)) => {
                    out.pop();
                }
                None
                | Some(Component::CurDir)
                | Some(Component::ParentDir)
                | Some(Component::Prefix(_)) => out.push(comp),
            },
            comp => out.push(comp),
        }
    }
    if !out.is_empty() {
        out.iter().collect()
    } else {
        PathBuf::from(".")
    }
}

/// Construct a relative path from a provided base directory path to the provided path.
pub(crate) fn diff_paths(path: &Path, base: &Path) -> Option<PathBuf> {
    if path.is_absolute() != base.is_absolute() {
        if path.is_absolute() {
            Some(PathBuf::from(path))
        } else {
            None
        }
    } else {
        let mut ita = path.components();
        let mut itb = base.components();
        let mut comps = vec![];
        loop {
            match (ita.next(), itb.next()) {
                (None, None) => break,
                (Some(a), None) => {
                    comps.push(a);
                    comps.extend(ita.by_ref());
                    break;
                }
                (None, _) => comps.push(Component::ParentDir),
                (Some(a), Some(b)) if comps.is_empty() && a == b => (),
                (Some(a), Some(Component::CurDir)) => comps.push(a),
                (Some(_), Some(Component::ParentDir)) => return None,
                (Some(a), Some(_)) => {
                    comps.push(Component::ParentDir);
                    for _ in itb {
                        comps.push(Component::ParentDir);
                    }
                    comps.push(a);
                    comps.extend(ita.by_ref());
                    break;
                }
            }
        }
        Some(comps.iter().map(|c| c.as_os_str()).collect())
    }
}

#[test]
fn test_diff_paths() {
    assert_eq!(
        diff_paths(Path::new("/foo/bar"), Path::new("/foo/bar/baz")),
        Some("../".into())
    );
    assert_eq!(
        diff_paths(Path::new("/foo/bar/baz"), Path::new("/foo/bar")),
        Some("baz".into())
    );
    assert_eq!(
        diff_paths(Path::new("/foo/bar/quux"), Path::new("/foo/bar/baz")),
        Some("../quux".into())
    );
    assert_eq!(
        diff_paths(Path::new("/foo/bar/baz"), Path::new("/foo/bar/quux")),
        Some("../baz".into())
    );
    assert_eq!(
        diff_paths(Path::new("/foo/bar"), Path::new("/foo/bar/quux")),
        Some("../".into())
    );

    assert_eq!(
        diff_paths(Path::new("/foo/bar"), Path::new("baz")),
        Some("/foo/bar".into())
    );
    assert_eq!(
        diff_paths(Path::new("/foo/bar"), Path::new("/baz")),
        Some("../foo/bar".into())
    );
    assert_eq!(
        diff_paths(Path::new("foo"), Path::new("bar")),
        Some("../foo".into())
    );
}
