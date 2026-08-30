//! Template source abstraction.
//!
//! Askama reads external templates from the filesystem, through the single
//! cached chokepoint in [`crate::input::get_template_source`]. This module
//! routes that read through a trait so alternative template stores (a
//! database, an in-memory overlay, a remote fetch) can plug in without
//! touching the parser or the generator.
//!
//! [`FsSource`] is the default and only in-tree implementation — behavior is
//! byte-for-byte identical to `std::fs::read_to_string` at the chokepoint.

use std::path::Path;

/// Where external template bodies come from at macro-expansion time.
pub(crate) trait TemplateSource: Send + Sync {
    /// Read the full body of the template identified by `path`.
    ///
    /// The error string is surfaced verbatim inside the compile error emitted
    /// at the call site, so it must name the actual reason the read failed —
    /// never a generic "not found".
    fn read(&self, path: &Path) -> Result<String, String>;
}

/// Upstream behavior: read the template from the filesystem.
pub(crate) struct FsSource;

impl TemplateSource for FsSource {
    fn read(&self, path: &Path) -> Result<String, String> {
        std::fs::read_to_string(path).map_err(|err| err.to_string())
    }
}

/// The active template source for this expansion.
///
/// Always the filesystem today — zero behavior change.
pub(crate) fn active_source() -> &'static dyn TemplateSource {
    static FS: FsSource = FsSource;
    &FS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fs_source_reads_file() {
        let dir = std::env::temp_dir().join("askama-source-test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("t.html");
        std::fs::write(&path, "hello {{ name }}\n").unwrap();
        let body = active_source().read(&path).unwrap();
        assert_eq!(body, "hello {{ name }}\n");
    }

    #[test]
    fn fs_source_error_names_reason() {
        let err = FsSource
            .read(Path::new("/definitely/not/a/real/template.html"))
            .unwrap_err();
        // The error must carry the underlying io reason, not a bare failure.
        assert!(!err.is_empty());
    }
}
