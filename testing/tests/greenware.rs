#![cfg(feature = "serde_json")]

use askama::Template;
use serde::Serialize;

#[derive(Template, Serialize)]
#[template(path = "greenware.html", greenware = true)]
struct GreenwarePage {
    title: String,
    items: Vec<String>,
    note: Option<String>,
}

fn page() -> GreenwarePage {
    GreenwarePage {
        title: "Fired & <Greenware>".to_owned(),
        items: vec!["clay".to_owned(), "stone".to_owned()],
        note: Some("maker's mark".to_owned()),
    }
}

/// One test function on purpose: it mutates process-global environment
/// state, and splitting it into several #[test]s would race under the
/// parallel test runner.
#[test]
fn greenware_parity_and_gating() {
    // SAFETY: single-threaded use of the env var within this one test; no
    // other test in this binary reads STONEWARE_GREENWARE.
    unsafe { std::env::remove_var("STONEWARE_GREENWARE") };
    let fired = page().render().expect("fired render");
    assert!(fired.contains("Fired &#38; &#60;Greenware&#62;"));

    // Greenware ON: interpreted render must match the fired render exactly.
    unsafe { std::env::set_var("STONEWARE_GREENWARE", "1") };
    let greenware = page().render().expect("greenware render");
    assert_eq!(
        greenware, fired,
        "greenware (interpreted) and fired (compiled) renders must agree"
    );

    // None branch parity too.
    let mut p = page();
    p.note = None;
    let greenware_none = p.render().expect("greenware render, None branch");
    unsafe { std::env::remove_var("STONEWARE_GREENWARE") };
    let fired_none = p.render().expect("fired render, None branch");
    assert_eq!(greenware_none, fired_none);
    assert!(fired_none.contains("no note"));
}
