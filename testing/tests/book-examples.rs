use std::ffi::OsStr;
use std::fs::{read_dir, read_to_string};
use std::path::Path;
use std::sync::Arc;

use askama_parser::{Parsed, SyntaxBuilder};
use pulldown_cmark::{CodeBlockKind, Event, Options, Parser, Tag, TagEnd};

fn check_markdown(file: &Path, errors: &mut usize) {
    let Ok(markdown) = read_to_string(file) else {
        *errors += 1;
        eprintln!("Failed to read {:?}", file);
        return;
    };
    let mut parser = Parser::new_ext(&markdown, Options::all()).into_offset_iter();
    let syntax = SyntaxBuilder {
        name: "txt",
        block_start: None,
        block_end: None,
        expr_start: None,
        expr_end: None,
        comment_start: None,
        comment_end: None,
    }
    .to_syntax()
    .unwrap();

    while let Some((event, range)) = parser.next() {
        if let Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(label))) = event {
            if label.is_empty() {
                *errors += 1;
                eprintln!(
                    ">> missing codeblock label at [{}:{}]: expected `jinja` or `rust`",
                    file.display(),
                    markdown[..range.start].lines().count() + 1,
                );
                continue;
            }
            if !label.contains("jinja") {
                continue;
            }
            if label.split(",").any(|part| part == "ignore") {
                continue;
            }
            let expects_error = label.split(",").any(|part| part == "error");
            let has_jinja = label.split(",").any(|part| part == "jinja");
            if !has_jinja {
                *errors += 1;
                eprintln!(
                    ">> typo in codeblock name at [{}:{}]: expected `jinja`, found `{label}`",
                    file.display(),
                    markdown[..range.start].lines().count() + 1,
                );
            }
            let mut jinja = String::new();
            for (event, _) in parser.by_ref() {
                match event {
                    Event::End(TagEnd::CodeBlock) => break,
                    Event::Text(text) | Event::Html(text) | Event::InlineHtml(text) => {
                        jinja.push_str(&text)
                    }
                    _ => {}
                }
            }
            if let Err(error) = Parsed::new(Arc::from(jinja.clone()), None, &syntax) {
                if !expects_error {
                    *errors += 1;
                    eprintln!(
                        ">> failed to parse jinja codeblock at line [{}:{}] around {:?}",
                        file.display(),
                        markdown[..range.start].lines().count() + 1,
                        &jinja[error.offset..],
                    );
                }
            } else if expects_error {
                *errors += 1;
                eprintln!(
                    ">> jinja codeblock was supposed to be invalid at line [{}:{}]",
                    file.display(),
                    markdown[..range.start].lines().count() + 1,
                );
            }
        }
    }
}

fn go_through_book(p: &Path, errors: &mut usize) {
    for entry in read_dir(p).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_dir() {
            go_through_book(&path, errors);
        } else if path.extension() == Some(OsStr::new("md")) {
            check_markdown(&path, errors);
        }
    }
}

#[test]
fn test_book_examples() {
    let Ok(cargo_home) = std::env::var("CARGO_MANIFEST_DIR") else {
        panic!(">> cannot get `CARGO_MANIFEST_DIR` env variable");
    };
    let mut errors = 0;
    go_through_book(
        &Path::new(&cargo_home).parent().unwrap().join("book/src"),
        &mut errors,
    );
    if errors != 0 {
        panic!(">> errors occurred in book examples check");
    }
}
