# askama + actix-web example web app

This is a simple web application that uses askama as template engine, and
[actix-web](https://crates.io/crates/actix-web) as web framework.
It lets the user of the web page select a display language, and asks for their name.
The example shows the interaction between both projects, and serves as an example to use
basic askama features such as base templates to a unified layout skeleton for your page,
and less boilerplate in your template code.

To run the example execute `cargo run` in this folder.
Once the project is running, open <http://127.0.0.1:8080/> in your browser.
To gracefully shut does the server, type ctrl+C in your terminal.

The files of the project contain comments for you to read.
The recommended reading order is "templates/_layout.html", "templates/index.html",
"Cargo.toml", "src/main.rs". Also please have a look at our [book](https://askama.rs/),
which explains askama's features in greater detail.
