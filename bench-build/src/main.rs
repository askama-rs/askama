use std::str::FromStr;

use askama::Template as _;
use askama_macros::Template;

fn main() {
    let mut args = std::env::args().fuse().skip(1);
    let greeting = args.next();
    let user = args.next();

    let tmpl = HelloWorld {
        greeting: greeting.as_deref().unwrap_or("hi").parse().unwrap(),
        user: user.as_deref().unwrap_or("user"),
    };
    println!("{}", tmpl.render().unwrap());
}

#[derive(Debug, Clone, Copy, Template)]
#[template(path = "hello_world.html")]
struct HelloWorld<'a> {
    greeting: Greeting,
    user: &'a str,
}

#[derive(Debug, Clone, Copy, Template)]
#[template(path = "greeting.html")]
enum Greeting {
    #[template(block = "hello")]
    Hello,
    #[template(block = "hey")]
    Hey,
    #[template(block = "hi")]
    Hi,
}

impl FromStr for Greeting {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "hello" => Ok(Self::Hello),
            "hey" => Ok(Self::Hey),
            "hi" => Ok(Self::Hi),
            _ => Err("Valid greetings: <hello | hey | hi>"),
        }
    }
}
