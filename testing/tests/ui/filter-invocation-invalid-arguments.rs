use askama::Template;

mod filters {
    #[askama::filter_fn]
    pub fn noargs(input: impl std::fmt::Display, _env: &dyn askama::Values) -> askama::Result<String> {
        Ok(format!("{input}"))
    }

    #[askama::filter_fn]
    pub fn req1(input: impl std::fmt::Display, _env: &dyn askama::Values, req1: usize) -> askama::Result<String> {
        Ok(format!("{input}{req1}"))
    }
}

#[derive(Template)]
#[template(source = r#"{{ "i like cake" | noargs(3) }}"#, ext = "html")]
struct InvokeNoArgFilterWithArgs;

#[derive(Template)]
#[template(source = r#"{{ "i like cake" | noargs(3, "test") }}"#, ext = "html")]
struct InvokeReq1FilterWith2Args;

#[derive(Template)]
#[template(source = r#"{{ "i like cake" | noargs(req1 = 3, nonexisting = "test") }}"#, ext = "html")]
struct InvokeReq1FilterWith2ArgsNamed;

fn main() {
    InvokeNoArgFilterWithArgs.render().unwrap();
}
