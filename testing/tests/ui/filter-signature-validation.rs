mod missing_required_args {
    #[askama::filter_fn]
    pub fn filter0() -> askama::Result<String> {}

    #[askama::filter_fn]
    pub fn filter1(input: usize) -> askama::Result<String> {}

    #[askama::filter_fn]
    pub fn filter2(_: &dyn askama::Values) -> askama::Result<String> {}
}

mod lifetime_args {
    #[askama::filter_fn]
    pub fn filter0<'a>(input: usize, _: &dyn askama::Values, arg: &'a ()) -> askama::Result<String> {}
}

mod const_generic_args {
    #[askama::filter_fn]
    pub fn filter0<const T: bool>(input: usize, _: &dyn askama::Values) -> askama::Result<String> {}
}

mod generic_default {
    #[askama::filter_fn]
    pub fn filter0<T = f64>(input: usize, _: &dyn askama::Values, arg: T) -> askama::Result<String> {}
}

mod missing_rettype {
    #[askama::filter_fn]
    pub fn filter0(input: usize, _: &dyn askama::Values) {}
}

mod argument_destructuring {
    pub struct Wrapper(i64);
    #[askama::filter_fn]
    pub fn filter0(input: usize, _: &dyn askama::Values, Wrapper(arg): Wrapper) -> askama::Result<String> {}
}

mod argument_impl_generic {
    #[askama::filter_fn]
    pub fn filter0(input: usize, _: &dyn askama::Values, arg: impl std::fmt::Display) -> askama::Result<String> {}
}

mod optional_args_before_required {
    #[askama::filter_fn]
    pub fn filter0(input: usize, _: &dyn askama::Values, #[optional(1337)] opt_arg: usize, req_arg: usize) -> askama::Result<String> {}
}

mod optional_arg_generics {
    #[askama::filter_fn]
    pub fn filter0(input: usize, _: &dyn askama::Values, #[optional(1337)] opt_arg: impl std::fmt::Display) -> askama::Result<String> {}

    #[askama::filter_fn]
    pub fn filter1<T: Copy>(input: usize, _: &dyn askama::Values, #[optional(1337usize)] opt_arg: T) -> askama::Result<String> {}

    #[askama::filter_fn]
    pub fn filter2<T: Copy>(input: usize, _: &dyn askama::Values, #[optional(1337usize)] opt_arg: Option<T>) -> askama::Result<String> {}
}

pub fn main() {}