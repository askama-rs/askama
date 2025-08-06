macro_rules! spanned {
    ($span:expr => $($x:tt)+) => {
        // if let Some(span) = $span {
            quote::quote_spanned!($span=> $($x)+)
        // } else {
            // quote::quote!($($x)+)
        // }
    }
}

macro_rules! quote_into {
    ($buffer:expr, $span:expr, { $($x:tt)+ } $(,)?) => {{
        let buffer: &mut $crate::integration::Buffer = $buffer;
        let span: ::proc_macro2::Span = $span;
        buffer.write_tokens(::quote::quote_spanned!(span => $($x)+));
    }};
}
