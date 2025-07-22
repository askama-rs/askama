macro_rules! spanned {
    ($span:expr => $($x:tt)+) => {
        // if let Some(span) = $span {
            quote::quote_spanned!($span=> $($x)+)
        // } else {
            // quote::quote!($($x)+)
        // }
    }
}
