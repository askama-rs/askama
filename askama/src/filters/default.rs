use core::convert::Infallible;
use core::num::{Saturating, Wrapping};
use core::ops::Deref;
use core::pin::Pin;

use crate::filters::Either;
use crate::{Result, impl_for_ref};

/// Render `value` if it is not its "default" value, see [`DefaultFilterable`],
/// otherwise `fallback`.
#[inline]
pub fn assigned_or<L: DefaultFilterable, R>(
    value: &L,
    fallback: R,
) -> Result<Either<L::Filtered<'_>, R>, L::Error> {
    match value.as_filtered()? {
        Some(value) => Ok(Either::Left(value)),
        None => Ok(Either::Right(fallback)),
    }
}

/// A type (or a reference to it) that can be used in [`|assigned_or`](assigned_or).
///
/// The type is either a monad such as [`Option`] or [`Result`], or a type that has a well defined,
/// trivial default value, e.g. an [empty](str::is_empty) [`str`] or `0` for integer types.
#[diagnostic::on_unimplemented(
    label = "`{Self}` is not `|assigned_or` filterable",
    message = "`{Self}` is not `|assigned_or` filterable"
)]
pub trait DefaultFilterable {
    /// The contained value
    type Filtered<'a>
    where
        Self: 'a;

    /// An error that prevented [`as_filtered()`](DefaultFilterable::as_filtered) to succeed,
    /// e.g. a poisoned state or an unacquirable lock.
    type Error: Into<crate::Error>;

    /// Return the contained value, if a value was contained, and it's not the default value.
    ///
    /// Returns `Ok(None)` if the value could not be unwrapped.
    fn as_filtered(&self) -> Result<Option<Self::Filtered<'_>>, Self::Error>;
}

impl_for_ref! {
    impl DefaultFilterable for T {
        type Filtered<'a> = T::Filtered<'a>
        where
            Self: 'a;

        type Error = T::Error;

        #[inline]
        fn as_filtered(&self) -> Result<Option<Self::Filtered<'_>>, Self::Error> {
            <T>::as_filtered(self)
        }
    }
}

impl<T> DefaultFilterable for Pin<T>
where
    T: Deref,
    <T as Deref>::Target: DefaultFilterable,
{
    type Filtered<'a>
        = <<T as Deref>::Target as DefaultFilterable>::Filtered<'a>
    where
        Self: 'a;

    type Error = <<T as Deref>::Target as DefaultFilterable>::Error;

    #[inline]
    fn as_filtered(&self) -> Result<Option<Self::Filtered<'_>>, Self::Error> {
        self.as_ref().get_ref().as_filtered()
    }
}

impl<T> DefaultFilterable for Option<T> {
    type Filtered<'a>
        = &'a T
    where
        Self: 'a;

    type Error = Infallible;

    #[inline]
    fn as_filtered(&self) -> Result<Option<&T>, Infallible> {
        Ok(self.as_ref())
    }
}

impl<T, E> DefaultFilterable for Result<T, E> {
    type Filtered<'a>
        = &'a T
    where
        Self: 'a;

    type Error = Infallible;

    #[inline]
    fn as_filtered(&self) -> Result<Option<&T>, Infallible> {
        Ok(self.as_ref().ok())
    }
}

impl DefaultFilterable for str {
    type Filtered<'a>
        = &'a str
    where
        Self: 'a;

    type Error = Infallible;

    #[inline]
    fn as_filtered(&self) -> Result<Option<&str>, Infallible> {
        match self.is_empty() {
            false => Ok(Some(self)),
            true => Ok(None),
        }
    }
}

#[cfg(feature = "alloc")]
impl DefaultFilterable for alloc::string::String {
    type Filtered<'a>
        = &'a str
    where
        Self: 'a;

    type Error = Infallible;

    #[inline]
    fn as_filtered(&self) -> Result<Option<&str>, Infallible> {
        self.as_str().as_filtered()
    }
}

#[cfg(feature = "alloc")]
impl<T: DefaultFilterable + alloc::borrow::ToOwned + ?Sized> DefaultFilterable
    for alloc::borrow::Cow<'_, T>
{
    type Filtered<'a>
        = T::Filtered<'a>
    where
        Self: 'a;

    type Error = T::Error;

    #[inline]
    fn as_filtered(&self) -> Result<Option<Self::Filtered<'_>>, Self::Error> {
        self.as_ref().as_filtered()
    }
}

impl<T: DefaultFilterable> DefaultFilterable for Wrapping<T> {
    type Filtered<'a>
        = T::Filtered<'a>
    where
        Self: 'a;

    type Error = T::Error;

    #[inline]
    fn as_filtered(&self) -> Result<Option<Self::Filtered<'_>>, Self::Error> {
        self.0.as_filtered()
    }
}

impl<T: DefaultFilterable> DefaultFilterable for Saturating<T> {
    type Filtered<'a>
        = T::Filtered<'a>
    where
        Self: 'a;

    type Error = T::Error;

    #[inline]
    fn as_filtered(&self) -> Result<Option<Self::Filtered<'_>>, Self::Error> {
        self.0.as_filtered()
    }
}

macro_rules! impl_for_int {
    ($($ty:ty)*) => { $(
        impl DefaultFilterable for $ty {
            type Filtered<'a> = $ty;
            type Error = Infallible;

            #[inline]
            fn as_filtered(&self) -> Result<Option<$ty>, Infallible> {
                match *self {
                    0 => Ok(None),
                    value => Ok(Some(value)),
                }
            }
        }
    )* };
}

impl_for_int!(
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
);

macro_rules! impl_for_non_zero {
    ($($name:ident : $ty:ty)*) => { $(
        impl DefaultFilterable for core::num::$name {
            type Filtered<'a> = $ty;
            type Error = Infallible;

            #[inline]
            fn as_filtered(&self) -> Result<Option<$ty>, Infallible> {
                Ok(Some(self.get()))
            }
        }
    )* };
}

impl_for_non_zero!(
    NonZeroU8:u8 NonZeroU16:u16 NonZeroU32:u32 NonZeroU64:u64 NonZeroU128:u128 NonZeroUsize:usize
    NonZeroI8:i8 NonZeroI16:i16 NonZeroI32:i32 NonZeroI64:i64 NonZeroI128:i128 NonZeroIsize:isize
);

impl DefaultFilterable for bool {
    type Filtered<'a> = bool;
    type Error = Infallible;

    #[inline]
    fn as_filtered(&self) -> Result<Option<bool>, Infallible> {
        match *self {
            true => Ok(Some(true)),
            false => Ok(None),
        }
    }
}
