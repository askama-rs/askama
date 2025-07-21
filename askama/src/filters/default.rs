use core::convert::Infallible;
use core::num::{self, FpCategory, Saturating, Wrapping};
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

/// A [pinned][Pin] reference has a value if the referenced data has a value.
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

/// An [`Option`] has a value if it is `Some`.
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

/// A [`Result`] has a value if it is `Ok`.
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

/// A [`str`] has a value if it is not empty.
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

/// A [`String`][alloc::string::String] has a value if it is not empty.
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

/// A [`Cow`][alloc::borrow::Cow] has a value if it's borrowed data has a value.
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

/// A [`Wrapping`] integer has a value if it is not `0`.
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

/// A [`Saturating`] integer has a value if it is not `0`.
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
    ($($name:ident : $ty:ty)*) => { $(
        #[doc = concat!("A [`", stringify!($ty), "`] has a value if it is not `0`.")]
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

        #[doc = concat!("A [`", stringify!($name), "`][num::", stringify!($name),"] always has a value.")]
        impl DefaultFilterable for num::$name {
            type Filtered<'a> = $ty;
            type Error = Infallible;

            #[inline]
            fn as_filtered(&self) -> Result<Option<$ty>, Infallible> {
                Ok(Some(self.get()))
            }
        }
    )* };
}

impl_for_int!(
    NonZeroU8:u8 NonZeroU16:u16 NonZeroU32:u32 NonZeroU64:u64 NonZeroU128:u128 NonZeroUsize:usize
    NonZeroI8:i8 NonZeroI16:i16 NonZeroI32:i32 NonZeroI64:i64 NonZeroI128:i128 NonZeroIsize:isize
);

/// A `bool` has a value if it is [`true`].
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

macro_rules! impl_for_float {
    ($($ty:ty)*) => { $(
        #[doc = concat!(
            "An [`",
            stringify!($ty),
            "`] has a value if it is [`Normal`][FpCategory::Normal], i.e. it is not zero, \
            not sub-normal, not infinite and not NaN."
        )]
        impl DefaultFilterable for $ty {
            type Filtered<'a>
                = Self
            where
                Self: 'a;

            type Error = Infallible;

            #[inline]
            fn as_filtered(&self) -> Result<Option<Self::Filtered<'_>>, Self::Error> {
                Ok((self.classify() == FpCategory::Normal).then_some(*self))
            }
        }
    )* }
}

impl_for_float!(f32 f64);

#[test]
#[cfg(feature = "std")]
fn test_default_filterable() {
    use std::borrow::Cow;
    use std::rc::Rc;
    use std::string::ToString;
    use std::sync::{Arc, Mutex};

    use assert_matches::assert_matches;

    // integers
    assert_matches!(0_u8.as_filtered(), Ok(None));
    assert_matches!(0_u16.as_filtered(), Ok(None));
    assert_matches!(0_u32.as_filtered(), Ok(None));
    assert_matches!(0_u64.as_filtered(), Ok(None));
    assert_matches!(0_u128.as_filtered(), Ok(None));
    assert_matches!(0_usize.as_filtered(), Ok(None));
    assert_matches!(0_i8.as_filtered(), Ok(None));
    assert_matches!(0_i16.as_filtered(), Ok(None));
    assert_matches!(0_i32.as_filtered(), Ok(None));
    assert_matches!(0_i64.as_filtered(), Ok(None));
    assert_matches!(0_i128.as_filtered(), Ok(None));
    assert_matches!(0_isize.as_filtered(), Ok(None));
    assert_matches!(1_u8.as_filtered(), Ok(Some(1)));
    assert_matches!(1_u16.as_filtered(), Ok(Some(1)));
    assert_matches!(1_u32.as_filtered(), Ok(Some(1)));
    assert_matches!(1_u64.as_filtered(), Ok(Some(1)));
    assert_matches!(1_u128.as_filtered(), Ok(Some(1)));
    assert_matches!(1_usize.as_filtered(), Ok(Some(1)));
    assert_matches!(1_i8.as_filtered(), Ok(Some(1)));
    assert_matches!(1_i16.as_filtered(), Ok(Some(1)));
    assert_matches!(1_i32.as_filtered(), Ok(Some(1)));
    assert_matches!(1_i64.as_filtered(), Ok(Some(1)));
    assert_matches!(1_i128.as_filtered(), Ok(Some(1)));
    assert_matches!(1_isize.as_filtered(), Ok(Some(1)));
    assert_matches!((-1_i8).as_filtered(), Ok(Some(-1)));
    assert_matches!((-1_i16).as_filtered(), Ok(Some(-1)));
    assert_matches!((-1_i32).as_filtered(), Ok(Some(-1)));
    assert_matches!((-1_i64).as_filtered(), Ok(Some(-1)));
    assert_matches!((-1_i128).as_filtered(), Ok(Some(-1)));
    assert_matches!((-1_isize).as_filtered(), Ok(Some(-1)));

    // floats
    // -> zero
    assert_matches!(0_f32.as_filtered(), Ok(None));
    assert_matches!(0_f64.as_filtered(), Ok(None));
    // -> subnormal
    assert_matches!((f32::MIN_POSITIVE / 2.0).as_filtered(), Ok(None));
    assert_matches!((f64::MIN_POSITIVE / 2.0).as_filtered(), Ok(None));
    // -> nan
    assert_matches!(f32::NAN.as_filtered(), Ok(None));
    assert_matches!(f64::NAN.as_filtered(), Ok(None));
    // -> infinite
    assert_matches!(f32::NEG_INFINITY.as_filtered(), Ok(None));
    assert_matches!(f32::INFINITY.as_filtered(), Ok(None));
    assert_matches!(f64::NEG_INFINITY.as_filtered(), Ok(None));
    assert_matches!(f64::INFINITY.as_filtered(), Ok(None));
    // -> normal
    assert_matches!(1_f32.as_filtered(), Ok(Some(1.0)));
    assert_matches!((-1_f32).as_filtered(), Ok(Some(-1.0)));
    assert_matches!(f32::MIN.as_filtered(), Ok(Some(f32::MIN)));
    assert_matches!(f32::MIN_POSITIVE.as_filtered(), Ok(Some(f32::MIN_POSITIVE)));
    assert_matches!(f32::MAX.as_filtered(), Ok(Some(f32::MAX)));
    assert_matches!(1_f64.as_filtered(), Ok(Some(1.0)));
    assert_matches!((-1_f64).as_filtered(), Ok(Some(-1.0)));
    assert_matches!(f64::MIN.as_filtered(), Ok(Some(f64::MIN)));
    assert_matches!(f64::MIN_POSITIVE.as_filtered(), Ok(Some(f64::MIN_POSITIVE)));
    assert_matches!(f64::MAX.as_filtered(), Ok(Some(f64::MAX)));

    // non-zero integers
    assert_matches!(num::NonZeroU8::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroU16::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroU32::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroU64::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroU128::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(
        num::NonZeroUsize::new(1).unwrap().as_filtered(),
        Ok(Some(1))
    );
    assert_matches!(num::NonZeroI8::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroI16::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroI32::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroI64::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(num::NonZeroI128::new(1).unwrap().as_filtered(), Ok(Some(1)));
    assert_matches!(
        num::NonZeroIsize::new(1).unwrap().as_filtered(),
        Ok(Some(1))
    );

    // strings
    assert_matches!("".as_filtered(), Ok(None));
    assert_matches!("hello".as_filtered(), Ok(Some("hello")));
    assert_matches!("".to_string().as_filtered(), Ok(None));
    assert_matches!("hello".to_string().as_filtered(), Ok(Some("hello")));
    assert_matches!(Cow::Borrowed("").as_filtered(), Ok(None));
    assert_matches!(Cow::Borrowed("hello").as_filtered(), Ok(Some("hello")));
    assert_matches!(Cow::<str>::Owned("".to_string()).as_filtered(), Ok(None));
    assert_matches!(
        Cow::<str>::Owned("hello".to_string()).as_filtered(),
        Ok(Some("hello"))
    );

    // results + options
    assert_matches!(Ok::<(), ()>(()).as_filtered(), Ok(Some(())));
    assert_matches!(Err::<(), ()>(()).as_filtered(), Ok(None));
    assert_matches!(Some(()).as_filtered(), Ok(Some(())));
    assert_matches!(None::<()>.as_filtered(), Ok(None));

    // references
    assert_matches!(Arc::new("").as_filtered(), Ok(None));
    assert_matches!(Arc::new("hello").as_filtered(), Ok(Some("hello")));
    assert_matches!(Arc::pin("").as_filtered(), Ok(None));
    assert_matches!(Arc::pin("hello").as_filtered(), Ok(Some("hello")));
    assert_matches!(Rc::new("").as_filtered(), Ok(None));
    assert_matches!(Rc::new("hello").as_filtered(), Ok(Some("hello")));
    assert_matches!(Rc::pin("").as_filtered(), Ok(None));
    assert_matches!(Rc::pin("hello").as_filtered(), Ok(Some("hello")));
    assert_matches!(Mutex::new("").try_lock().unwrap().as_filtered(), Ok(None));
    assert_matches!(
        Mutex::new("hello").try_lock().unwrap().as_filtered(),
        Ok(Some("hello"))
    );
}
