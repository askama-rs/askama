#[cfg(feature = "alloc")]
use alloc::string::String;
use core::any::Any;
use core::fmt;

use either::{Either, for_both};

use crate::{Error, FastWritable, PrimitiveType, Template, Value, Values, filters};

impl<L, R> FastWritable for Either<L, R>
where
    L: FastWritable,
    R: FastWritable,
{
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn Values,
    ) -> Result<(), Error> {
        for_both!(self, this => this.write_into(dest, values))
    }
}

impl<T: PrimitiveType> PrimitiveType for Either<T, T> {
    type Value = T::Value;

    #[inline]
    fn get(&self) -> Self::Value {
        for_both!(self, this => this.get())
    }
}

impl<L, R> Template for Either<L, R>
where
    L: Template,
    R: Template,
{
    #[inline]
    fn render_into_with_values<W: fmt::Write + ?Sized>(
        &self,
        writer: &mut W,
        values: &dyn Values,
    ) -> Result<(), Error> {
        for_both!(self, this => this.render_into_with_values(writer, values))
    }

    #[inline]
    #[cfg(feature = "alloc")]
    fn render_with_values(&self, values: &dyn Values) -> Result<String, Error> {
        // We add a non-default implementation for `render_with_values`,
        // so a better size_hint is used.
        let mut buf = String::new();
        let _ = buf.try_reserve(match self.is_left() {
            true => L::SIZE_HINT,
            false => R::SIZE_HINT,
        });
        self.render_into_with_values(&mut buf, values)?;
        Ok(buf)
    }

    const SIZE_HINT: usize = match (L::SIZE_HINT, R::SIZE_HINT) {
        (l, r) if l >= r => l,
        (_, r) => r,
    };
}

impl<L, R> Value for Either<L, R>
where
    L: Value,
    R: Value,
{
    #[inline]
    fn ref_any(&self) -> Option<&dyn Any> {
        for_both!(self, this => this.ref_any())
    }
}

impl<L, R> Values for Either<L, R>
where
    L: Values,
    R: Values,
{
    #[inline]
    fn get_value<'a>(&'a self, key: &str) -> Option<&'a dyn Any> {
        for_both!(self, this => this.get_value(key))
    }
}

#[cfg(feature = "alloc")]
impl<L, R> filters::AsIndent for Either<L, R>
where
    L: filters::AsIndent,
    R: filters::AsIndent,
{
    #[inline]
    fn as_indent(&self) -> &str {
        for_both!(self, this => this.as_indent())
    }
}

impl<L, R> filters::Escaper for Either<L, R>
where
    L: filters::Escaper,
    R: filters::Escaper,
{
    #[inline]
    fn write_escaped_str<W: fmt::Write>(&self, dest: W, string: &str) -> fmt::Result {
        for_both!(self, this => this.write_escaped_str(dest, string))
    }
}

impl<L, R> filters::HtmlSafe for Either<L, R>
where
    L: filters::HtmlSafe,
    R: filters::HtmlSafe,
{
}

impl<L, R> filters::PluralizeCount for Either<L, R>
where
    L: filters::PluralizeCount,
    R: filters::PluralizeCount,
{
    type Error = Error;

    #[inline]
    fn is_singular(&self) -> Result<bool, Self::Error> {
        for_both!(self, this => this.is_singular().map_err(Into::into))
    }
}
