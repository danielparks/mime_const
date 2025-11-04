//! MIME/media type stored as a slice with indices to its parts of type `T`.

macro_rules! impl_mime {
    ($t:ty, $max:expr) => {
        use crate::rfc7231::{
            parse_parameter, unquote_string, ConstMime, ConstParameter,
            ConstParameters, ParseError, Parser, Result,
        };
        use std::borrow::Cow;
        use std::cmp::Ordering;
        use std::fmt;
        use std::ops::Range;

        #[derive(Clone, Debug, Eq)]
        pub struct Mime<'a> {
            source: Source<'a>,
            slash: $t,
            plus: Option<$t>,
            end: $t,
            parameters: Parameters,
        }

        impl<'a> Mime<'a> {
            /// Parse a media type at compile time or panic.
            ///
            /// ```rust
            /// use mime_const::index::Mime;
            /// use std::borrow::Cow;
            ///
            /// const MARKDOWN: Mime = Mime::constant("text/markdown; charset=utf-8");
            ///
            /// fn main() {
            ///     assert_eq!(MARKDOWN.type_(), "text");
            ///     assert_eq!(MARKDOWN.subtype(), "markdown");
            ///     assert_eq!(
            ///         MARKDOWN.parameters().next(),
            ///         Some(("charset", Cow::from("utf-8"))),
            ///     );
            /// }
            /// ```
            #[must_use]
            pub const fn constant(input: &'a str) -> Self {
                // Can’t use `try_constant()` because Self might be dropped.
                match Parser::type_parser().parse_const(input, $max) {
                    Ok(const_mime) => Self::from_const(const_mime),
                    Err(error) => {
                        error.panic();
                        panic!("error.panic() did not panic");
                    }
                }
            }

            /// Parse a media type at compile time or return an error.
            ///
            /// ```rust
            /// use mime_const::index::Mime;
            ///
            /// let mime = Mime::try_constant("text/plain").unwrap();
            /// assert_eq!(mime.type_(), "text");
            /// assert_eq!(mime.subtype(), "plain");
            /// assert_eq!(mime.parameters().next(), None);
            /// ```
            pub const fn try_constant(input: &'a str) -> Result<Self> {
                match Parser::type_parser().parse_const(input, $max) {
                    Ok(const_mime) => Ok(Self::from_const(const_mime)),
                    Err(error) => Err(error),
                }
            }

            /// Parse a media type or return an error.
            ///
            /// ```rust
            /// use mime_const::index::Mime;
            ///
            /// let mime = Mime::new("text/plain").unwrap();
            /// assert_eq!(mime.type_(), "text");
            /// assert_eq!(mime.subtype(), "plain");
            /// assert_eq!(mime.parameters().next(), None);
            /// ```
            pub fn new<S: Into<String>>(input: S) -> Result<Self> {
                let source = Source::Owned(input.into());
                Parser::type_parser()
                    .parse_const(source.as_str(), $max)
                    .map(
                        |ConstMime {
                             source: _,
                             slash,
                             plus,
                             end,
                             parameters,
                         }| {
                            Self {
                                source: source.clone(),
                                slash: slash as _,
                                plus: match plus {
                                    Some(plus) => Some(plus as _),
                                    None => None,
                                },
                                end: end as _,
                                parameters: Parameters::from_const(parameters),
                            }
                        },
                    )
            }

            /// Convert [`ConstMime`] to [`Mime`].
            const fn from_const(
                ConstMime { source, slash, plus, end, parameters }: ConstMime<
                    'a,
                >,
            ) -> Self {
                Self {
                    source: Source::Str(source),
                    slash: slash as _,
                    plus: match plus {
                        Some(plus) => Some(plus as _),
                        None => None,
                    },
                    end: end as _,
                    parameters: Parameters::from_const(parameters),
                }
            }

            #[must_use]
            pub fn type_(&self) -> &str {
                &self.source.as_str()[0..self.slash.into()]
            }

            #[must_use]
            pub fn subtype(&self) -> &str {
                &self.source.as_str()
                    [usize::from(self.slash) + 1..self.end.into()]
            }

            #[must_use]
            pub fn suffix(&self) -> Option<&str> {
                self.plus.map(|plus| {
                    &self.source.as_str()
                        [usize::from(plus) + 1..self.end.into()]
                })
            }

            #[must_use]
            pub fn parameters(&'a self) -> ParameterIter<'a> {
                ParameterIter {
                    source: &self.source,
                    parameters: &self.parameters,
                    index: if matches!(self.parameters, Parameters::Many) {
                        self.end.into()
                    } else {
                        0
                    },
                }
            }

            /// Are there any parameters?
            #[must_use]
            pub fn has_parameters(&'a self) -> bool {
                !matches!(&self.parameters, Parameters::None)
            }

            /// Get the maximum number of parameters with a cheap check.
            ///
            /// Returns `0`, `1`, `2`, or [`usize::MAX`].
            #[must_use]
            pub fn parameters_len_max(&'a self) -> usize {
                match &self.parameters {
                    Parameters::None => 0,
                    Parameters::One(_) => 1,
                    Parameters::Two(_, _) => 2,
                    Parameters::Many => usize::MAX,
                }
            }

            /// Update the type with a different subtype.
            pub fn with_subtype(mut self, subtype: &str) -> Result<Self> {
                self.set_subtype(subtype)?;
                Ok(self)
            }

            /// Change the subtype.
            pub fn set_subtype(&mut self, subtype: &str) -> Result<()> {
                // Validate subtype
                let bytes = subtype.as_bytes();
                let (end, plus) =
                    Parser::type_parser().consume_subtype(bytes, 0)?;
                if end < bytes.len() {
                    return Err(ParseError::InvalidToken {
                        pos: end,
                        byte: bytes[end],
                    });
                }

                // self.end must be at least this, so this won’t overflow:
                let start = self.slash + 1;
                let difference: isize = isize::try_from(subtype.len()).unwrap()
                    - isize::try_from(self.end - start).unwrap();
                self.source
                    .set_range(usize::from(start)..self.end.into(), subtype);
                self.end = Self::add(self.end, difference)?;

                // Update suffix
                // plus (if Some) is always < end, so this won’t overflow:
                self.plus =
                    plus.map(|plus| <$t>::try_from(plus).unwrap() + start);

                // Update parameters
                match self.parameters {
                    Parameters::One(ref mut one) => {
                        one.shift(difference)?;
                    }
                    Parameters::Two(ref mut one, ref mut two) => {
                        one.shift(difference)?;
                        two.shift(difference)?;
                    }
                    Parameters::None | Parameters::Many => {}
                }
                Ok(())
            }

            /// Add `base` to `difference` as best we can.
            ///
            /// # Errors
            ///
            /// Returns [`ParseError::TooLong`] on overflow or underflow.
            fn add(base: $t, difference: isize) -> Result<$t> {
                if difference < 0 {
                    (-difference)
                        .try_into()
                        .ok()
                        .and_then(|difference| base.checked_sub(difference))
                } else {
                    difference
                        .try_into()
                        .ok()
                        .and_then(|difference| base.checked_add(difference))
                }
                .ok_or(ParseError::TooLong)
            }
        }

        impl fmt::Display for Mime<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}/{}", self.type_(), self.subtype())?;
                for (key, value) in self.parameters() {
                    write!(f, "; {}={}", key, value)?;
                }
                Ok(())
            }
        }

        impl<'a> PartialEq for Mime<'a> {
            fn eq(&self, other: &Self) -> bool {
                // FIXME can we do this without all the allocations?
                fn sorted_params<'b>(
                    mime: &'b Mime,
                ) -> Vec<(String, Cow<'b, str>)> {
                    let mut vec: Vec<_> = mime
                        .parameters()
                        .map(|(k, v)| (k.to_ascii_lowercase(), v))
                        .collect();
                    vec.sort();
                    vec
                }

                self.type_().eq_ignore_ascii_case(other.type_())
                    && self.subtype().eq_ignore_ascii_case(other.subtype())
                    && self.parameters_len_max() == other.parameters_len_max()
                    && sorted_params(self) == sorted_params(other)
            }
        }

        impl<'a> Ord for Mime<'a> {
            fn cmp(&self, other: &Self) -> Ordering {
                // FIXME can we do this without all the allocations?
                fn sorted_params<'b>(
                    mime: &'b Mime,
                ) -> Vec<(String, Cow<'b, str>)> {
                    let mut vec: Vec<_> = mime
                        .parameters()
                        .map(|(k, v)| (k.to_ascii_lowercase(), v))
                        .collect();
                    vec.sort();
                    vec
                }

                match self
                    .type_()
                    .to_ascii_lowercase()
                    .cmp(&other.type_().to_ascii_lowercase())
                {
                    Ordering::Equal => {}
                    ord => return ord,
                }

                match self
                    .subtype()
                    .to_ascii_lowercase()
                    .cmp(&other.subtype().to_ascii_lowercase())
                {
                    Ordering::Equal => {}
                    ord => return ord,
                }

                sorted_params(self).cmp(&sorted_params(other))
            }
        }

        impl PartialOrd for Mime<'_> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        #[derive(Clone, Debug, Eq, PartialEq)]
        enum Source<'a> {
            Str(&'a str),
            Owned(String),
        }

        impl<'a> Source<'a> {
            /// Get the source as a byte slice.
            fn as_bytes(&'a self) -> &'a [u8] {
                match self {
                    Self::Str(src) => src.as_bytes(),
                    Self::Owned(src) => src.as_bytes(),
                }
            }

            /// Get the source as a `&str`.
            fn as_str(&'a self) -> &'a str {
                match self {
                    Self::Str(src) => src,
                    Self::Owned(src) => src.as_str(),
                }
            }

            /// Ensure this source is `Source::Owned` and get the value.
            fn owned(&mut self) -> &mut String {
                if let Self::Str(str) = *self {
                    *self = Self::Owned(str.to_owned());
                }

                if let Self::Owned(string) = self {
                    string
                } else {
                    unreachable!();
                }
            }

            /// Set a slice of the source to a value
            ///
            /// Will convert the source to `Source::Owned` if it isn’t already.
            fn set_range(&mut self, range: Range<usize>, value: &str) {
                self.owned().replace_range(range, value);
            }
        }

        /// Parameters in a MIME type.
        ///
        /// This can only store the parse information for two parameters because an
        /// arbitrary number of parameters would require a `Vec` and we can’t fill a
        /// `Vec` in a `const fn`.
        ///
        /// Instead, we validate the parameters and re-parse when need to access them.
        #[derive(Debug, Clone, Eq, PartialEq)]
        pub(crate) enum Parameters {
            None,
            One(Parameter),
            Two(Parameter, Parameter),
            /// More than two.
            Many,
        }

        impl Parameters {
            /// Convert [`ConstParameters`] to [`Parameters`].
            const fn from_const(parameters: ConstParameters) -> Self {
                match parameters {
                    ConstParameters::None => Self::None,
                    ConstParameters::One(one) => {
                        Self::One(Parameter::from_const(one))
                    }
                    ConstParameters::Two(one, two) => Self::Two(
                        Parameter::from_const(one),
                        Parameter::from_const(two),
                    ),
                    ConstParameters::Many => Self::Many,
                }
            }
        }

        /// A single parameter in a MIME type, e.g. “charset=utf-8”.
        ///
        /// This only contains indices, so it’s useless without the [`Mime`].
        #[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
        pub struct Parameter {
            /// The index of the start of the parameter name.
            pub(crate) start: $t,

            /// The index of the `'='`. The start of the value is `equal + 1`.
            pub(crate) equal: $t,

            /// The index just past the last character in the value.
            pub(crate) end: $t,

            /// Whether or not the value is a quoted string.
            pub(crate) quoted: bool,
        }

        impl Parameter {
            /// Convert [`ConstParameter`] to [`Parameter`].
            #[must_use]
            const fn from_const(
                ConstParameter { start, equal, end, quoted }: ConstParameter,
            ) -> Self {
                Self {
                    start: start as _,
                    equal: equal as _,
                    end: end as _,
                    quoted,
                }
            }

            #[must_use]
            pub fn name<'a>(&self, src: &'a str) -> &'a str {
                &src[self.start()..self.equal()]
            }

            #[must_use]
            pub fn value<'a>(&self, src: &'a str) -> Cow<'a, str> {
                if self.quoted {
                    // Strip quotes.
                    unquote_string(&src[self.equal() + 2..self.end() - 1])
                } else {
                    Cow::from(&src[self.equal() + 1..self.end()])
                }
            }

            #[inline]
            #[must_use]
            pub fn tuple<'a>(&self, src: &'a str) -> (&'a str, Cow<'a, str>) {
                (self.name(src), self.value(src))
            }

            #[inline]
            #[must_use]
            fn start(&self) -> usize {
                self.start.into()
            }

            #[inline]
            #[must_use]
            fn equal(&self) -> usize {
                self.equal.into()
            }

            #[inline]
            #[must_use]
            fn end(&self) -> usize {
                self.end.into()
            }

            /// Shift the indices in this parameter by `difference`.
            ///
            /// # Errors
            ///
            /// Returns [`ParseError::TooLong`] on overflow or underflow.
            fn shift(&mut self, difference: isize) -> Result<()> {
                self.start = Mime::add(self.start, difference)?;
                self.equal = Mime::add(self.equal, difference)?;
                self.end = Mime::add(self.end, difference)?;
                Ok(())
            }
        }

        /// Iterator over parameters.
        pub struct ParameterIter<'a> {
            source: &'a Source<'a>,
            parameters: &'a Parameters,
            index: usize,
        }

        impl<'a> Iterator for ParameterIter<'a> {
            type Item = (&'a str, Cow<'a, str>);

            fn next(&mut self) -> Option<Self::Item> {
                match self.parameters {
                    Parameters::None => None,
                    Parameters::One(one) => {
                        if self.index == 0 {
                            self.index += 1;
                            Some(one.tuple(self.source.as_str()))
                        } else {
                            None
                        }
                    }
                    Parameters::Two(one, two) => {
                        if self.index == 0 {
                            self.index += 1;
                            Some(one.tuple(self.source.as_str()))
                        } else if self.index == 1 {
                            self.index += 1;
                            Some(two.tuple(self.source.as_str()))
                        } else {
                            None
                        }
                    }
                    Parameters::Many => {
                        let parameter =
                            parse_parameter(self.source.as_bytes(), self.index)
                                .expect("parameters must be valid")?;
                        self.index = parameter.end;
                        Some(parameter.tuple(self.source.as_str()))
                    }
                }
            }
        }

        #[cfg(test)]
        mod test {
            use super::*;
            use assert2::{assert, check};
            use itertools::Itertools;

            #[test]
            fn display_const_lowercase() {
                assert!(
                    Mime::try_constant("text/plain; charset=utf-8")
                        .map(|m| m.to_string())
                        == Ok("text/plain; charset=utf-8".to_owned())
                );
            }

            #[test]
            fn display_new_lowercase() {
                assert!(
                    Mime::new("text/plain; charset=utf-8")
                        .map(|m| m.to_string())
                        == Ok("text/plain; charset=utf-8".to_owned())
                );
            }

            #[test]
            fn display_const_mixed_case() {
                assert!(
                    Mime::try_constant("Text/SGML; CharSet=UTF-8")
                        .map(|m| m.to_string())
                        == Ok("Text/SGML; CharSet=UTF-8".to_owned()),
                );
            }

            #[test]
            fn display_new_mixed_case() {
                assert!(
                    Mime::new("Text/SGML; CharSet=UTF-8")
                        .map(|m| m.to_string())
                        == Ok("Text/SGML; CharSet=UTF-8".to_owned())
                );
            }

            #[test]
            fn display_const_extra_spaces() {
                assert!(
                    Mime::try_constant("text/plain  ;   charset=utf-8")
                        .map(|m| m.to_string())
                        == Ok("text/plain; charset=utf-8".to_owned()),
                );
            }

            #[test]
            fn display_new_extra_spaces() {
                assert!(
                    Mime::new("text/plain   ;  charset=utf-8")
                        .map(|m| m.to_string())
                        == Ok("text/plain; charset=utf-8".to_owned())
                );
            }

            #[test]
            fn display_const_no_spaces() {
                assert!(
                    Mime::try_constant("text/plain;charset=utf-8")
                        .map(|m| m.to_string())
                        == Ok("text/plain; charset=utf-8".to_owned()),
                );
            }

            #[test]
            fn display_new_no_spaces() {
                assert!(
                    Mime::new("text/plain;charset=utf-8")
                        .map(|m| m.to_string())
                        == Ok("text/plain; charset=utf-8".to_owned())
                );
            }

            #[test]
            fn eq_const_spaces() {
                assert!(
                    Mime::try_constant("text/plain;charset=utf-8")
                        == Mime::try_constant("text/plain   ; charset=utf-8")
                );
            }

            #[test]
            fn eq_new_spaces() {
                assert!(
                    Mime::new("text/plain;charset=utf-8")
                        == Mime::new("text/plain   ; charset=utf-8")
                );
            }

            #[test]
            fn eq_const_parameters() {
                assert!(
                    Mime::try_constant("a/b; k1=v1; k2=v2")
                        == Mime::try_constant("a/b; k2=v2; k1=v1")
                );
            }

            #[test]
            fn ne_const_parameters_different_len() {
                assert!(
                    Mime::try_constant("a/b; k1=v1; k2=v2")
                        != Mime::try_constant("a/b; k1=v1")
                );
            }

            #[test]
            fn eq_const_mixed_case() {
                assert!(
                    Mime::try_constant("A/b; K1=aaa; k2=v2")
                        == Mime::try_constant("a/B; K2=v2; k1=aaa")
                );
            }

            #[test]
            fn ne_const_mixed_case_parameter_values() {
                assert!(
                    Mime::try_constant("a/b; k1=AAA; k2=v2")
                        != Mime::try_constant("a/b; k1=aaa; k2=v2")
                );
            }

            #[test]
            fn sort_mime() {
                let source = &[
                    Mime::constant("a/b"),
                    Mime::constant("a/b; k=v"),
                    Mime::constant("A/b; k=v; k2=v"),
                    Mime::constant("b/a; k=v"),
                    Mime::constant("b/B; k=v"),
                    Mime::constant("b/b; k=v2"),
                    Mime::constant("b/b; k2=2; k1=1"),
                    Mime::constant("b/b; k2=1; k1=2"),
                ][..];

                fn stringify<T: ToString>(slice: &[T]) -> Vec<String> {
                    slice.iter().map(|m| m.to_string()).collect()
                }

                let expected = stringify(source);
                for mut permution in source.iter().permutations(expected.len())
                {
                    permution.sort();
                    assert!(expected == stringify(&permution));
                }
            }

            #[test]
            fn update_subtype() {
                check!(
                    Mime::constant("a/b; k1=a; k2=b").with_subtype("foobar")
                        == Mime::try_constant("a/foobar; k1=a; k2=b")
                );
                check!(
                    Mime::constant("a/foo+bar; k1=a; k2=b").with_subtype("b")
                        == Mime::try_constant("a/b; k1=a; k2=b")
                );
                check!(
                    Mime::constant("a/b; k1=a; k2=b").with_subtype("c+d+e")
                        == Mime::try_constant("a/c+d+e; k1=a; k2=b")
                );
                check!(
                    Mime::constant("a/foo+bar; k1=a; k2=b")
                        .with_subtype("c+d+e")
                        == Mime::try_constant("a/c+d+e; k1=a; k2=b")
                );
                check!(
                    Mime::constant("a/b; k1=a; k2=b")
                        .with_subtype("c+d+e")
                        .unwrap()
                        .suffix()
                        == Some("d+e")
                );
                check!(
                    Mime::constant("a/foo+bar; k1=a; k2=b; k3=c")
                        .with_subtype("b")
                        == Mime::try_constant("a/b; k1=a; k2=b; k3=c")
                );
                check!(
                    Mime::constant("a/b; k=v").with_subtype("*")
                        == Err(ParseError::InvalidToken { pos: 0, byte: b'*' })
                );
            }
        }
    };
}

#[allow(clippy::manual_map)] // const
pub mod index_u8 {
    impl_mime!(u8, u8::MAX as usize);
}

#[allow(clippy::manual_map)] // const
pub mod index_u16 {
    impl_mime!(u16, u16::MAX as usize);
}

#[allow(clippy::manual_map)] // const
#[allow(clippy::useless_conversion)] // usize::from(usize)
#[allow(clippy::unnecessary_cast)] // usize as usize
pub mod index_usize {
    impl_mime!(usize, usize::MAX);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::rfc7231::ParseError;
    use assert2::check;

    #[test]
    fn long_subtype() {
        check!(
            index_u8::Mime::constant("a/b; k=v")
                .with_subtype(&"X".repeat(248))
                .unwrap()
                .parameters()
                .count()
                == 1
        );

        for i in 249..260 {
            check!(
                index_u8::Mime::constant("a/b; k=v")
                    .with_subtype(&"X".repeat(i))
                    == Err(ParseError::TooLong)
            );
        }
    }
}
