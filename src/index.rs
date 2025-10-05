//! MIME/media type stored as a slice with indices to its parts.
#![allow(clippy::manual_map)] // const

use crate::rfc7231::{
    parse_parameter, unquote_string, ConstMime, ConstParameter,
    ConstParameters, Parser, Result,
};
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Debug, Eq)]
pub struct Mime<'a> {
    source: Source<'a>,
    slash: u16,
    plus: Option<u16>,
    end: u16,
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
        match Parser::type_parser().parse_const(input, u16::MAX as usize) {
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
        match Parser::type_parser().parse_const(input, u16::MAX as usize) {
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
            .parse_const(source.as_str(), u16::MAX as usize)
            .map(
                |ConstMime { source: _, slash, plus, end, parameters }| Self {
                    source: source.clone(),
                    slash: slash as _,
                    plus: match plus {
                        Some(plus) => Some(plus as _),
                        None => None,
                    },
                    end: end as _,
                    parameters: Parameters::from_const(parameters),
                },
            )
    }

    /// Convert [`ConstMime`] to [`Mime`].
    const fn from_const(
        ConstMime { source, slash, plus, end, parameters }: ConstMime<'a>,
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
        &self.source.as_str()[usize::from(self.slash) + 1..self.end.into()]
    }

    #[must_use]
    pub fn suffix(&self) -> Option<&str> {
        self.plus.map(|plus| {
            &self.source.as_str()[usize::from(plus) + 1..self.end.into()]
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
        fn sorted_params<'b>(mime: &'b Mime) -> Vec<(String, Cow<'b, str>)> {
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
        fn sorted_params<'b>(mime: &'b Mime) -> Vec<(String, Cow<'b, str>)> {
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
            ConstParameters::One(one) => Self::One(Parameter::from_const(one)),
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
    pub(crate) start: u16,

    /// The index of the `'='`. The start of the value is `equal + 1`.
    pub(crate) equal: u16,

    /// The index just past the last character in the value.
    pub(crate) end: u16,

    /// Whether or not the value is a quoted string.
    pub(crate) quoted: bool,
}

impl Parameter {
    /// Convert [`ConstParameter`] to [`Parameter`].
    const fn from_const(
        ConstParameter { start, equal, end, quoted }: ConstParameter,
    ) -> Self {
        Self { start: start as _, equal: equal as _, end: end as _, quoted }
    }

    pub fn name<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start.into()..self.equal.into()]
    }

    pub fn value<'a>(&self, src: &'a str) -> Cow<'a, str> {
        if self.quoted {
            // Strip quotes.
            unquote_string(
                &src[usize::from(self.equal) + 2..usize::from(self.end) - 1],
            )
        } else {
            Cow::from(&src[usize::from(self.equal) + 1..self.end.into()])
        }
    }

    pub fn tuple<'a>(&self, src: &'a str) -> (&'a str, Cow<'a, str>) {
        (self.name(src), self.value(src))
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
