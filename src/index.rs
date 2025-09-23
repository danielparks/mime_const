//! MIME/media type stored as a slice with indices to its parts.

use crate::rfc7231::{
    parse_parameter, unquote_string, ConstMime, Parser, Result,
};
use std::borrow::Cow;

// FIXME should implement Eq, PartialEq, Ord, and PartialOrd manually
#[derive(Clone, Debug)]
pub struct Mime<'a> {
    source: Source<'a>,
    slash: u16,
    plus: Option<u16>,
    end: u16,
    parameters: Parameters,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Source<'a> {
    Str(&'a str),
    #[allow(dead_code)] // FIXME
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
    pub const fn constant(input: &'a str) -> Self {
        // Can’t use `try_constant()` because Self might be dropped.
        match Parser::type_parser().parse_const(input) {
            Ok(ConstMime { source, slash, plus, end, parameters }) => Mime {
                source: Source::Str(source),
                slash,
                plus,
                end,
                parameters,
            },
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
        match Parser::type_parser().parse_const(input) {
            Ok(ConstMime { source, slash, plus, end, parameters }) => {
                Ok(Mime {
                    source: Source::Str(source),
                    slash,
                    plus,
                    end,
                    parameters,
                })
            }
            Err(error) => Err(error),
        }
    }

    pub fn type_(&self) -> &str {
        &self.source.as_str()[0..self.slash.into()]
    }

    pub fn subtype(&self) -> &str {
        &self.source.as_str()[usize::from(self.slash) + 1..self.end.into()]
    }

    pub fn suffix(&self) -> Option<&str> {
        self.plus.map(|plus| {
            &self.source.as_str()[usize::from(plus) + 1..self.end.into()]
        })
    }

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

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
///
/// This only contains indices, so it’s useless without the [`Mime::source`].
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct Parameter {
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
    fn name<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start.into()..self.equal.into()]
    }

    fn value<'a>(&self, src: &'a str) -> Cow<'a, str> {
        if self.quoted {
            // Strip quotes.
            unquote_string(
                &src[usize::from(self.equal) + 2..usize::from(self.end) - 1],
            )
        } else {
            Cow::from(&src[usize::from(self.equal) + 1..self.end.into()])
        }
    }

    fn tuple<'a>(&self, src: &'a str) -> (&'a str, Cow<'a, str>) {
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
                self.index = parameter.end.into();
                Some(parameter.tuple(self.source.as_str()))
            }
        }
    }
}
