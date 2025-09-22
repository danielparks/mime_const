//! MIME/media type stored as a slice with indices to its parts.

use crate::rfc7231::unquote_string;
use std::borrow::Cow;

// FIXME should implement Eq, PartialEq, Ord, and PartialOrd manually
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mime<'a> {
    pub(crate) source: Source<'a>,
    pub(crate) slash: u16,
    pub(crate) plus: Option<u16>,
    pub(crate) end: u16,
    pub(crate) parameters: Parameters,
}

impl<'a> Mime<'a> {
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
            index: 0,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Source<'a> {
    Str(&'a str),
    #[expect(dead_code, reason = "FIXME")]
    Owned(String),
}

impl<'a> Source<'a> {
    /// Get the source as a `&str`.
    pub fn as_str(&'a self) -> &'a str {
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

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
///
/// This only contains indices, so it’s useless without the [`Mime`] struct and
/// its [`Source`];
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
                panic!("unimplemented"); // FIXME
            }
        }
    }
}
