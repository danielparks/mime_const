//! MIME/media type stored as slices.

use crate::rfc7231::{is_valid_token_byte, is_valid_token_byte_not_plus};
use std::borrow::Cow;
use std::fmt;
use std::mem;

/// Replacement for the `?` postfix operator.
///
/// Can‘t be made `pub(crate)`, so it’s here instead of in `crate::const_utils`.
///
/// `?` doesn’t work in `const` because it invokes
/// [`std::convert::Into::into()`], which is not `const`.
macro_rules! try_ {
    ($value:expr) => {
        match $value {
            Ok(value) => value,
            Err(error) => return Err(error),
        }
    };
}

pub struct Mime<'a> {
    pub(crate) type_: &'a str,
    pub(crate) subtype: &'a str,
    pub(crate) suffix: Option<&'a str>,
    pub(crate) parameters: Parameters<'a>,
}

impl<'a> Mime<'a> {
    /// Create a `Mime` or panic.
    ///
    /// ```rust
    /// use mime_const::slice::{Mime, Parameter};
    /// use std::borrow::Cow;
    ///
    /// const MARKDOWN: Mime = Mime::constant(
    ///     "text",
    ///     "markdown",
    ///     None,
    ///     Some(("charset", "utf-8")),
    ///     None,
    /// );
    ///
    /// fn main() {
    ///     assert_eq!(MARKDOWN.type_(), "text");
    ///     assert_eq!(MARKDOWN.subtype(), "markdown");
    ///     assert_eq!(
    ///         MARKDOWN.parameters().next(),
    ///         Some(("charset", Cow::Borrowed("utf-8"))),
    ///     );
    /// }
    /// ```
    pub const fn constant(
        type_: &'a str,
        subtype: &'a str,
        suffix: Option<&'a str>,
        parameter_1: Option<(&'a str, &'a str)>,
        parameter_2: Option<(&'a str, &'a str)>,
    ) -> Self {
        match ConstMime::new(type_, subtype, suffix, parameter_1, parameter_2) {
            Ok(mime) => Self::from_const(mime),
            Err(error) => {
                error.panic();
                panic!("error.panic() did not panic");
            }
        }
    }

    /// Create a `Mime` or return an error.
    ///
    /// ```rust
    /// use mime_const::slice::Mime;
    ///
    /// let mime = Mime::new("image", "svg+xml", Some("xml"), None, None)
    ///     .unwrap();
    ///
    /// assert_eq!(mime.type_(), "image");
    /// assert_eq!(mime.subtype(), "svg+xml");
    /// assert_eq!(mime.suffix(), Some("xml"));
    /// assert_eq!(mime.parameters().next(), None);
    /// ```
    pub const fn new(
        type_: &'a str,
        subtype: &'a str,
        suffix: Option<&'a str>,
        parameter_1: Option<(&'a str, &'a str)>,
        parameter_2: Option<(&'a str, &'a str)>,
    ) -> Result<Self> {
        match ConstMime::new(type_, subtype, suffix, parameter_1, parameter_2) {
            Ok(mime) => Ok(Self::from_const(mime)),
            Err(error) => Err(error),
        }
    }

    /// Convert `ConstMime` to `Mime`.
    #[must_use]
    #[inline]
    const fn from_const(
        ConstMime { type_, subtype, suffix, parameters }: ConstMime<'a>,
    ) -> Self {
        Self { type_, subtype, suffix, parameters: parameters.into_normal() }
    }

    pub fn with_parameter(&mut self, name: &'a str, value: &'a str) -> &Self {
        match mem::replace(&mut self.parameters, Parameters::None) {
            Parameters::None => {
                self.parameters = Parameters::One(Parameter { name, value });
            }
            Parameters::One(one) => {
                self.parameters =
                    Parameters::Two(one, Parameter { name, value });
            }
            Parameters::Two(one, two) => {
                self.parameters =
                    Parameters::Many(vec![one, two, Parameter { name, value }]);
            }
            Parameters::Many(mut vec) => {
                vec.push(Parameter { name, value });
            }
        }
        self
    }

    #[must_use]
    pub const fn type_(&self) -> &str {
        self.type_
    }

    #[must_use]
    pub const fn subtype(&self) -> &str {
        self.subtype
    }

    #[must_use]
    pub const fn suffix(&self) -> Option<&str> {
        self.suffix
    }

    #[must_use]
    pub fn parameters(&self) -> ParameterIter<'_> {
        ParameterIter { parameters: &self.parameters, index: 0 }
    }
}

/// Parameters in a MIME type.
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum Parameters<'a> {
    None,
    One(Parameter<'a>),
    Two(Parameter<'a>, Parameter<'a>),
    /// More than two.
    Many(Vec<Parameter<'a>>),
}

/// Iterator over parameters.
pub struct ParameterIter<'a> {
    parameters: &'a Parameters<'a>,
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
                    Some(one.tuple())
                } else {
                    None
                }
            }
            Parameters::Two(one, two) => {
                if self.index == 0 {
                    self.index += 1;
                    Some(one.tuple())
                } else if self.index == 1 {
                    self.index += 1;
                    Some(two.tuple())
                } else {
                    None
                }
            }
            Parameters::Many(vec) => match vec.get(self.index) {
                Some(parameter) => {
                    self.index += 1;
                    Some(parameter.tuple())
                }
                None => None,
            },
        }
    }
}

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Parameter<'a> {
    pub(crate) name: &'a str,
    pub(crate) value: &'a str,
}

impl<'a> Parameter<'a> {
    #[must_use]
    pub const fn constant(name_value: (&'a str, &'a str)) -> Self {
        match Self::new(name_value) {
            Ok(parameter) => parameter,
            Err(error) => {
                error.panic();
                panic!("error.panic() did not panic");
            }
        }
    }

    pub const fn new((name, value): (&'a str, &'a str)) -> Result<Self> {
        if !validate_token(name) {
            Err(Error::InvalidParameterName)
        } else if !validate_parameter_value(value) {
            Err(Error::InvalidParameterValue)
        } else {
            Ok(Self { name, value })
        }
    }

    #[must_use]
    #[inline]
    pub const fn name(&self) -> &'a str {
        self.name
    }

    #[must_use]
    #[inline]
    pub const fn value(&self) -> &'a str {
        self.value
    }

    #[must_use]
    #[inline]
    pub const fn tuple(&self) -> (&'a str, Cow<'a, str>) {
        (self.name, Cow::Borrowed(self.value))
    }
}

/// Internal struct for working in const-context.
///
/// This can’t contain anything with `Drop`.
struct ConstMime<'a> {
    type_: &'a str,
    subtype: &'a str,
    suffix: Option<&'a str>,
    parameters: ConstParameters<'a>,
}

impl<'a> ConstMime<'a> {
    const fn new(
        type_: &'a str,
        subtype: &'a str,
        suffix: Option<&'a str>,
        parameter_1: Option<(&'a str, &'a str)>,
        parameter_2: Option<(&'a str, &'a str)>,
    ) -> Result<Self> {
        if !validate_token(type_) {
            return Err(Error::InvalidType);
        }

        if let Some(suffix) = suffix {
            let subtype = subtype.as_bytes();
            let suffix = suffix.as_bytes();

            if subtype.len() < suffix.len() {
                return Err(Error::InvalidSuffix);
            }

            let mut i = 0;
            let plus = subtype.len() - suffix.len() - 1;
            while i < plus {
                if !is_valid_token_byte_not_plus(subtype[i]) {
                    if subtype[i] == b'+' {
                        return Err(Error::SuffixNotAfterFirstPlus);
                    } else {
                        return Err(Error::InvalidSubtype);
                    }
                }
                i += 1;
            }

            if subtype[plus] != b'+' {
                return Err(Error::SuffixNotAfterFirstPlus);
            }

            // Check that the suffix is at the end of the subtype and validate.
            i = plus + 1;
            let mut suffix_i = 0;
            while i < subtype.len() {
                if subtype[i] != suffix[suffix_i] {
                    return Err(Error::SuffixNotEndOfSubtype);
                } else if !is_valid_token_byte(subtype[i]) {
                    return Err(Error::InvalidSuffix);
                }
                i += 1;
                suffix_i += 1;
            }
        } else {
            // Subtype must not have a plus in it.
            if !validate_token_no_plus(subtype) {
                return Err(Error::InvalidSubtype);
            }
        }

        let parameters = match (parameter_1, parameter_2) {
            (None, None) => ConstParameters::None,
            (Some(one), None) => {
                ConstParameters::One(try_!(Parameter::new(one)))
            }
            (None, Some(one)) => {
                ConstParameters::One(try_!(Parameter::new(one)))
            }
            (Some(one), Some(two)) => ConstParameters::Two(
                try_!(Parameter::new(one)),
                try_!(Parameter::new(two)),
            ),
        };

        Ok(Self { type_, subtype, suffix, parameters })
    }
}

/// Parameters in a MIME type.
///
/// This can’t contain anything with `Drop`.
#[derive(Debug, Clone, Eq, PartialEq)]
enum ConstParameters<'a> {
    None,
    One(Parameter<'a>),
    Two(Parameter<'a>, Parameter<'a>),
}

impl<'a> ConstParameters<'a> {
    /// Convert `ConstParameters` to `Parameters`.
    #[must_use]
    #[inline]
    const fn into_normal(self) -> Parameters<'a> {
        match self {
            Self::None => Parameters::None,
            Self::One(one) => Parameters::One(one),
            Self::Two(one, two) => Parameters::Two(one, two),
        }
    }
}

#[inline]
pub(crate) const fn validate_token(token: &str) -> bool {
    let mut i = 0;
    let bytes = token.as_bytes();
    while i < bytes.len() {
        if !is_valid_token_byte(bytes[i]) {
            return false;
        }
        i += 1;
    }

    true
}

#[inline]
pub(crate) const fn validate_token_no_plus(token: &str) -> bool {
    let mut i = 0;
    let bytes = token.as_bytes();
    while i < bytes.len() {
        if !is_valid_token_byte_not_plus(bytes[i]) {
            return false;
        }
        i += 1;
    }

    true
}

/// `value` must be representable by `quoted-string`, defined in [RFC7230
/// (HTTP) §3.2.6]:
///
/// > A string of text is parsed as a single value if it is quoted using
/// > double-quote marks.
/// >
/// > ```ABNF
/// > quoted-string  = DQUOTE *( qdtext / quoted-pair ) DQUOTE
/// > qdtext         = HTAB / SP /%x21 / %x23-5B / %x5D-7E / obs-text
/// > obs-text       = %x80-FF
/// > ```
/// >
/// > ...
/// >
/// > The backslash octet ("\") can be used as a single-octet quoting
/// > mechanism within quoted-string and comment constructs.  Recipients
/// > that process the value of a quoted-string MUST handle a quoted-pair
/// > as if it were replaced by the octet following the backslash.
/// >
/// > ```ABNF
/// > quoted-pair    = "\" ( HTAB / SP / VCHAR / obs-text )
/// > ```
///
/// [RFC7230 (HTTP) §3.2.6]: https://datatracker.ietf.org/doc/html/rfc7230#section-3.2.6
#[inline]
pub(crate) const fn validate_parameter_value(value: &str) -> bool {
    let mut i = 0;
    let bytes = value.as_bytes();
    while i < bytes.len() {
        // HTAB / SP / VCHAR / obs-text
        if !matches!(bytes[i], b'\t' | b' ' | 0x21..=0x7e | 0x80..=0xff) {
            return false;
        }
        i += 1;
    }

    true
}

/// An error encountered while parsing a media type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    InvalidType,
    InvalidSubtype,
    InvalidSuffix,
    SuffixNotEndOfSubtype,
    SuffixNotAfterFirstPlus,
    InvalidParameterName,
    InvalidParameterValue,
}

impl Error {
    pub const fn message(&self) -> &'static str {
        use Error::*;
        match self {
            InvalidType => "invalid type",
            InvalidSubtype => "invalid subtype",
            InvalidSuffix => "invalid suffix",
            SuffixNotEndOfSubtype => "suffix does not end the subtype",
            SuffixNotAfterFirstPlus => "suffix not immediately after first '+'",
            InvalidParameterName => "invalid parameter name",
            InvalidParameterValue => "invalid parameter value",
        }
    }

    pub const fn panic(&self) {
        use Error::*;
        match self {
            InvalidType => panic!("invalid type"),
            InvalidSubtype => panic!("invalid subtype"),
            InvalidSuffix => panic!("invalid suffix"),
            SuffixNotEndOfSubtype => panic!("suffix does not end the subtype"),
            SuffixNotAfterFirstPlus => {
                panic!("suffix not immediately after first '+'")
            }
            InvalidParameterName => panic!("invalid parameter name"),
            InvalidParameterValue => panic!("invalid parameter value"),
        }
    }
}

impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.message())
    }
}

/// A `Result` with a [`Error`] error type.
pub type Result<T, E = Error> = std::result::Result<T, E>;
