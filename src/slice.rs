//! MIME/media type stored as slices.

use crate::rfc7231::{is_valid_token_byte, is_valid_token_byte_not_plus};
use std::fmt;
use std::mem;

pub struct Mime<'a> {
    pub(crate) type_: &'a str,
    pub(crate) subtype: &'a str,
    pub(crate) suffix: Option<&'a str>,
    pub(crate) parameters: Parameters<'a>,
}

impl<'a> Mime<'a> {
    pub const fn constant(
        type_: &'a str,
        subtype: &'a str,
        suffix: Option<&'a str>,
        parameter_1: Option<Parameter<'a>>,
        parameter_2: Option<Parameter<'a>>,
    ) -> Self {
        // FIXME this is a copy and paste of `new()`.
        if !validate_token(type_) {
            panic!("InvalidType");
        }

        if let Some(suffix) = suffix {
            let subtype = subtype.as_bytes();
            let suffix = suffix.as_bytes();

            if subtype.len() < suffix.len() {
                panic!("InvalidSuffix");
            }

            let mut i = 0;
            let plus = subtype.len() - suffix.len() - 1;
            while i < plus {
                if !is_valid_token_byte_not_plus(subtype[i]) {
                    if subtype[i] == b'+' {
                        panic!("SuffixNotAfterFirstPlus");
                    } else {
                        panic!("InvalidSubtype");
                    }
                }
                i += 1;
            }

            if subtype[plus] != b'+' {
                panic!("SuffixNotAfterFirstPlus");
            }

            // Check that the suffix is at the end of the subtype and validate.
            i = plus + 1;
            let mut suffix_i = 0;
            while i < subtype.len() {
                if subtype[i] != suffix[suffix_i] {
                    panic!("SuffixNotEndOfSubtype");
                } else if !is_valid_token_byte(subtype[i]) {
                    panic!("InvalidSuffix");
                }
                i += 1;
                suffix_i += 1;
            }
        } else {
            // Subtype must not have a plus in it.
            if !validate_token_no_plus(subtype) {
                panic!("InvalidSubtype");
            }
        }

        let parameters = match (parameter_1, parameter_2) {
            (None, None) => Parameters::None,
            (Some(one), None) => Parameters::One(one),
            (None, Some(one)) => Parameters::One(one),
            (Some(one), Some(two)) => Parameters::Two(one, two),
        };

        Self { type_, subtype, suffix, parameters }
    }

    pub const fn new(
        type_: &'a str,
        subtype: &'a str,
        suffix: Option<&'a str>,
        parameter_1: Option<Parameter<'a>>,
        parameter_2: Option<Parameter<'a>>,
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
            (None, None) => Parameters::None,
            (Some(one), None) => Parameters::One(one),
            (None, Some(one)) => Parameters::One(one),
            (Some(one), Some(two)) => Parameters::Two(one, two),
        };

        Ok(Self { type_, subtype, suffix, parameters })
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
///
/// Instead, we validate the parameters and re-parse when need to access them.
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
    type Item = &'a Parameter<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.parameters {
            Parameters::None => None,
            Parameters::One(one) => {
                if self.index == 0 {
                    self.index += 1;
                    Some(one)
                } else {
                    None
                }
            }
            Parameters::Two(one, two) => {
                if self.index == 0 {
                    self.index += 1;
                    Some(one)
                } else if self.index == 1 {
                    self.index += 1;
                    Some(two)
                } else {
                    None
                }
            }
            Parameters::Many(vec) => match vec.get(self.index) {
                Some(parameter) => {
                    self.index += 1;
                    Some(parameter)
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
    pub const fn constant(name: &'a str, value: &'a str) -> Self {
        // FIXME this is copy and paste of new
        if !validate_token(name) {
            panic!("InvalidParameterName");
        } else if !validate_parameter_value(value) {
            panic!("InvalidParameterValue");
        } else {
            Self { name, value }
        }
    }

    pub const fn new(name: &'a str, value: &'a str) -> Result<Self> {
        if !validate_token(name) {
            Err(Error::InvalidParameterName)
        } else if !validate_parameter_value(value) {
            Err(Error::InvalidParameterValue)
        } else {
            Ok(Self { name, value })
        }
    }

    #[must_use]
    pub const fn name(&self) -> &'a str {
        self.name
    }

    #[must_use]
    pub const fn value(&self) -> &'a str {
        self.value
    }
}

#[inline]
const fn validate_token(token: &str) -> bool {
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
const fn validate_token_no_plus(token: &str) -> bool {
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
const fn validate_parameter_value(value: &str) -> bool {
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
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Error {
    InvalidType,
    InvalidSubtype,
    InvalidSuffix,
    SuffixNotEndOfSubtype,
    SuffixNotAfterFirstPlus,
    InvalidParameterName,
    InvalidParameterValue,
}

impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            InvalidType => f.write_str("invalid type"),
            InvalidSubtype => f.write_str("invalid subtype"),
            InvalidSuffix => f.write_str("invalid suffix"),
            SuffixNotEndOfSubtype => {
                f.write_str("suffix does not end the subtype")
            }
            SuffixNotAfterFirstPlus => {
                f.write_str("suffix not immediately after first '+'")
            }
            InvalidParameterName => f.write_str("invalid parameter name"),
            InvalidParameterValue => f.write_str("invalid parameter value"),
        }
    }
}

/// A `Result` with a [`Error`] error type.
pub type Result<T, E = Error> = std::result::Result<T, E>;
