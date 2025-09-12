//! # Minimum supported Rust version
//!
//! Currently the minimum supported Rust version (MSRV) is **1.57**. Future
//! increases in the MSRV will require a major version bump.

// Lint configuration in Cargo.toml isn’t supported by cargo-geiger.
#![forbid(unsafe_code)]
// Enable doc_cfg on docsrs so that we get feature markers.
#![cfg_attr(docsrs, feature(doc_cfg))]

use core::ops::Range;
use konst::{option, try_};

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Parameter {
    start: usize,
    equal: usize,
    end: usize,
    quoted: bool,
}

/// Parameters in a MIME type.
///
/// FIXME: We can’t use a `Vec` here because it might be dropped within a `const
/// fn`, such as `MimeType::constant()`. See [E0493] for more information.
///
/// [E0493]: https://doc.rust-lang.org/error_codes/E0493.html
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Parameters {
    None,
    One(Parameter),
    Two(Parameter, Parameter),
    Three(Parameter, Parameter, Parameter),
    // Many(Vec<Parameter>),
}

/// A MIME type (also called a media type).
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MimeType<'a> {
    source: &'a str,
    type_: Range<usize>,
    subtype: Range<usize>,
    suffix: Option<Range<usize>>,
    parameters: Parameters,
}

/// Check if a byte is valid in a token.
///
/// See [RFC 9110 (HTTP Semantics) §5.6.2 Tokens][tokens].
///
/// [tokens]: https://www.rfc-editor.org/rfc/rfc9110#section-5.6.2
pub const fn is_valid_token_byte(b: u8) -> bool {
    // FIXME? the spec says + is a valid token character, but it doesn’t seem
    // like it should be.
    matches!(b,
        b'!' | b'#' | b'$' | b'%' | b'&' | b'\'' | b'*' | // b'+' |
        b'-' | b'.' | b'^' | b'_' | b'`' | b'|' | b'~' |
        b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z',
    )
}

const fn find_non_token_byte(input: &[u8], start: usize) -> Option<usize> {
    let mut i = start;
    while i < input.len() {
        if !is_valid_token_byte(input[i]) {
            return Some(i);
        }
        i += 1;
    }
    None
}

const fn find_non_whitespace_byte(input: &[u8], start: usize) -> Option<usize> {
    let mut i = start;
    while i < input.len() {
        if !matches!(input[i], b' ' | b'\t') {
            return Some(i);
        }
        i += 1;
    }
    None
}

#[derive(Debug, Eq, PartialEq)]
pub enum ParseError {
    /// Input is empty
    Empty,
    /// Missing '/'.
    SlashMissing,
    /// Starts with '/' (no type)
    TypeEmpty,
    /// Invalid character in type (before '/')
    TypeInvalidCharacter(usize),
    /// No subtype (after '/')
    SubtypeEmpty,
    /// Invalid character in subtype (after '/')
    SubtypeInvalidCharacter(usize),
    /// No suffix (after '+')
    SuffixEmpty,
    /// Invalid character in suffix (after '+')
    SuffixInvalidCharacter(usize),
    /// Parameter missing (after ';')
    ParameterEmpty(usize),
    /// Invalid character in parameter (after ';')
    ParameterInvalidCharacter(usize),
    /// Parameter missing '=' (after ';')
    ParameterEqualMissing(usize),
    /// Parameter missing value (after '=')
    ParameterValueEmpty(usize),
    /// More than three parameters (internal limitation)
    TooManyParameters,
    /// Trailing whitespace
    TrailingWhitespace,
}

pub type Result<T, E = ParseError> = core::result::Result<T, E>;

/// Parse the _type_ out of `bytes` starting at `start`.
///
/// > type/subtype+suffix ; parameter_key=value
const fn parse_type(bytes: &[u8], start: usize) -> Result<Range<usize>> {
    match find_non_token_byte(bytes, 0) {
        Some(end) => {
            if end == 0 {
                Err(ParseError::TypeEmpty)
            } else if bytes[end] != b'/' {
                Err(ParseError::TypeInvalidCharacter(end))
            } else {
                Ok(Range { start, end })
            }
        }
        None => Err(ParseError::SlashMissing),
    }
}

/// Parse the _subtype_ out of `bytes` starting at `start`.
///
/// > type/subtype+suffix ; parameter_key=value
const fn parse_subtype(bytes: &[u8], start: usize) -> Result<Range<usize>> {
    let end = match find_non_token_byte(bytes, start) {
        Some(end) if matches!(bytes[end], b'+' | b';' | b' ' | b'\t') => end,
        Some(end) => return Err(ParseError::SubtypeInvalidCharacter(end)),
        None => bytes.len(),
    };

    if end <= start {
        Err(ParseError::SubtypeEmpty)
    } else {
        Ok(Range { start, end })
    }
}

/// Parse the _suffix_ out of `bytes` starting at `plus_index`.
///
/// > type/subtype+suffix ; parameter_key=value
const fn parse_suffix(
    bytes: &[u8],
    plus_index: usize,
) -> Result<Option<Range<usize>>> {
    if plus_index >= bytes.len() || bytes[plus_index] != b'+' {
        return Ok(None);
    }
    let start = plus_index + 1;
    let end = match find_non_token_byte(bytes, start) {
        Some(end) if matches!(bytes[end], b';' | b' ' | b'\t') => end,
        Some(end) => return Err(ParseError::SuffixInvalidCharacter(end)),
        None => bytes.len(),
    };

    if end <= start {
        Err(ParseError::SuffixEmpty)
    } else {
        Ok(Some(Range { start, end }))
    }
}

/// Parse the _parameters_ out of `bytes` starting at `previous_end`.
///
/// > type/subtype+suffix ; parameter_key=value
const fn parse_parameters(
    bytes: &[u8],
    previous_end: usize,
) -> Result<Parameters> {
    match parse_parameter(bytes, previous_end) {
        Err(error) => Err(error),
        Ok(None) => Ok(Parameters::None),
        Ok(Some(one)) => match parse_parameter(bytes, one.end) {
            Err(error) => Err(error),
            Ok(None) => Ok(Parameters::One(one)),
            Ok(Some(two)) => match parse_parameter(bytes, two.end) {
                Err(error) => Err(error),
                Ok(None) => Ok(Parameters::Two(one, two)),
                Ok(Some(three)) => match parse_parameter(bytes, three.end) {
                    Err(error) => Err(error),
                    Ok(None) => Ok(Parameters::Three(one, two, three)),
                    Ok(Some(_four)) => Err(ParseError::TooManyParameters),
                },
            },
        },
    }
}

/// Parse the _parameter_ out of `bytes` starting at `previous_end`.
///
/// > type/subtype+suffix ; parameter_key=value
const fn parse_parameter(
    bytes: &[u8],
    previous_end: usize,
) -> Result<Option<Parameter>> {
    match find_non_whitespace_byte(bytes, previous_end) {
        None if previous_end < bytes.len() => {
            Err(ParseError::TrailingWhitespace)
        }
        None => Ok(None),
        Some(i) if bytes[i] != b';' => {
            Err(ParseError::ParameterInvalidCharacter(i))
        }
        Some(semicolon) => {
            match find_non_whitespace_byte(bytes, semicolon + 1) {
                None => Err(ParseError::ParameterEmpty(semicolon)),
                Some(start) => parse_parameter_key_value(bytes, start),
            }
        }
    }
}

/// Parse the _parameter_ out of `bytes` starting at `start`.
///
/// > type/subtype+suffix ; parameter_key=value
const fn parse_parameter_key_value(
    bytes: &[u8],
    start: usize,
) -> Result<Option<Parameter>> {
    match find_non_token_byte(bytes, start) {
        Some(equal) if start >= equal => Err(ParseError::ParameterEmpty(start)),
        Some(equal) if bytes[equal] == b'=' => {
            // FIXME support quotes
            let end = match find_non_token_byte(bytes, equal + 1) {
                Some(i) if matches!(bytes[i], b';' | b' ' | b'\t') => i,
                Some(i) => {
                    return Err(ParseError::ParameterInvalidCharacter(i))
                }
                None => bytes.len(),
            };

            if end <= equal + 1 {
                // FIXME? is an empty value legal?
                Err(ParseError::ParameterValueEmpty(end))
            } else {
                Ok(Some(Parameter { start, equal, end, quoted: false }))
            }
        }
        Some(i) => Err(ParseError::ParameterInvalidCharacter(i)),
        None => Err(ParseError::ParameterEqualMissing(start)),
    }
}

impl<'a> MimeType<'a> {
    /// Create a `MimeType` in `const` context.
    ///
    /// # Panics
    ///
    /// Will panic if a parse error is encountered.
    #[must_use]
    pub const fn constant(source: &'a str) -> Self {
        match Self::try_constant(source) {
            Ok(mt) => mt,
            Err(_) => panic!("Error parsing MimeType"),
        }
    }

    /// Create a `MimeType` in `const` context.
    ///
    /// # Errors
    ///
    /// Can return [`ParseError`].
    pub const fn try_constant(source: &'a str) -> Result<Self> {
        let bytes = source.as_bytes();
        if bytes.is_empty() {
            return Err(ParseError::Empty);
        }

        let type_ = try_!(parse_type(bytes, 0));
        let subtype = try_!(parse_subtype(bytes, type_.end + 1));
        let suffix = try_!(parse_suffix(bytes, subtype.end));

        let essence_end = option::unwrap_or!(&suffix, &subtype).end;
        let parameters = try_!(parse_parameters(bytes, essence_end));

        Ok(Self { source, type_, subtype, suffix, parameters })
    }

    pub fn tuple(&self) -> (&'a str, &'a str, Option<&'a str>) {
        (
            &self.source[self.type_.clone()],
            &self.source[self.subtype.clone()],
            self.suffix
                .as_ref()
                .map(|range| &self.source[range.clone()]),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_type_subtype() {
        assert_eq!(MimeType::constant("foo/bar").tuple(), ("foo", "bar", None));
    }

    #[test]
    fn parse_type_subtype_suffix() {
        assert_eq!(
            MimeType::constant("foo/bar+hey").tuple(),
            ("foo", "bar", Some("hey"))
        );
    }

    #[test]
    fn parse_one_parameter() {
        assert_eq!(
            MimeType::constant("foo/bar+hey ; a=b").tuple(),
            ("foo", "bar", Some("hey"))
        );
    }

    #[test]
    fn parse_two_parameters() {
        assert_eq!(
            MimeType::constant("foo/bar+hey;a=b ; c=abc").tuple(),
            ("foo", "bar", Some("hey"))
        );
    }

    #[test]
    fn parse_three_parameters() {
        assert_eq!(
            MimeType::constant("foo/bar+hey  ;a=b;  c=abc;key=value").tuple(),
            ("foo", "bar", Some("hey"))
        );
    }

    #[test]
    fn parse_four_parameters() {
        assert_eq!(
            MimeType::try_constant("foo/bar+hey ;a=1;b=2;c=3;d=4"),
            Err(ParseError::TooManyParameters),
        );
    }
}
