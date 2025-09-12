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

/// A MIME type (also called a media type).
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MimeType<'a> {
    source: &'a str,
    type_: Range<usize>,
    subtype: Range<usize>,
    suffix: Option<Range<usize>>,
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

#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("input is empty")]
    Empty,
    #[error("no '/'")]
    NoSlash,
    #[error("starts with '/' (no type)")]
    TypeEmpty,
    #[error("invalid character in type (before '/')")]
    TypeInvalidCharacter(usize),
    #[error("no subtype (after '/')")]
    SubtypeEmpty,
    #[error("invalid character in subtype (after '/')")]
    SubtypeInvalidCharacter(usize),
    #[error("no suffix (after '+')")]
    SuffixEmpty,
    #[error("invalid character in suffix (after '+')")]
    SuffixInvalidCharacter(usize),
    #[error("invalid character in parameter (after ';')")]
    ParameterInvalidCharacter(usize),
    #[error("trailing whitespace")]
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
        None => Err(ParseError::NoSlash),
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

        let essence_end = option::unwrap_or!(&suffix, &subtype).end + 1;
        match find_non_whitespace_byte(bytes, essence_end) {
            None if essence_end < bytes.len() => {
                return Err(ParseError::TrailingWhitespace)
            }
            None => {}
            // FIXME parameters not supported.
            Some(parameters_start) => {
                return Err(ParseError::ParameterInvalidCharacter(
                    parameters_start,
                ))
            }
        }

        Ok(Self { source, type_, subtype, suffix })
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
}
