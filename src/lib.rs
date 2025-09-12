//! # Minimum supported Rust version
//!
//! Currently the minimum supported Rust version (MSRV) is **1.65**. Future
//! increases in the MSRV will require a major version bump.

// Lint configuration in Cargo.toml isn’t supported by cargo-geiger.
#![forbid(unsafe_code)]
// Enable doc_cfg on docsrs so that we get feature markers.
#![cfg_attr(docsrs, feature(doc_cfg))]

use std::ops::Range;

/// A token used in a MIME type.
#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct Token<'a>(&'a str);

/// Parameters for a MIME type.
#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct Parameters<'a>(&'a str); // FIXME

/// A MIME type (also called a media type).
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MimeType<'a> {
    source: &'a str,
    type_: Range<usize>,
    subtype: Range<usize>,
    extension: Option<Range<usize>>,
}

impl<'a> Token<'a> {
    /// Create a `Token` in `const` context.
    ///
    /// # Panics
    ///
    /// Will panic if a parse error is encountered.
    #[must_use]
    pub const fn constant(input: &'a str) -> Self {
        let bytes = input.as_bytes();
        assert!(!bytes.is_empty(), "Token must not be empty");
        assert!(
            find_non_token_byte(bytes, 0).is_none(),
            "Found invalid character when parsing token",
        );

        Self(input)
    }
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

impl<'a> Parameters<'a> {
    /// Create a `Parameters` in `const` context.
    ///
    /// # Panics
    ///
    /// Will panic if a parse error is encountered.
    #[must_use]
    pub const fn constant(input: &'a str) -> Self {
        Self(input)
    }
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

impl<'a> MimeType<'a> {
    /// Create a `MimeType` in `const` context.
    ///
    /// # Panics
    ///
    /// Will panic if a parse error is encountered.
    #[must_use]
    pub const fn constant(source: &'a str) -> Self {
        let bytes = source.as_bytes();
        assert!(!bytes.is_empty(), "MIME type must not be empty");

        let slash_index = match find_non_token_byte(bytes, 0) {
            Some(i) => i,
            None => panic!("MIME type does not contain '/'"),
        };
        // Did we find a character other than '/'?
        assert!(
            bytes[slash_index] == b'/',
            "MIME type contains invalid character"
        );
        assert!(slash_index > 0, "MIME type has empty type");
        let type_ = Range { start: 0, end: slash_index };

        let (subtype_end, extension) = match find_non_token_byte(
            bytes,
            slash_index + 1,
        ) {
            Some(subtype_end) => {
                assert!(
                    bytes[subtype_end] == b'+',
                    "MIME subtype contains invalid character"
                );
                // Has extension
                let extension_end = match find_non_token_byte(
                    bytes,
                    subtype_end + 1,
                ) {
                    Some(extension_end) => {
                        match find_non_whitespace_byte(bytes, extension_end) {
                            Some(parameter_start) => {
                                assert!(
                                    bytes[parameter_start] == b';',
                                    "MIME type parameter contains invalid character"
                                );
                                panic!("Parameters not supported");
                            }
                            None => {
                                // The previous `find_non_token_byte()` would
                                // have returned `None` if it found the end of
                                // the input, so there must be *something*.
                                panic!("MIME type contains trailing whitespace")
                            }
                        }
                    }
                    None => bytes.len(),
                };
                assert!(
                    bytes[subtype_end] == b'+',
                    "MIME subtype contains invalid character"
                );

                assert!(
                    subtype_end + 1 < extension_end,
                    "MIME extension is empty"
                );
                (
                    subtype_end,
                    Some(Range { start: subtype_end + 1, end: extension_end }),
                )
            }
            None => (bytes.len(), None),
        };
        assert!(slash_index + 1 < subtype_end, "MIME type has empty subtype");

        Self {
            source,
            type_,
            subtype: Range { start: slash_index + 1, end: subtype_end },
            extension,
        }
    }

    pub fn tuple(&self) -> (&'a str, &'a str, Option<&'a str>) {
        (
            &self.source[self.type_.clone()],
            &self.source[self.subtype.clone()],
            self.extension
                .as_ref()
                .map(|range| &self.source[range.clone()]),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_debug() {
        assert_eq!(format!("{:?}", Token::constant("foo")), r#"Token("foo")"#);
    }

    #[test]
    #[should_panic(expected = "Token must not be empty")]
    fn token_empty() {
        let _ = Token::constant("");
    }

    #[test]
    #[should_panic(expected = "Found invalid character when parsing token")]
    fn token_invalid_char() {
        let _ = Token::constant("a b");
    }

    #[test]
    fn parameters_debug() {
        assert_eq!(
            format!("{:?}", Parameters::constant("foo")),
            r#"Parameters("foo")"#
        );
    }

    #[test]
    fn parse_type_subtype() {
        assert_eq!(MimeType::constant("foo/bar").tuple(), ("foo", "bar", None));
    }

    #[test]
    fn parse_type_subtype_extension() {
        assert_eq!(
            MimeType::constant("foo/bar+hey").tuple(),
            ("foo", "bar", Some("hey"))
        );
    }
}
