//! # Code to parse a media type or range
//!
//! This is a modification of code in [hyperium/mime](
//! https://github.com/hyperium/mime/tree/1ef137c7358fc64e07c8a640e4e9ba2a784b7f7d/mime-parse/src),
//! so it is mostly copyright 2014-2019 Sean McArthur. See mime-LICENSE.
//!
//! There are multiple, contradictory specs defining the format of a media type.
//! We follow [RFC7231 (HTTP)][RFC7231] because it is least restrictive:
//!
//! > ```ABNF
//! > media-type = type "/" subtype *( OWS ";" OWS parameter )
//! > type       = token
//! > subtype    = token
//! > parameter  = token "=" ( token / quoted-string )
//! > ```
//!
//! Where token is defined as:
//!
//! > ```ABNF
//! > token = 1*tchar
//! > tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" / "." /
//! >    "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA
//! > ```
//!
//! For contrast, [RFC6838 (Media Type Specifications and Registration
//! Procedures)][RFC6838] says:
//!
//! > All registered media types MUST be assigned top-level type and
//! > subtype names.  The combination of these names serves to uniquely
//! > identify the media type, and the subtype name facet (or the absence
//! > of one) identifies the registration tree.  Both top-level type and
//! > subtype names are case-insensitive.
//! >
//! > Type and subtype names MUST conform to the following ABNF:
//! >
//! > ```ABNF
//! > type-name = restricted-name
//! > subtype-name = restricted-name
//! >
//! > restricted-name = restricted-name-first *126restricted-name-chars
//! > restricted-name-first  = ALPHA / DIGIT
//! > restricted-name-chars  = ALPHA / DIGIT / "!" / "#" /
//! >                          "$" / "&" / "-" / "^" / "_"
//! > restricted-name-chars =/ "." ; Characters before first dot always
//! >                              ; specify a facet name
//! > restricted-name-chars =/ "+" ; Characters after last plus always
//! >                              ; specify a structured syntax suffix
//! > ```
//! >
//! > Note that this syntax is somewhat more restrictive than what is allowed
//! > by the ABNF in [Section 5.1 of \[RFC2045\]][RFC2045] or [Section 4.2 of
//! > \[RFC4288\]][RFC4288].  Also note that while this syntax allows names of
//! > up to 127 characters, implementation limits may make such long names
//! > problematic.  For this reason, \<type-name\> and \<subtype-name\> SHOULD
//! > be limited to 64 characters.
//!
//! ¯\\\_(ツ)\_/¯
//!
//! Notably all RFC6838 media types are also HTTP media types.
//!
//! [RFC2045]: https://datatracker.ietf.org/doc/html/rfc2045#section-5.1
//! [RFC4288]: https://datatracker.ietf.org/doc/html/rfc4288#section-4.2
//! [RFC6838]: https://datatracker.ietf.org/doc/html/rfc6838#section-4.2
//! [RFC7231]: https://datatracker.ietf.org/doc/html/rfc7231#section-3.1.1.1

use crate::polyfill::*;
use std::fmt;

/// Parser for media types.
#[derive(Clone, Debug)]
pub struct Parser {
    pub accept_media_range: bool,
}

impl Parser {
    /// Create a `Parser` that can parse media ranges, e.g. `text/*`.
    #[inline]
    pub fn range_parser() -> Self {
        Parser { accept_media_range: true }
    }

    /// Create a `Parser` that parses media types.
    ///
    /// It will reject media ranges, e.g. `text/*`.
    #[inline]
    pub fn type_parser() -> Self {
        Parser { accept_media_range: false }
    }

    /// Actually do the parsing.
    pub const fn parse_const<'a>(
        &self,
        src: &'a str,
    ) -> Result<Mime<'a>, ParseError> {
        let source = Source::Str(src);
        let bytes = src.as_bytes();

        if bytes.len() > u16::MAX as usize {
            return Err(ParseError::TooLong);
        }

        // Validate first byte of type token.
        match bytes {
            [] => {
                // FIXME empty
                return Err(ParseError::MissingSlash);
            }
            [b'*', b'/', b'*', ..] if self.accept_media_range => {
                if bytes[1] == b'/' {
                    panic!("not implemented");
                } else {
                    return Err(ParseError::InvalidToken {
                        pos: 0,
                        byte: Byte(b'*'),
                    });
                }
            }
            // FIXME what about starting with +?
            [c, ..] if is_token(*c) => (),
            [c, ..] => {
                // FIXME if c == b'/', then error missing type?
                return Err(ParseError::InvalidToken {
                    pos: 0,
                    byte: Byte(*c),
                });
            }
        }

        let mut i = 0;

        // Validate rest of type token and find '/'.
        let slash;
        loop {
            i += 1;
            if i >= bytes.len() {
                return Err(ParseError::MissingSlash);
            }

            match bytes[i] {
                b'/' => {
                    slash = as_u16(i);
                    break;
                }
                c if is_token(c) => (),
                c => {
                    return Err(ParseError::InvalidToken {
                        pos: i,
                        byte: Byte(c),
                    })
                }
            };
        }

        // Validate first byte of subtype token.
        i += 1;
        if i >= bytes.len() {
            return Err(ParseError::MissingSubtype);
        }

        let mut plus = None;
        match bytes[i] {
            b'+' => {
                // FIXME? allow start with +?
                plus = Some(as_u16(i));
            }
            b';' | b' ' | b'\t' => {
                return Err(ParseError::MissingSubtype);
            }
            b'*' if self.accept_media_range => {
                // * subtype; peek at next byte to make sure it’s either the end
                // of the input or the end of the subtype.
                if i + 1 >= bytes.len() {
                    return Ok(Mime { source, slash, plus });
                }

                match bytes[i + 1] {
                    b';' | b' ' | b'\t' => (),
                    _ => {
                        return Err(ParseError::InvalidToken {
                            pos: i,
                            byte: Byte(b'*'),
                        })
                    }
                }
            }
            c if is_token(c) => (),
            c => {
                return Err(ParseError::InvalidToken { pos: i, byte: Byte(c) })
            }
        }

        // Validate rest of subtype token and find either space or ';'.
        loop {
            i += 1;
            if i >= bytes.len() {
                return Ok(Mime { source, slash, plus });
            }
            #[allow(clippy::redundant_pattern_matching)] // is_none() not const
            match bytes[i] {
                b'+' if matches!(plus, None) => {
                    plus = Some(as_u16(i));
                }
                b';' | b' ' | b'\t' => {
                    break;
                }
                c if is_token(c) => (),
                c => {
                    return Err(ParseError::InvalidToken {
                        pos: i,
                        byte: Byte(c),
                    })
                }
            };
        }

        panic!("unimplemented");
    }
}

// FIXME should implement Eq, PartialEq, Ord, and PartialOrd manually
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mime<'a> {
    source: Source<'a>,
    slash: u16,
    plus: Option<u16>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Source<'a> {
    Str(&'a str),
    Owned(String),
}

impl<'a> Source<'a> {
    /// Get the source as a byte slice.
    pub fn as_bytes(&'a self) -> &'a [u8] {
        match self {
            Self::Str(src) => src.as_bytes(),
            Self::Owned(src) => src.as_bytes(),
        }
    }
}

/// An error encountered while parsing a media type.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ParseError {
    MissingSlash,
    MissingSubtype,
    MissingEqual,
    MissingQuote,
    InvalidToken { pos: usize, byte: Byte },
    InvalidRange,
    TooLong,
}

impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let description = match self {
            ParseError::MissingSlash => "a slash (/) was missing between the type and subtype",
            ParseError::MissingSubtype => "missing subtype after the slash (/)",
            ParseError::MissingEqual => "an equals sign (=) was missing between a parameter and its value",
            ParseError::MissingQuote => "a quote (\") was missing from a parameter value",
            ParseError::InvalidToken { .. } => "invalid token",
            ParseError::InvalidRange => "unexpected asterisk",
            ParseError::TooLong => "the string is too long",
        };
        if let ParseError::InvalidToken { pos, byte } = *self {
            write!(f, "{}, {:?} at position {}", description, byte, pos)
        } else {
            f.write_str(description)
        }
    }
}

/// Wrapper for `u8` to make displaying bytes as characters easy.
///
/// ```
/// use mime_const::rfc7231::Byte;
/// assert_eq!(format!("{:?}", Byte(b'a')), "'a'".to_string());
/// assert_eq!(format!("{:?}", Byte(0)), "'\\0'".to_string());
/// ```
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Byte(pub u8);

impl fmt::Debug for Byte {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            b'\n' => f.write_str("'\\n'"),
            b'\r' => f.write_str("'\\r'"),
            b'\t' => f.write_str("'\\t'"),
            b'\\' => f.write_str("'\\'"),
            b'\0' => f.write_str("'\\0'"),
            0x20..=0x7f => write!(f, "'{}'", self.0 as char),
            _ => write!(f, "'\\x{:02x}'", self.0),
        }
    }
}

#[inline]
const fn as_u16(i: usize) -> u16 {
    debug_assert!(i <= u16::MAX as usize, "as_u16 overflow");
    i as u16
}

macro_rules! byte_map {
    ($($flag:expr,)*) => ([
        $($flag != 0,)*
    ])
}

const TOKEN_MAP: [bool; 256] = byte_map![
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
];

const fn is_token(c: u8) -> bool {
    TOKEN_MAP[c as usize]
}

#[allow(dead_code)]
const fn is_restricted_quoted_char(c: u8) -> bool {
    c == 9 || (c > 31 && c != 127)
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_parse {
        ($input:expr, Ok(Mime { slash: $slash:expr, plus: $plus:expr, .. })) => {
            assert_eq!(
                Parser::type_parser().parse_const($input),
                Ok(Mime {
                    source: Source::Str($input),
                    slash: $slash,
                    plus: $plus
                })
            );
        };
        ($input:expr, Err($error:expr)) => {
            assert_eq!(Parser::type_parser().parse_const($input), Err($error));
        };
    }

    macro_rules! tests {
        ($($name:ident { $expected:literal == $($value:tt)+ })*) => {
            $(
                #[test]
                fn $name() {
                    assert_parse!($expected, $($value)+);
                }
            )*
        };
    }

    use rfc7231::ParseError::*;

    // FIXME test ranges

    tests! {
        ok_type_subtype { "foo/bar" == Ok(Mime { slash: 3, plus: None, .. }) }
        ok_type_subtype_suffix {
            "foo/bar+hey" == Ok(Mime { slash: 3, plus: Some(7), .. })
        }
        ok_multiple_plus {
            "foo/bar+a+b" == Ok(Mime { slash: 3, plus: Some(7), .. })
        }
        ok_type_plus {
            "foo+c/bar+a+b" == Ok(Mime { slash: 5, plus: Some(9), .. })
        }
        ok_subtype_first_plus {
            "foo/+a+b" == Ok(Mime { slash: 3, plus: Some(4), .. })
        }
        ok_subtype_just_plus {
            "foo/+" == Ok(Mime { slash: 3, plus: Some(4), .. })
        }
        err_empty {  "" == Err(MissingSlash) }
        err_no_slash { "abc" == Err(MissingSlash) }
        err_no_type {
            "/abc" == Err(InvalidToken { pos: 0, byte: Byte(b'/') })
        }
        err_bad_type {
            "a b/abc" == Err(InvalidToken { pos: 1, byte: Byte(b' ') })
        }
        err_no_subtype { "abc/" == Err(MissingSubtype) }
        err_just_slash {
            "/" == Err(InvalidToken { pos: 0, byte: Byte(b'/') })
        }
        err_multiple_slash {
            "ab//c" == Err(InvalidToken { pos: 3, byte: Byte(b'/') })
        }
        err_multiple_separate_slash {
            "ab/c/d" == Err(InvalidToken { pos: 4, byte: Byte(b'/') })
        }
    }
}
