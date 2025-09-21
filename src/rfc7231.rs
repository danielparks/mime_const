//! # Code to parse a media type or range
//!
//! This is a modification of code in [hyperium/mime](
//! https://github.com/hyperium/mime/tree/1ef137c7358fc64e07c8a640e4e9ba2a784b7f7d/mime-parse/src),
//! so it is mostly copyright 2014-2019 Sean McArthur. See mime-LICENSE.
//!
//! There are multiple, contradictory specs defining the format of a media type.
//! We _mostly_ (see [Parsing details](#parsing-details) below) follow [RFC7231
//! (HTTP)] because it is least restrictive:
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
//! Notably all RFC6838 media types are also HTTP media types. However, HTTP is
//! more restrictive than, say, [RFC2045 (Internet Message Bodies)][RFC2045],
//! appears to allow whitespace around the slash and the equals in parameters.
//!
//! ## Parsing details
//!
//!   * Contrary to the spec, we don’t allow `*` in a type, subtype, parameter
//!     name, or unquoted parameter value. In a type of subtype it would make it
//!     hard to distinguish from a range. FIXME? Does this matter?
//!   * Following the spec, we don’t allow empty unquoted parameter values, but
//!     do allow empty quoted values.
//!   * Following the spec, we allow `+` anywhere in the type, subtype,
//!     parameter names, and unquoted parameter values.
//!
//! [RFC2045]: https://datatracker.ietf.org/doc/html/rfc2045#section-5.1
//! [RFC4288]: https://datatracker.ietf.org/doc/html/rfc4288#section-4.2
//! [RFC6838]: https://datatracker.ietf.org/doc/html/rfc6838#section-4.2
//! [RFC7231 (HTTP)]: https://datatracker.ietf.org/doc/html/rfc7231#section-3.1.1.1

use crate::index::{Mime, Parameter, Parameters, Source};
use std::fmt;

/// Replacement for the `?` postfix operator.
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

/// Parser for media types.
#[derive(Clone, Debug)]
pub struct Parser {
    pub accept_media_range: bool,
}

// FIXME how do we deal with case?

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
    pub const fn parse_const<'a>(&self, src: &'a str) -> Result<Mime<'a>> {
        let source = Source::Str(src);
        let bytes = src.as_bytes();

        if bytes.len() > u16::MAX as usize {
            return Err(ParseError::TooLong);
        }

        // Check the first bytes.
        let (i, slash, plus) = match bytes {
            [] | [b'/', ..] => {
                return Err(ParseError::MissingType);
            }
            b"*/*" | [b'*', b'/', b'*', b' ' | b';', ..]
                if self.accept_media_range =>
            {
                // Everything range with or without parameters.
                (3, 1, None)
            }
            [c, ..] if is_valid_token_byte(*c) => {
                let i = try_!(self.consume_type(bytes));
                let slash = as_u16(i);
                let (i, plus) = try_!(self.consume_subtype(bytes, i));
                (i, slash, plus)
            }
            [c, ..] => {
                return Err(ParseError::InvalidToken {
                    pos: 0,
                    byte: Byte(*c),
                });
            }
        };

        let end = as_u16(i);

        let parameters = try_!(parse_parameters(bytes, i));
        Ok(Mime { source, slash, plus, end, parameters })
    }

    /// Validate the type and return the index of the slash.
    const fn consume_type(&self, bytes: &[u8]) -> Result<usize> {
        // Validate rest of type token and find '/'.
        match consume_token(bytes, 1) {
            Some((i, b'/')) => Ok(i),
            Some((i, c)) => {
                Err(ParseError::InvalidToken { pos: i, byte: Byte(c) })
            }
            None => Err(ParseError::MissingSlash),
        }
    }

    /// Validate the subtype and return the index after the last character.
    const fn consume_subtype(
        &self,
        bytes: &[u8],
        start: usize,
    ) -> Result<(usize, Option<u16>)> {
        // Validate first byte of subtype token.
        let mut i = start + 1;
        let mut plus = None;
        match get_byte(bytes, i) {
            None | Some(b';' | b' ' | b'\t') => {
                return Err(ParseError::MissingSubtype)
            }
            Some(b'+') => {
                plus = Some(as_u16(i));
            }
            Some(b'*') if self.accept_media_range => {
                // * subtype; check next byte to make sure it’s either the end
                // of the input or the end of the subtype.
                return match get_byte(bytes, i + 1) {
                    None | Some(b';' | b' ' | b'\t') => Ok((i + 1, plus)),
                    Some(_) => {
                        // subtype starts with *, which is invalid
                        Err(ParseError::InvalidToken {
                            pos: i,
                            byte: Byte(b'*'),
                        })
                    }
                };
            }
            Some(c) if is_valid_token_byte(c) => (),
            Some(c) => {
                return Err(ParseError::InvalidToken { pos: i, byte: Byte(c) })
            }
        }

        // Validate rest of subtype token and find either space or ';'.
        loop {
            i += 1;
            #[allow(clippy::redundant_pattern_matching)] // is_none() not const
            match get_byte(bytes, i) {
                None | Some(b';' | b' ' | b'\t') => return Ok((i, plus)),
                Some(b'+') if matches!(plus, None) => {
                    plus = Some(as_u16(i));
                }
                Some(c) if is_valid_token_byte(c) => (),
                Some(c) => {
                    return Err(ParseError::InvalidToken {
                        pos: i,
                        byte: Byte(c),
                    })
                }
            }
        }
    }
}

/// Parse parameters from `bytes` starting at `start`.
///
/// Parameters look like `; key=value; key2=value2`.
const fn parse_parameters(bytes: &[u8], start: usize) -> Result<Parameters> {
    let one = match try_!(parse_parameter(bytes, start)) {
        None => return Ok(Parameters::None),
        Some(one) => one,
    };

    let two = match try_!(parse_parameter(bytes, one.end as usize)) {
        None => return Ok(Parameters::One(one)),
        Some(two) => two,
    };

    let mut i = match try_!(parse_parameter(bytes, two.end as usize)) {
        None => return Ok(Parameters::Two(one, two)),
        Some(Parameter { end, .. }) => end as usize,
    };

    // More than two parameters. Parse the remaining parameters to validate
    // them, but drop the results because we can’t store them.
    loop {
        i = match try_!(parse_parameter(bytes, i)) {
            None => return Ok(Parameters::Many),
            Some(Parameter { end, .. }) => end as usize,
        }
    }
}

/// Parse a parameter out of `bytes` starting at `start`.
///
/// First this consumes the separator (`[ \t]*;[ \t]`), then it passes off
/// the actual key=value parsing to [`parse_parameter_key_value()`].
const fn parse_parameter(
    bytes: &[u8],
    start: usize,
) -> Result<Option<Parameter>> {
    match consume_whitespace(bytes, start) {
        None if start < bytes.len() => Err(ParseError::TrailingWhitespace),
        None => Ok(None),
        Some((semicolon, b';')) => {
            match consume_whitespace(bytes, semicolon + 1) {
                None => Err(ParseError::MissingParameter { pos: semicolon }),
                Some((start, _)) => parse_parameter_key_value(bytes, start),
            }
        }
        Some((i, c)) => {
            Err(ParseError::InvalidParameter { pos: i, byte: Byte(c) })
        }
    }
}

/// Parse a parameter key=value out of `bytes` starting at `start`.
const fn parse_parameter_key_value(
    bytes: &[u8],
    start: usize,
) -> Result<Option<Parameter>> {
    match consume_token(bytes, start) {
        Some((i, b';')) if i == start => {
            Err(ParseError::MissingParameter { pos: i })
        }
        Some((i, c)) if i == start => {
            Err(ParseError::InvalidParameter { pos: i, byte: Byte(c) })
        }
        Some((equal, b'=')) => {
            let end = match consume_token(bytes, equal + 1) {
                Some((i, b'"')) if i == equal + 1 => {
                    let end = try_!(parse_quoted_string(bytes, i));
                    return Ok(Some(Parameter {
                        start: as_u16(start),
                        equal: as_u16(equal),
                        end: as_u16(end),
                        quoted: true,
                    }));
                }
                Some((i, b';' | b' ' | b'\t')) => i,
                Some((i, c)) => {
                    return Err(ParseError::InvalidParameter {
                        pos: i,
                        byte: Byte(c),
                    })
                }
                None => bytes.len(),
            };

            if end <= equal + 1 {
                Err(ParseError::MissingParameterValue { pos: end })
            } else {
                Ok(Some(Parameter {
                    start: as_u16(start),
                    equal: as_u16(equal),
                    end: as_u16(end),
                    quoted: false,
                }))
            }
        }
        Some((i, c)) => {
            Err(ParseError::InvalidParameter { pos: i, byte: Byte(c) })
        }
        None => Err(ParseError::MissingParameterEqual { pos: start }),
    }
}

/// # Parse `quoted-string`.
///
/// `input[i]` must by `b'"'`.
///
/// Returns the index + 1 of the last byte in the quoted string (always `b'"'`).
///
/// [RFC7230 (HTTP) §3.2.6] defines `quoted-string`:
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
/// # Panics
///
/// If `input.get(i) != Some(b'"')`.
///
/// # Errors
///
/// Returns variants of [`ParseError`] for errors in the quoted string.
///
/// [RFC7230 (HTTP) §3.2.6]: https://datatracker.ietf.org/doc/html/rfc7230#section-3.2.6
const fn parse_quoted_string(input: &[u8], mut i: usize) -> Result<usize> {
    assert!(
        matches!(get_byte(input, i), Some(b'"')),
        "quoted-string must start with '\"'",
    );

    i += 1;
    loop {
        match get_byte(input, i) {
            Some(b'"') => {
                // End of the quoted-string.
                return Ok(i + 1); // input[i] existed, so i + 1 <= input.len()
            }
            Some(b'\\') => {
                // Start of quoted-pair.
                i += 1;
                match get_byte(input, i) {
                    // HTAB / SP / VCHAR / obs-text
                    Some(b'\t' | b' ' | 0x21..=0x7e | 0x80..=0xff) => (),
                    Some(c) => {
                        return Err(ParseError::InvalidQuotedString {
                            pos: i,
                            byte: Byte(c),
                        })
                    }
                    None => {
                        return Err(ParseError::MissingParameterQuote {
                            pos: i,
                        })
                    }
                }
            }
            // HTAB / SP /%x21 / %x23-5B / %x5D-7E / obs-text
            Some(
                b'\t' | b' ' | 0x21 | 0x23..=0x5b | 0x5d..=0x7e | 0x80..=0xff,
            ) => (),
            Some(c) => {
                return Err(ParseError::InvalidQuotedString {
                    pos: i,
                    byte: Byte(c),
                })
            }
            None => return Err(ParseError::MissingParameterQuote { pos: i }),
        }
        i += 1;
    }
}

/// Convert a `usize` to a `u16`.
///
/// # Panics
///
/// If the `usize` is larger than [`u16::MAX`].
#[inline]
const fn as_u16(i: usize) -> u16 {
    debug_assert!(i <= u16::MAX as usize, "as_u16 overflow");
    i as u16
}

/// Valid token characters are defined in [RFC7231 (HTTP)][RFC7231]:
///
/// > ```ABNF
/// > tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" / "." /
/// >    "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA
/// > ```
///
/// We make an exception for `'*'`. FIXME?
///
/// [RFC7231]: https://datatracker.ietf.org/doc/html/rfc7231#section-3.1.1.1
#[inline]
pub(crate) const fn is_valid_token_byte(c: u8) -> bool {
    matches!(
        c,
        b'!' | b'#' | b'$' | b'%' | b'&' | b'\'' | b'+' | b'-' | b'.' | b'^' |
        b'_' | b'`' | b'|' | b'~' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z',
    )
}

/// Is the passed byte valid in a token and not `b'+'`?
///
/// See [`is_valid_token_byte()`].
#[inline]
pub(crate) const fn is_valid_token_byte_not_plus(c: u8) -> bool {
    matches!(
        c,
        b'!' | b'#' | b'$' | b'%' | b'&' | b'\'' | b'-' | b'.' | b'^' |
        b'_' | b'`' | b'|' | b'~' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z',
    )
}

/// Get a byte from the input.
///
/// Returns `None` if `i` is past the end of `input`.
#[inline]
const fn get_byte(input: &[u8], i: usize) -> Option<u8> {
    if i < input.len() {
        Some(input[i])
    } else {
        None
    }
}

/// Consume valid token bytes and return first non-token byte.
///
/// Returns `None` if all the bytes until the end of `input` are token bytes,
/// otherwise returns the index (and content) of the first non-token byte.
const fn consume_token(input: &[u8], mut i: usize) -> Option<(usize, u8)> {
    while i < input.len() {
        if !is_valid_token_byte(input[i]) {
            return Some((i, input[i]));
        }
        i += 1;
    }
    None
}

/// Consume horizontal whitespace (`[ \t]`).
///
/// Returns `None` if all the bytes until the end of `input` are whitespace,
/// otherwise returns the index (and content) of the first non-whitespace byte.
const fn consume_whitespace(input: &[u8], mut i: usize) -> Option<(usize, u8)> {
    while i < input.len() {
        if !matches!(input[i], b' ' | b'\t') {
            return Some((i, input[i]));
        }
        i += 1;
    }
    None
}

/// An error encountered while parsing a media type.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ParseError {
    MissingType,
    MissingSlash,
    MissingSubtype,
    MissingParameter { pos: usize },
    MissingParameterEqual { pos: usize },
    MissingParameterValue { pos: usize },
    MissingParameterQuote { pos: usize },
    InvalidToken { pos: usize, byte: Byte },
    InvalidParameter { pos: usize, byte: Byte },
    InvalidQuotedString { pos: usize, byte: Byte },
    TrailingWhitespace,
    TooLong,
}

impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParseError::*;
        match self {
            MissingType => f.write_str("missing type before the slash (/)"),
            MissingSlash => f.write_str(
                "a slash (/) was missing between the type and subtype",
            ),
            MissingSubtype => {
                f.write_str("missing subtype after the slash (/)")
            }
            MissingParameter { pos } => {
                write!(
                    f,
                    "missing parameter after the semicolon (;) at position {}",
                    pos,
                )
            }
            MissingParameterEqual { pos } => {
                write!(
                    f,
                    "an equals sign (=) was missing between a parameter and \
                    its value at position {}",
                    pos,
                )
            }
            MissingParameterValue { pos } => {
                write!(
                    f,
                    "a value was missing in a parameter at position {}",
                    pos,
                )
            }
            MissingParameterQuote { pos } => {
                write!(
                    f,
                    "a quote (\") was missing from a parameter value at \
                    position {}",
                    pos,
                )
            }
            InvalidToken { pos, byte } => {
                write!(f, "invalid token, {:?} at position {}", byte, pos)
            }
            InvalidParameter { pos, byte } => {
                write!(f, "invalid parameter, {:?} at position {}", byte, pos)
            }
            InvalidQuotedString { pos, byte } => {
                write!(
                    f,
                    "invalid quoted-string in parameter value, {:?} at \
                    position {}",
                    byte, pos,
                )
            }
            TrailingWhitespace => {
                f.write_str("there is trailing whitespace at the end")
            }
            TooLong => f.write_str("the string is too long"),
        }
    }
}

/// A `Result` with a [`ParseError`] error type.
pub type Result<T, E = ParseError> = std::result::Result<T, E>;

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

#[cfg(test)]
mod tests {
    use super::*;

    /// Test a parsing with the passed parser.
    macro_rules! assert_parse {
        (
            $input:expr,
            $parser:expr,
            Ok(Mime {
                slash: $slash:expr,
                plus: $plus:expr,
                end: $end:expr,
                ..
            })
        ) => {
            assert_eq!(
                $parser.parse_const($input),
                Ok(Mime {
                    source: Source::Str($input),
                    slash: $slash,
                    plus: $plus,
                    end: $end,
                    parameters: Parameters::None,
                })
            );
        };
        (
            $input:expr,
            $parser:expr,
            Ok(Mime {
                slash: $slash:expr,
                plus: $plus:expr,
                end: $end:expr,
                parameters: $parameters:expr,
                ..
            })
        ) => {
            assert_eq!(
                $parser.parse_const($input),
                Ok(Mime {
                    source: Source::Str($input),
                    slash: $slash,
                    plus: $plus,
                    end: $end,
                    parameters: $parameters,
                })
            );
        };
        ($input:expr, $parser:expr, Err($error:expr)) => {
            assert_eq!($parser.parse_const($input), Err($error));
        };
    }

    /// Test parsing a media type (rather than a range).
    macro_rules! assert_type_parse {
        ($input:expr, $($expected:tt)+) => {
            assert_parse!($input, Parser::type_parser(), $($expected)+);
        };
    }

    /// Test parsing a media range.
    macro_rules! assert_range_parse {
        ($input:expr, $($expected:tt)+) => {
            assert_parse!($input, Parser::range_parser(), $($expected)+);
        };
    }

    /// Test both media and type parsers
    macro_rules! tests_both {
        ($($name:ident { $expected:literal == $($value:tt)+ })*) => {
            $(
                #[test]
                fn $name() {
                    assert_type_parse!($expected, $($value)+);
                    assert_range_parse!($expected, $($value)+);
                }
            )*
        };
    }

    /// Test only the media type parser (not the media range parser)
    macro_rules! tests_type {
        ($($name:ident { $expected:literal == $($value:tt)+ })*) => {
            $(
                #[test]
                fn $name() {
                    assert_type_parse!($expected, $($value)+);
                }
            )*
        };
    }

    /// Test only the media range parser
    macro_rules! tests_range {
        ($($name:ident { $expected:literal == $($value:tt)+ })*) => {
            $(
                #[test]
                fn $name() {
                    assert_range_parse!($expected, $($value)+);
                }
            )*
        };
    }

    use ParseError::*;

    // Tests against both media type and media range parsers.
    tests_both! {
        ok_type_subtype {
            "foo/bar" == Ok(Mime { slash: 3, plus: None, end: 7, .. })
        }
        ok_type_subtype_suffix {
            "foo/bar+hey" == Ok(Mime { slash: 3, plus: Some(7), end: 11, .. })
        }
        ok_multiple_plus {
            "foo/bar+a+b" == Ok(Mime { slash: 3, plus: Some(7), end: 11, .. })
        }
        ok_type_plus {
            "foo+c/bar+a+b" == Ok(Mime { slash: 5, plus: Some(9), end: 13, .. })
        }
        ok_subtype_first_plus {
            "foo/+a+b" == Ok(Mime { slash: 3, plus: Some(4), end: 8, .. })
        }
        ok_subtype_just_plus {
            "foo/+" == Ok(Mime { slash: 3, plus: Some(4), end: 5, .. })
        }
        err_empty {  "" == Err(MissingType) }
        err_no_slash { "abc" == Err(MissingSlash) }
        err_no_type { "/abc" == Err(MissingType) }
        err_bad_type {
            "a b/abc" == Err(InvalidToken { pos: 1, byte: Byte(b' ') })
        }
        err_no_subtype { "abc/" == Err(MissingSubtype) }
        err_just_slash {  "/" == Err(MissingType) }
        err_multiple_slash {
            "ab//c" == Err(InvalidToken { pos: 3, byte: Byte(b'/') })
        }
        err_multiple_separate_slash {
            "ab/c/d" == Err(InvalidToken { pos: 4, byte: Byte(b'/') })
        }
        err_subtype_range_suffix {
            "foo/*+a" == Err(InvalidToken { pos: 4, byte: Byte(b'*') })
        }
        err_trailing_spaces {
            "a/b   \t" == Err(TrailingWhitespace)
        }
        ok_one_parameter {
            "a/b; k=v" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 5,
                    equal: 6,
                    end: 8,
                    quoted: false,
                }),
                ..
            })
        }
        ok_two_parameters {
            "a/b; k=v;key=value" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::Two(
                    Parameter {
                        start: 5,
                        equal: 6,
                        end: 8,
                        quoted: false,
                    },
                    Parameter {
                        start: 9,
                        equal: 12,
                        end: 18,
                        quoted: false,
                    },
                ),
                ..
            })
        }
        ok_three_parameters {
            "a/b; k=v;key=value   ;3=3" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::Many,
                ..
            })
        }
        ok_four_parameters {
            "a/b; k=v;key=value   ;3=3 ; 4=4" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::Many,
                ..
            })
        }
        ok_one_parameter_many_spaces {
            "a/b   ;    k=v" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 11,
                    equal: 12,
                    end: 14,
                    quoted: false,
                }),
                ..
            })
        }
        ok_one_parameter_quoted {
            r#"a/b; k="v""# == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 5,
                    equal: 6,
                    end: 10,
                    quoted: true,
                }),
                ..
            })
        }
        ok_one_parameter_quoted_quote {
            r#"a/b; k="a\"b""# == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 5,
                    equal: 6,
                    end: 13,
                    quoted: true,
                }),
                ..
            })
        }
        ok_two_parameters_one_quoted {
            r#"a/b; k="v" ; a=b"# == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::Two(
                    Parameter {
                        start: 5,
                        equal: 6,
                        end: 10,
                        quoted: true,
                    },
                    Parameter {
                        start: 13,
                        equal: 14,
                        end: 16,
                        quoted: false,
                    },
                ),
                ..
            })
        }
        ok_parameter_empty_quoted {
            r#"a/b; k="""# == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 5,
                    equal: 6,
                    end: 9,
                    quoted: true,
                }),
                ..
            })
        }
        ok_parameter_quoted_tab {
            "a/b; k=\"\t\"" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 5,
                    equal: 6,
                    end: 10,
                    quoted: true,
                }),
                ..
            })
        }
        err_space_in_parameter_key {
            "a/b; k =v" == Err(InvalidParameter { pos: 6, byte: Byte(b' ') })
        }
        err_space_after_parameter {
            "a/b; k=v " == Err(TrailingWhitespace)
        }
        err_missing_parameter_key {
            "a/b; =v" == Err(InvalidParameter { pos: 5, byte: Byte(b'=') })
        }
        err_parameter_double_equal {
            "a/b; k==v" == Err(InvalidParameter { pos: 7, byte: Byte(b'=') })
        }
        err_missing_parameter {
            "a/b;; k=v" == Err(MissingParameter { pos: 4 })
        }
        err_parameter_start_quoted {
            r#"a/b; k="a"# == Err(MissingParameterQuote { pos: 9 })
        }
        err_parameter_quoted_invalid_char {
            "a/b; k=\"\n\"" == Err(InvalidQuotedString {
                pos: 8,
                byte: Byte(b'\n'),
            })
        }
        err_parameter_quoted_char_after_end {
            "a/b; k=\"a\"b" == Err(InvalidParameter {
                pos: 10,
                byte: Byte(b'b'),
            })
        }
        err_foo_slash_star_star {
            "foo/**" == Err(InvalidToken { pos: 4, byte: Byte(b'*') })
        }
        err_foo_slash_star_a {
            "foo/*a" == Err(InvalidToken { pos: 4, byte: Byte(b'*') })
        }
        err_star_slash_foo {
            "*/foo" == Err(InvalidToken { pos: 0, byte: Byte(b'*') })
        }
        err_star_a_slash_star {
            "*a/*" == Err(InvalidToken { pos: 0, byte: Byte(b'*') })
        }
        err_star_slash_a_star {
            "*/*a" == Err(InvalidToken { pos: 0, byte: Byte(b'*') })
        }
        err_star_slash_a_star_one_parameter {
            "*/*a; k=v" == Err(InvalidToken { pos: 0, byte: Byte(b'*') })
        }
    }

    // Tests against only the media type parser.
    tests_type! {
        type_parse_err_everything_range {
            "*/*" == Err(InvalidToken { pos: 0, byte: Byte(b'*') })
        }
        type_parse_err_subtype_range {
            "foo/*" == Err(InvalidToken { pos: 4, byte: Byte(b'*') })
        }
    }

    // Tests against only the media range parser.
    tests_range! {
        range_parse_ok_everything_range {
            "*/*" == Ok(Mime { slash: 1, plus: None, end: 3, .. })
        }
        range_parse_ok_subtype_range {
            "foo/*" == Ok(Mime { slash: 3, plus: None, end: 5, .. })
        }
        range_parse_ok_everything_range_one_parameter {
            "*/*; k=v" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 5,
                    equal: 6,
                    end: 8,
                    quoted: false,
                }),
                ..
            })
        }
        range_parse_ok_subtype_range_one_parameter {
            "a/*; k=v" == Ok(Mime {
                slash: 1,
                plus: None,
                end: 3,
                parameters: Parameters::One(Parameter {
                    start: 5,
                    equal: 6,
                    end: 8,
                    quoted: false,
                }),
                ..
            })
        }
    }
}
