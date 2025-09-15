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

        let i = try_!(self.consume_type(bytes));
        let slash = as_u16(i);
        let (i, plus) = try_!(self.consume_subtype(bytes, i));

        if i >= bytes.len() {
            return Ok(Mime {
                source,
                slash,
                plus,
                parameters: Parameters::None,
            });
        }

        let parameters = try_!(Self::parse_parameters(bytes, i));
        Ok(Mime { source, slash, plus, parameters })
    }

    /// Validate the type and return the index of the slash.
    const fn consume_type(&self, bytes: &[u8]) -> Result<usize> {
        // Validate first byte of type token.
        match bytes {
            [] => {
                // FIXME? empty
                return Err(ParseError::MissingSlash);
            }
            [b'*', b'/', ..] if self.accept_media_range => {
                return Ok(1);
            }
            [b'/', ..] => {
                return Err(ParseError::MissingType);
            }
            // FIXME what about starting with +?
            [c, ..] if is_valid_token_byte(*c) => (),
            [c, ..] => {
                return Err(ParseError::InvalidToken {
                    pos: 0,
                    byte: Byte(*c),
                });
            }
        }

        // Validate rest of type token and find '/'.
        match find_non_token_byte(bytes, 1) {
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
                // FIXME? allow start with +?
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

    /// Parse parameters from `bytes` starting at `start`.
    ///
    /// Parameters look like `; key=value; key2=value2`.
    const fn parse_parameters(
        bytes: &[u8],
        start: usize,
    ) -> Result<Parameters> {
        let one = match try_!(Self::parse_parameter(bytes, start)) {
            None => return Ok(Parameters::None),
            Some(one) => one,
        };

        let two = match try_!(Self::parse_parameter(bytes, one.end as usize)) {
            None => return Ok(Parameters::One(one)),
            Some(two) => two,
        };

        let mut i = match try_!(Self::parse_parameter(bytes, two.end as usize))
        {
            None => return Ok(Parameters::Two(one, two)),
            Some(Parameter { end, .. }) => end as usize,
        };

        // More than two parameters. Parse the remaining parameters to validate
        // them, but drop the results because we can’t store them.
        loop {
            i = match try_!(Self::parse_parameter(bytes, i)) {
                None => return Ok(Parameters::Many),
                Some(Parameter { end, .. }) => end as usize,
            }
        }
    }

    /// Parse a parameter out of `bytes` starting at `start`.
    ///
    /// First this consumes the separator (`[ \t]*;[ \t]`), then it passes off
    /// the actual key=value parsing to [`Self::parse_parameter_key_value()`].
    const fn parse_parameter(
        bytes: &[u8],
        start: usize,
    ) -> Result<Option<Parameter>> {
        match find_non_whitespace_byte(bytes, start) {
            None if start < bytes.len() => Err(ParseError::TrailingWhitespace),
            None => Ok(None),
            Some((semicolon, b';')) => {
                match find_non_whitespace_byte(bytes, semicolon + 1) {
                    None => {
                        Err(ParseError::MissingParameter { pos: semicolon })
                    }
                    Some((start, _)) => {
                        Self::parse_parameter_key_value(bytes, start)
                    }
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
        match find_non_token_byte(bytes, start) {
            Some((i, b';')) if i == start => {
                Err(ParseError::MissingParameter { pos: i })
            }
            Some((i, c)) if i == start => {
                Err(ParseError::InvalidParameter { pos: i, byte: Byte(c) })
            }
            Some((equal, b'=')) => {
                let end = match find_non_token_byte(bytes, equal + 1) {
                    Some((i, b'"')) if i == equal + 1 => {
                        // FIXME support quotes
                        panic!("unimplemented");
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
                    // FIXME? is an empty value legal?
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
}

// FIXME should implement Eq, PartialEq, Ord, and PartialOrd manually
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mime<'a> {
    source: Source<'a>,
    slash: u16,
    plus: Option<u16>,
    parameters: Parameters,
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

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
///
/// This only contains indices, so it’s useless without the [`Mime`] struct and
/// its [`Source`];
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Parameter {
    /// The index of the start of the parameter name.
    start: u16,

    /// The index of the `'='`. The start of the value is `equal + 1`.
    equal: u16,

    /// The index just past the last character in the value.
    end: u16,

    /// Whether or not the value is a quoted string.
    quoted: bool,
}

/// Parameters in a MIME type.
///
/// This can only store the parse information for two parameters because an
/// arbitrary number of parameters would require a `Vec` and we can’t fill a
/// `Vec` in a `const fn`.
///
/// Instead, we validate the parameters and re-parse when need to access them.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Parameters {
    None,
    One(Parameter),
    Two(Parameter, Parameter),
    /// More than two.
    Many,
}

/// An error encountered while parsing a media type.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ParseError {
    MissingType,
    MissingSlash,
    MissingSubtype,
    MissingParameter { pos: usize },
    MissingParameterEqual { pos: usize },
    MissingParameterValue { pos: usize }, // FIXME? correct?
    MissingParameterQuote { pos: usize },
    InvalidToken { pos: usize, byte: Byte },
    InvalidRange,
    InvalidParameter { pos: usize, byte: Byte },
    TrailingWhitespace,
    TooLong,
}

impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::MissingType => {
                f.write_str("missing type before the slash (/)")
            }
            ParseError::MissingSlash => f.write_str(
                "a slash (/) was missing between the type and subtype",
            ),
            ParseError::MissingSubtype => {
                f.write_str("missing subtype after the slash (/)")
            }
            ParseError::MissingParameter { pos } => {
                write!(
                    f,
                    "missing parameter after the semicolon (;) at position {}",
                    pos
                )
            }
            ParseError::MissingParameterEqual { pos } => {
                write!(
                    f,
                    "an equals sign (=) was missing between a parameter and \
                    its value at position {}",
                    pos
                )
            }
            ParseError::MissingParameterValue { pos } => {
                write!(
                    f,
                    "a value was missing in a parameter at position {}",
                    pos
                )
            }
            ParseError::MissingParameterQuote { pos } => {
                write!(
                    f,
                    "a quote (\") was missing from a parameter value at \
                    position {}",
                    pos
                )
            }
            ParseError::InvalidToken { pos, byte } => {
                write!(f, "invalid token, {:?} at position {}", byte, pos)
            }
            ParseError::InvalidRange => f.write_str("unexpected asterisk"),
            ParseError::InvalidParameter { pos, byte } => {
                write!(f, "invalid parameter, {:?} at position {}", byte, pos)
            }
            ParseError::TrailingWhitespace => {
                f.write_str("there is trailing whitespace at the end")
            }
            ParseError::TooLong => f.write_str("the string is too long"),
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
const fn is_valid_token_byte(c: u8) -> bool {
    matches!(
        c,
        b'!' | b'#' | b'$' | b'%' | b'&' | b'\'' | b'+' | b'-' | b'.' | b'^' |
        b'_' | b'`' | b'|' | b'~' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z',
    )
}

#[inline]
const fn get_byte(input: &[u8], i: usize) -> Option<u8> {
    if i < input.len() {
        Some(input[i])
    } else {
        None
    }
}

const fn find_non_token_byte(
    input: &[u8],
    start: usize,
) -> Option<(usize, u8)> {
    let mut i = start;
    while i < input.len() {
        if !is_valid_token_byte(input[i]) {
            return Some((i, input[i]));
        }
        i += 1;
    }
    None
}

const fn find_non_whitespace_byte(
    input: &[u8],
    start: usize,
) -> Option<(usize, u8)> {
    let mut i = start;
    while i < input.len() {
        if !matches!(input[i], b' ' | b'\t') {
            return Some((i, input[i]));
        }
        i += 1;
    }
    None
}

#[allow(dead_code)]
const fn is_restricted_quoted_char(c: u8) -> bool {
    c == 9 || (c > 31 && c != 127)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test a parsing with the passed parser.
    macro_rules! assert_parse {
        (
            $input:expr,
            $parser:expr,
            Ok(Mime { slash: $slash:expr, plus: $plus:expr, .. })
        ) => {
            assert_eq!(
                $parser.parse_const($input),
                Ok(Mime {
                    source: Source::Str($input),
                    slash: $slash,
                    plus: $plus,
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
                parameters: Parameters::Many,
                ..
            })
        }
        ok_four_parameters {
            "a/b; k=v;key=value   ;3=3 ; 4=4" == Ok(Mime {
                slash: 1,
                plus: None,
                parameters: Parameters::Many,
                ..
            })
        }
        ok_one_parameter_many_spaces {
            "a/b   ;    k=v" == Ok(Mime {
                slash: 1,
                plus: None,
                parameters: Parameters::One(Parameter {
                    start: 11,
                    equal: 12,
                    end: 14,
                    quoted: false,
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
            "*/*" == Ok(Mime { slash: 1, plus: None, .. })
        }
        range_parse_ok_subtype_range {
            "foo/*" == Ok(Mime { slash: 3, plus: None, .. })
        }
    }
}
