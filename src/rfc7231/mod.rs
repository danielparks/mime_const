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

mod errors;
mod quoted_string;
mod tests_parse;

pub use errors::*;
pub use quoted_string::*;

use crate::bytefilter::ByteFilter;
use crate::const_utils::get_byte;
use std::borrow::Cow;

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

/// Parser for media types.
#[derive(Clone, Debug)]
pub(crate) struct Parser {
    pub accept_media_range: bool,
}

#[derive(Debug, PartialEq)]
pub(crate) struct ConstMime<'a> {
    pub(crate) source: &'a str,
    pub(crate) slash: usize,
    pub(crate) plus: Option<usize>,
    pub(crate) end: usize,
    pub(crate) parameters: ConstParameters,
}

/// Parameters in a MIME type.
///
/// This can only store the parse information for two parameters because an
/// arbitrary number of parameters would require a `Vec` and we can’t fill a
/// `Vec` in a `const fn`.
///
/// Instead, we validate the parameters and re-parse when need to access them.
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum ConstParameters {
    None,
    One(ConstParameter),
    Two(ConstParameter, ConstParameter),
    /// More than two.
    Many,
}

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
///
/// This only contains indices, so it’s useless without the [`ConstMime`].
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct ConstParameter {
    /// The index of the start of the parameter name.
    pub(crate) start: usize,

    /// The index of the `'='`. The start of the value is `equal + 1`.
    pub(crate) equal: usize,

    /// The index just past the last character in the value.
    pub(crate) end: usize,

    /// Whether or not the value is a quoted string.
    pub(crate) quoted: bool,
}

impl ConstParameter {
    pub(crate) fn name<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start..self.equal]
    }

    pub(crate) fn value<'a>(&self, src: &'a str) -> Cow<'a, str> {
        if self.quoted {
            // Strip quotes.
            unquote_string(&src[self.equal + 2..self.end - 1])
        } else {
            Cow::from(&src[self.equal + 1..self.end])
        }
    }

    pub(crate) fn tuple<'a>(&self, src: &'a str) -> (&'a str, Cow<'a, str>) {
        (self.name(src), self.value(src))
    }
}

// FIXME how do we deal with case?

impl Parser {
    /// Create a `Parser` that can parse media ranges, e.g. `text/*`.
    #[inline]
    #[allow(dead_code)]
    pub(crate) const fn range_parser() -> Self {
        Parser { accept_media_range: true }
    }

    /// Create a `Parser` that parses media types.
    ///
    /// It will reject media ranges, e.g. `text/*`.
    #[inline]
    pub(crate) const fn type_parser() -> Self {
        Parser { accept_media_range: false }
    }

    /// Actually do the parsing.
    pub(crate) const fn parse_const<'a>(
        &self,
        source: &'a str,
        max_len: usize,
    ) -> Result<ConstMime<'a>> {
        let bytes = source.as_bytes();
        if bytes.len() > max_len {
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
            [c, ..] if TOKEN_FILTER.match_byte(*c) => {
                let slash = try_!(self.consume_type(bytes));
                let (i, plus) = try_!(self.consume_subtype(bytes, slash));
                (i, slash, plus)
            }
            [c, ..] => {
                return Err(ParseError::InvalidToken { pos: 0, byte: *c });
            }
        };

        let end = i;

        let parameters = try_!(parse_parameters(bytes, end));
        Ok(ConstMime { source, slash, plus, end, parameters })
    }

    /// Validate the type and return the index of the slash.
    const fn consume_type(&self, bytes: &[u8]) -> Result<usize> {
        // Validate rest of type token and find '/'.
        match consume_token(bytes, 1) {
            Some((i, b'/')) => Ok(i),
            Some((i, c)) => Err(ParseError::InvalidToken { pos: i, byte: c }),
            None => Err(ParseError::MissingSlash),
        }
    }

    /// Validate the subtype and return the index after the last character.
    const fn consume_subtype(
        &self,
        bytes: &[u8],
        start: usize,
    ) -> Result<(usize, Option<usize>)> {
        // Validate first byte of subtype token.
        let mut i = start + 1;
        let mut plus = None;
        match get_byte(bytes, i) {
            None | Some(b';' | b' ' | b'\t') => {
                return Err(ParseError::MissingSubtype)
            }
            Some(b'+') => {
                plus = Some(i);
            }
            Some(b'*') if self.accept_media_range => {
                // * subtype; check next byte to make sure it’s either the end
                // of the input or the end of the subtype.
                return match get_byte(bytes, i + 1) {
                    None | Some(b';' | b' ' | b'\t') => Ok((i + 1, plus)),
                    Some(_) => {
                        // subtype starts with *, which is invalid
                        Err(ParseError::InvalidToken { pos: i, byte: b'*' })
                    }
                };
            }
            Some(c) if TOKEN_FILTER.match_byte(c) => (),
            Some(c) => {
                return Err(ParseError::InvalidToken { pos: i, byte: c })
            }
        }

        // Validate rest of subtype token and find either space or ';'.
        loop {
            i += 1;
            #[allow(clippy::redundant_pattern_matching)] // is_none() not const
            match get_byte(bytes, i) {
                None | Some(b';' | b' ' | b'\t') => return Ok((i, plus)),
                Some(b'+') if matches!(plus, None) => {
                    plus = Some(i);
                }
                Some(c) if TOKEN_FILTER.match_byte(c) => (),
                Some(c) => {
                    return Err(ParseError::InvalidToken { pos: i, byte: c })
                }
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
) -> Result<ConstParameters> {
    let one = match try_!(parse_parameter(bytes, start)) {
        None => return Ok(ConstParameters::None),
        Some(one) => one,
    };

    let two = match try_!(parse_parameter(bytes, one.end as usize)) {
        None => return Ok(ConstParameters::One(one)),
        Some(two) => two,
    };

    let mut i = match try_!(parse_parameter(bytes, two.end as usize)) {
        None => return Ok(ConstParameters::Two(one, two)),
        Some(ConstParameter { end, .. }) => end,
    };

    // More than two parameters. Parse the remaining parameters to validate
    // them, but drop the results because we can’t store them.
    loop {
        i = match try_!(parse_parameter(bytes, i)) {
            None => return Ok(ConstParameters::Many),
            Some(ConstParameter { end, .. }) => end,
        }
    }
}

/// Parse a parameter out of `bytes` starting at `start`.
///
/// First this consumes the separator (`[ \t]*;[ \t]`), then it passes off
/// the actual key=value parsing to [`parse_parameter_key_value()`].
pub(crate) const fn parse_parameter(
    bytes: &[u8],
    start: usize,
) -> Result<Option<ConstParameter>> {
    match consume_whitespace(bytes, start) {
        None if start < bytes.len() => Err(ParseError::TrailingWhitespace),
        None => Ok(None),
        Some((semicolon, b';')) => {
            match consume_whitespace(bytes, semicolon + 1) {
                None => Err(ParseError::MissingParameter { pos: semicolon }),
                Some((start, _)) => parse_parameter_key_value(bytes, start),
            }
        }
        Some((i, c)) => Err(ParseError::InvalidParameter { pos: i, byte: c }),
    }
}

/// Parse a parameter key=value out of `bytes` starting at `start`.
const fn parse_parameter_key_value(
    bytes: &[u8],
    start: usize,
) -> Result<Option<ConstParameter>> {
    match consume_token(bytes, start) {
        Some((i, b';')) if i == start => {
            Err(ParseError::MissingParameter { pos: i })
        }
        Some((i, c)) if i == start => {
            Err(ParseError::InvalidParameter { pos: i, byte: c })
        }
        Some((equal, b'=')) => {
            let end = match consume_token(bytes, equal + 1) {
                Some((i, b'"')) if i == equal + 1 => {
                    let end = try_!(parse_quoted_string(bytes, i));
                    return Ok(Some(ConstParameter {
                        start,
                        equal,
                        end,
                        quoted: true,
                    }));
                }
                Some((i, b';' | b' ' | b'\t')) => i,
                Some((i, c)) => {
                    return Err(ParseError::InvalidParameter {
                        pos: i,
                        byte: c,
                    })
                }
                None => bytes.len(),
            };

            if end <= equal + 1 {
                Err(ParseError::MissingParameterValue { pos: end })
            } else {
                Ok(Some(ConstParameter { start, equal, end, quoted: false }))
            }
        }
        Some((i, c)) => Err(ParseError::InvalidParameter { pos: i, byte: c }),
        None => Err(ParseError::MissingParameterEqual { pos: start }),
    }
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
pub const TOKEN_FILTER: ByteFilter =
    ByteFilter::from_bytes(b"-!#$%&'+.^_`|~0-9a-zA-Z");

/// Consume valid token bytes and return first non-token byte.
///
/// Returns `None` if all the bytes until the end of `input` are token bytes,
/// otherwise returns the index (and content) of the first non-token byte.
const fn consume_token(input: &[u8], mut i: usize) -> Option<(usize, u8)> {
    while i < input.len() {
        if !TOKEN_FILTER.match_byte(input[i]) {
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
