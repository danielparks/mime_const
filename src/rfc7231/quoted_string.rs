//! Deal with quoted strings
//!
//! Defined in [RFC7230 (HTTP) §3.2.6].
//!
//! [RFC7230 (HTTP) §3.2.6]: https://datatracker.ietf.org/doc/html/rfc7230#section-3.2.6

use crate::bytefilter::ByteFilter;
use crate::const_utils::get_byte;
use crate::rfc7231::{ParseError, Result};
use std::borrow::Cow;

/// `qdtext`
///
/// ```ABNF
/// qdtext         = HTAB / SP /%x21 / %x23-5B / %x5D-7E / obs-text
/// obs-text       = %x80-FF
/// ```
const QDTEXT_FILTER: ByteFilter = ByteFilter::from_bytes(b"\t \x21")
    .with_inclusive_range(0x23..=0x5b)
    .with_inclusive_range(0x5d..=0x7e)
    .with_inclusive_range(0x80..=0xff);

/// 2nd octet of `quoted-pair`
///
/// ```ABNF
/// quoted-pair    = "\" ( HTAB / SP / VCHAR / obs-text )
/// obs-text       = %x80-FF
/// ```
const QUOTED_PAIR_FILTER: ByteFilter = ByteFilter::from_bytes(b"\t ")
    .with_inclusive_range(0x21..=0x7e)
    .with_inclusive_range(0x80..=0xff);

/// # Parse `quoted-string`.
///
/// `input[0]` must be `b'"'`.
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
pub(crate) const fn parse_quoted_string(
    input: &[u8],
    mut i: usize,
) -> Result<usize> {
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
                    Some(c) => {
                        if !QUOTED_PAIR_FILTER.match_byte(c) {
                            return Err(ParseError::InvalidQuotedString {
                                pos: i,
                                byte: c,
                            });
                        }
                    }
                    None => {
                        return Err(ParseError::MissingParameterQuote {
                            pos: i,
                        })
                    }
                }
            }
            Some(c) => {
                if !QDTEXT_FILTER.match_byte(c) {
                    return Err(ParseError::InvalidQuotedString {
                        pos: i,
                        byte: c,
                    });
                }
            }
            None => return Err(ParseError::MissingParameterQuote { pos: i }),
        }
        i += 1;
    }
}

/// Unquote a quoted string (without the quotes).
///
/// This does not validate that the quoted string is otherwise valid.
///
/// In the [RFC7230 (HTTP) §3.2.6] definition of `quoted-string`:
///
/// > The backslash octet ("\") can be used as a single-octet quoting
/// > mechanism within quoted-string and comment constructs.  Recipients
/// > that process the value of a quoted-string MUST handle a quoted-pair
/// > as if it were **replaced by the octet following the backslash.**
///
/// My emphasis. In other words, in a quoted string `"\n"` unquotes to `"n"`.
/// The only uses for the backslash escape are quotes and backslashes.
///
/// [RFC7230 (HTTP) §3.2.6]: https://datatracker.ietf.org/doc/html/rfc7230#section-3.2.6
#[must_use]
pub fn unquote_string(input: &str) -> Cow<'_, str> {
    if let Some(i) = input.find('\\') {
        // FIXME? This will probably over-allocate a bit.
        let mut output = String::with_capacity(input.len() - 1);
        output.push_str(&input[..i]);

        let mut input = &input[i + 1..];
        // Use as_bytes() here so that we don’t slice through a char.
        while let Some(i) =
            input.as_bytes()[1..].iter().position(|b| *b == b'\\')
        {
            // We pass the byte immediately after the backlash through
            // regardless, so we start searching for the next backslash after
            // it. This means that i is relative to the first byte, rather than
            // the zeroth. Fix it:
            let i = i + 1;

            // input.len() should never be < 1, because the input should
            // never end with a single backslash. If it does, panic.
            output.push_str(&input[..i]);
            input = &input[i + 1..];
        }

        output.push_str(input);
        Cow::from(output)
    } else {
        Cow::from(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::assert;

    #[test]
    fn unquote_string_boring() {
        assert!(unquote_string("") == "");
        assert!(unquote_string("abc") == "abc");
    }

    #[test]
    fn unquote_string_backslash_n() {
        assert!(unquote_string(r"\n") == "n");
    }

    #[test]
    fn unquote_string_backslash_quote() {
        assert!(unquote_string(r#"a\"b"#) == r#"a"b"#);
    }

    #[test]
    fn unquote_string_backslash_backslash() {
        assert!(unquote_string(r"a\\b") == r"a\b");
    }

    #[test]
    fn unquote_string_complicated() {
        assert!(unquote_string(r#"\\\\\"a\\"#) == r#"\\"a\"#);
    }

    #[test]
    fn unquote_string_unicode() {
        assert!(unquote_string(r"\🙂") == r"🙂");
    }

    #[test]
    fn parse_quoted_string_boring() {
        assert!(parse_quoted_string(br#""""#, 0) == Ok(2));
        assert!(parse_quoted_string(br#""abc""#, 0) == Ok(5));
    }

    #[test]
    fn parse_quoted_string_backslash_n() {
        assert!(parse_quoted_string(br#""\n""#, 0) == Ok(4));
    }

    #[test]
    fn parse_quoted_string_backslash_quote() {
        assert!(parse_quoted_string(br#""a\"b""#, 0) == Ok(6));
    }

    #[test]
    fn parse_quoted_string_backslash_backslash() {
        assert!(parse_quoted_string(br#""a\\b""#, 0) == Ok(6));
    }

    #[test]
    fn parse_quoted_string_complicated() {
        assert!(parse_quoted_string(br#""\\\\\"a\\""#, 0) == Ok(11));
    }

    #[test]
    fn parse_quoted_string_unicode() {
        assert!(parse_quoted_string(r#""\🙂""#.as_bytes(), 0) == Ok(7));
    }
}
