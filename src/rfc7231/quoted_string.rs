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
            Some(c) => {
                if QDTEXT_FILTER.match_byte(c) {
                    // Looks good; continue.
                } else if c == b'"' {
                    // End of the quoted-string.
                    // input[i] existed, so i + 1 <= input.len()
                    return Ok(i + 1);
                } else if c == b'\\' {
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
                } else {
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

/// Quote a string for use as a parameter value if necessary.
///
/// Returns the input string if it contains only token characters, otherwise
/// returns a quoted and escaped version.
///
/// # Valid Characters
///
/// Input must contain only characters valid in quoted strings (per [RFC7230
/// (HTTP) §3.2.6] `quoted-pair`):
///   - `'\t'`
///   - `' '`
///   - `'!'..='~'` (printable ASCII characters)
///   - `\x80`..`\xFF` (high bit characters)
///
/// Other characters, e.g. '\n' and '\r', will cause this function to return
/// `Err(ParseError::InvalidQuotedString { .. })`.
///
/// # Examples
///
/// ```
/// use mime_const::rfc7231::quote_string;
/// use std::borrow::Cow;
///
/// assert_eq!(quote_string("utf-8").unwrap(), Cow::Borrowed("utf-8"));
/// assert_eq!(
///     quote_string("hello world"),
///     Ok(Cow::Borrowed("\"hello world\"")),
/// );
/// assert_eq!(
///     quote_string(r#"say "hi""#),
///     Ok(Cow::Borrowed(r#""say \"hi\"""#)),
/// );
///
/// // Invalid: control characters
/// assert!(quote_string("hello\nworld").is_err());
/// ```
///
/// # Errors
///
/// Returns [`ParseError::InvalidQuotedString`] if the input contains control
/// characters other than tab.
///
/// [RFC7230 (HTTP) §3.2.6]: https://datatracker.ietf.org/doc/html/rfc7230#section-3.2.6
pub fn quote_string(input: &str) -> Result<Cow<'_, str>> {
    use crate::rfc7231::TOKEN_FILTER;

    // Single pass: validate and check what we need to do
    let mut needs_quoting = input.is_empty();
    let mut needs_escaping = false;

    for (i, &byte) in input.as_bytes().iter().enumerate() {
        // Validate: byte must be in QUOTED_PAIR_FILTER
        if !QUOTED_PAIR_FILTER.match_byte(byte) {
            return Err(ParseError::InvalidQuotedString { pos: i, byte });
        }

        // Check if quoting is needed (non-token characters)
        if !TOKEN_FILTER.match_byte(byte) {
            needs_quoting = true;
        }

        // Check if escaping is needed (quotes or backslashes)
        if byte == b'"' || byte == b'\\' {
            needs_escaping = true;
        }
    }

    // No quoting needed - return as-is
    if !needs_quoting {
        return Ok(Cow::Borrowed(input));
    }

    // Quoting needed but no escaping - just wrap in quotes
    if !needs_escaping {
        return Ok(Cow::Owned(format!("\"{}\"", input)));
    }

    // Need to escape quotes and backslashes
    let mut output = String::with_capacity(input.len() + 10);
    output.push('"');

    for ch in input.chars() {
        if ch == '"' || ch == '\\' {
            output.push('\\');
        }
        output.push(ch);
    }

    output.push('"');
    Ok(Cow::Owned(output))
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
    use crate::rfc7231::parse_parameter_value;
    use assert2::{assert, let_assert};

    #[test]
    fn quote_string_no_quoting_needed() {
        // Simple tokens don't need quoting
        assert!(quote_string("utf-8") == Ok(Cow::Borrowed("utf-8")));
        assert!(quote_string("text") == Ok(Cow::Borrowed("text")));
        assert!(quote_string("abc123") == Ok(Cow::Borrowed("abc123")));
        assert!(quote_string("foo-bar") == Ok(Cow::Borrowed("foo-bar")));
        assert!(quote_string("a.b.c") == Ok(Cow::Borrowed("a.b.c")));
    }

    #[test]
    fn quote_string_empty() {
        // Empty string needs quoting
        assert!(quote_string("") == Ok(Cow::Owned("\"\"".to_string())));
    }

    #[test]
    fn quote_string_with_spaces() {
        assert!(
            quote_string("hello world")
                == Ok(Cow::Owned("\"hello world\"".to_string()))
        );
        assert!(quote_string(" ") == Ok(Cow::Owned("\" \"".to_string())));
        assert!(
            quote_string("a b c") == Ok(Cow::Owned("\"a b c\"".to_string()))
        );
    }

    #[test]
    fn quote_string_with_special_chars() {
        assert!(quote_string("a;b") == Ok(Cow::Owned("\"a;b\"".to_string())));
        assert!(quote_string("a=b") == Ok(Cow::Owned("\"a=b\"".to_string())));
        assert!(quote_string("a,b") == Ok(Cow::Owned("\"a,b\"".to_string())));
        assert!(quote_string("a/b") == Ok(Cow::Owned("\"a/b\"".to_string())));
    }

    #[test]
    fn quote_string_with_quotes() {
        assert!(
            quote_string(r#"say "hi""#)
                == Ok(Cow::Owned(r#""say \"hi\"""#.to_string()))
        );
        assert!(quote_string(r#"""#) == Ok(Cow::Owned(r#""\"""#.to_string())));
        assert!(
            quote_string(r#"a"b"c"#)
                == Ok(Cow::Owned(r#""a\"b\"c""#.to_string()))
        );
    }

    #[test]
    fn quote_string_with_backslashes() {
        assert!(
            quote_string(r"a\b") == Ok(Cow::Owned(r#""a\\b""#.to_string()))
        );
        assert!(quote_string(r"\") == Ok(Cow::Owned(r#""\\""#.to_string())));
        assert!(quote_string(r"\\") == Ok(Cow::Owned(r#""\\\\""#.to_string())));
    }

    #[test]
    fn quote_string_with_both() {
        assert!(
            quote_string(r#"a\"b"#)
                == Ok(Cow::Owned(r#""a\\\"b""#.to_string()))
        );
        assert!(
            quote_string(r#"\""#) == Ok(Cow::Owned(r#""\\\"""#.to_string()))
        );
    }

    #[test]
    fn quote_string_unicode() {
        // Unicode is allowed in quoted strings
        assert!(quote_string("🙂") == Ok(Cow::Owned("\"🙂\"".to_string())));
        assert!(
            quote_string("hello 🙂")
                == Ok(Cow::Owned("\"hello 🙂\"".to_string()))
        );
    }

    /// Quote a string, validate it, and check that it unquotes correctly.
    fn quote_validate_and_unquote(input: &str) {
        let quoted = quote_string(input).unwrap();

        let_assert!(
            Ok((end, is_quoted)) = parse_parameter_value(quoted.as_bytes(), 0),
            "Invalid quoted string ({:?}) for input {:?}",
            quoted,
            input,
        );
        assert!(
            end == quoted.len(),
            "Invalid quoted string ({:?}) for input {:?}",
            quoted,
            input,
        );

        // Verify round-trip
        if is_quoted {
            // Remove quotes and unescape
            let unquoted = unquote_string(&quoted[1..quoted.len() - 1]);
            assert!(
                unquoted == input,
                "Unquoted value doesn't match input (quoted={:?})",
                quoted,
            );
        } else {
            // Should be unchanged
            assert!(quoted == input, "Unquoted value doesn't match input");
        }
    }

    #[test]
    fn quote_string_validates_and_roundtrips() {
        for input in [
            "utf-8",
            "hello world",
            r#"say "hi""#,
            r"a\b",
            r#"a\"b"#,
            "",
            "🙂",
            "a;b",
            "a=b",
            "a,b",
            "a/b",
            "a b c",
            r"\\",
            r#"""#,
            "a\tb",
        ] {
            quote_validate_and_unquote(input);
        }
    }

    #[test]
    fn quote_string_1024_chars_after_space() {
        let end = char::from_u32(b' ' as u32 + 1024).unwrap();
        for c in ' '..end {
            if c != '\x7f' {
                // Only invalid char in this range
                quote_validate_and_unquote(&c.to_string());
            }
        }
    }

    #[test]
    fn quote_string_all_ascii_bytes() {
        // Bytes 128 and above are invalid in UTF-8.
        for byte in 0u8..128 {
            let input = &[byte][..];
            let input = str::from_utf8(input).expect("valid utf-8");

            // Valid b'\t', 0x20-0x7E (printable ASCII), 0x80-0xFF (obs-text)
            let is_valid =
                byte == b'\t' || (0x20..=0x7E).contains(&byte) || byte >= 0x80;

            if is_valid {
                // Should succeed
                let_assert!(
                    Ok(quoted) = quote_string(input),
                    "Expected quote_string() to succeed for valid byte {:?}",
                    byte as char,
                );

                assert!(
                    parse_parameter_value(quoted.as_bytes(), 0)
                        == Ok((quoted.len(), quoted.starts_with('"'))),
                    "Invalid quoted string ({:?}) for valid byte {:?}",
                    quoted,
                    byte,
                );
            } else {
                // Should fail (control characters other than tab)
                assert!(
                    let Err(_) = quote_string(input),
                    "Expected quote_string() to reject invalid byte {:02x}",
                    byte,
                );
            }
        }
    }

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
