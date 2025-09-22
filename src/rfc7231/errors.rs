//! Errors for RFC7231 parsing

use std::fmt;

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
    InvalidToken { pos: usize, byte: u8 },
    InvalidParameter { pos: usize, byte: u8 },
    InvalidQuotedString { pos: usize, byte: u8 },
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
                write!(
                    f,
                    "invalid token, {:?} at position {}",
                    Byte(*byte),
                    pos
                )
            }
            InvalidParameter { pos, byte } => {
                write!(
                    f,
                    "invalid parameter, {:?} at position {}",
                    Byte(*byte),
                    pos
                )
            }
            InvalidQuotedString { pos, byte } => {
                write!(
                    f,
                    "invalid quoted-string in parameter value, {:?} at \
                    position {}",
                    Byte(*byte),
                    pos,
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

    #[test]
    fn byte_a() {
        assert_eq!(format!("{:?}", Byte(b'a')), "'a'".to_string());
    }

    #[test]
    fn byte_0() {
        assert_eq!(format!("{:?}", Byte(0)), "'\\0'".to_string());
    }
}
