//! Test parsing.
#![cfg(test)]

use super::*;

/// Test a parsing with the passed parser.
macro_rules! assert_parse {
    (
        $input:expr,
        $parser:expr,
        Ok(Mime { slash: $slash:expr, plus: $plus:expr, end: $end:expr, .. })
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
    err_bad_type { "a b/abc" == Err(InvalidToken { pos: 1, byte: b' ' }) }
    err_no_subtype { "abc/" == Err(MissingSubtype) }
    err_just_slash {  "/" == Err(MissingType) }
    err_multiple_slash { "ab//c" == Err(InvalidToken { pos: 3, byte: b'/' }) }
    err_multiple_separate_slash {
        "ab/c/d" == Err(InvalidToken { pos: 4, byte: b'/' })
    }
    err_subtype_range_suffix {
        "foo/*+a" == Err(InvalidToken { pos: 4, byte: b'*' })
    }
    err_trailing_spaces { "a/b   \t" == Err(TrailingWhitespace) }
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
        "a/b; k =v" == Err(InvalidParameter { pos: 6, byte: b' ' })
    }
    err_space_after_parameter { "a/b; k=v " == Err(TrailingWhitespace) }
    err_missing_parameter_key {
        "a/b; =v" == Err(InvalidParameter { pos: 5, byte: b'=' })
    }
    err_parameter_double_equal {
        "a/b; k==v" == Err(InvalidParameter { pos: 7, byte: b'=' })
    }
    err_missing_parameter { "a/b;; k=v" == Err(MissingParameter { pos: 4 }) }
    err_parameter_start_quoted {
        r#"a/b; k="a"# == Err(MissingParameterQuote { pos: 9 })
    }
    err_parameter_quoted_invalid_char {
        "a/b; k=\"\n\"" == Err(InvalidQuotedString { pos: 8, byte: b'\n' })
    }
    err_parameter_quoted_char_after_end {
        "a/b; k=\"a\"b" == Err(InvalidParameter { pos: 10, byte: b'b' })
    }
    err_foo_slash_star_star {
        "foo/**" == Err(InvalidToken { pos: 4, byte: b'*' })
    }
    err_foo_slash_star_a {
        "foo/*a" == Err(InvalidToken { pos: 4, byte: b'*' })
    }
    err_star_slash_foo { "*/foo" == Err(InvalidToken { pos: 0, byte: b'*' }) }
    err_star_a_slash_star { "*a/*" == Err(InvalidToken { pos: 0, byte: b'*' }) }
    err_star_slash_a_star { "*/*a" == Err(InvalidToken { pos: 0, byte: b'*' }) }
    err_star_slash_a_star_one_parameter {
        "*/*a; k=v" == Err(InvalidToken { pos: 0, byte: b'*' })
    }
}

// Tests against only the media type parser.
tests_type! {
    type_parse_err_everything_range {
        "*/*" == Err(InvalidToken { pos: 0, byte: b'*' })
    }
    type_parse_err_subtype_range {
        "foo/*" == Err(InvalidToken { pos: 4, byte: b'*' })
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
