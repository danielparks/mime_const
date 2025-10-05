//! Helpers for benchmarks
#![allow(dead_code)] // Not all benchmarks need all items

use std::borrow::Cow;

/// Quick and dirty mime type parsing.
///
/// Quick and dirty test in `benchmarks()`.
#[allow(clippy::type_complexity)]
pub fn rough_parse(input: &str) -> BigTuple<'_> {
    fn parameter_to_tuple(key_value: &str) -> (&str, &str) {
        let mut iter = key_value.splitn(2, '=');
        (iter.next().unwrap(), iter.next().unwrap())
    }

    let (type_, rest) = input.split_once('/').unwrap();
    let mut iter = rest.splitn(4, "; ");
    let subtype = iter.next().unwrap();
    let suffix = subtype.split_once('+').map(|(_, suffix)| suffix);

    let parameter_1 = iter.next().map(parameter_to_tuple);
    let parameter_2 = iter.next().map(parameter_to_tuple);
    assert!(iter.next().is_none(), "too many parameters");

    (type_, subtype, suffix, parameter_1, parameter_2)
}

pub type BigTuple<'a> = (
    &'a str,
    &'a str,
    Option<&'a str>,
    Option<(&'a str, &'a str)>,
    Option<(&'a str, &'a str)>,
);

/// Quick and dirty mime type parsing.
#[allow(clippy::type_complexity)]
pub fn rough_parse_cow(input: &str) -> BigTupleCow<'_> {
    fn parameter_to_tuple(key_value: &str) -> (&str, Cow<'_, str>) {
        let mut iter = key_value.splitn(2, '=');
        (iter.next().unwrap(), Cow::Borrowed(iter.next().unwrap()))
    }

    let (type_, rest) = input.split_once('/').unwrap();
    let mut iter = rest.splitn(4, "; ");
    let subtype = iter.next().unwrap();
    let suffix = subtype.split_once('+').map(|(_, suffix)| suffix);

    let parameter_1 = iter.next().map(parameter_to_tuple);
    let parameter_2 = iter.next().map(parameter_to_tuple);
    assert!(iter.next().is_none(), "too many parameters");

    (type_, subtype, suffix, parameter_1, parameter_2)
}

pub type BigTupleCow<'a> = (
    &'a str,
    &'a str,
    Option<&'a str>,
    Option<(&'a str, Cow<'a, str>)>,
    Option<(&'a str, Cow<'a, str>)>,
);

/// Test `rough_parse()`.
///
/// Can’t have regular tests in `benches/`.
pub fn test_rough_parse() {
    assert_eq!(
        (
            "image",
            "svg+xml",
            Some("xml"),
            Some(("charset", "utf-8")),
            None
        ),
        rough_parse("image/svg+xml; charset=utf-8")
    );
}
