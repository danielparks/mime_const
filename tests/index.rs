//! Test behavior of [`mime_const::index::Mime`].

use mime_const::index::Mime;
// use mime_const::rfc7231::ParseError;

#[test]
fn const_display_lowercase() {
    assert_eq!(
        Mime::constant("text/plain; charset=utf-8").to_string(),
        "text/plain; charset=utf-8"
    );
}

#[test]
fn new_display_lowercase() {
    assert_eq!(
        Mime::new("text/plain; charset=utf-8").unwrap().to_string(),
        "text/plain; charset=utf-8"
    );
}

/*
#[ignore = "no case support"]
#[test]
#[should_panic]
fn const_display_uppercase() {
    assert_eq!(
        Mime::try_constant("TEXT/PLAIN; CHARSET=UTF-8"),
        Err(ParseError::UppercaseType { pos: 0, byte: b'T' })
    );
}
*/

#[ignore = "no case support"]
#[test]
fn new_display_uppercase() {
    assert_eq!(
        Mime::new("TEXT/PLAIN; CHARSET=UTF-8").unwrap().to_string(),
        "text/plain; charset=utf-8"
    );
}
