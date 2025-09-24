//! Test behavior of [`mime_const::index::Mime`].

use mime_const::index::Mime;

#[test]
fn display_const_lowercase() {
    assert_eq!(
        Mime::try_constant("text/plain; charset=utf-8").map(|m| m.to_string()),
        Ok("text/plain; charset=utf-8".to_owned()),
    );
}

#[test]
fn display_new_lowercase() {
    assert_eq!(
        Mime::new("text/plain; charset=utf-8").map(|m| m.to_string()),
        Ok("text/plain; charset=utf-8".to_owned())
    );
}

#[test]
fn display_const_mixed_case() {
    assert_eq!(
        Mime::try_constant("Text/SGML; CharSet=UTF-8").map(|m| m.to_string()),
        Ok("Text/SGML; CharSet=UTF-8".to_owned()),
    );
}

#[test]
fn display_new_mixed_case() {
    assert_eq!(
        Mime::new("Text/SGML; CharSet=UTF-8").map(|m| m.to_string()),
        Ok("Text/SGML; CharSet=UTF-8".to_owned())
    );
}

#[test]
fn display_const_extra_spaces() {
    assert_eq!(
        Mime::try_constant("text/plain  ;   charset=utf-8")
            .map(|m| m.to_string()),
        Ok("text/plain; charset=utf-8".to_owned()),
    );
}

#[test]
fn display_new_extra_spaces() {
    assert_eq!(
        Mime::new("text/plain   ;  charset=utf-8").map(|m| m.to_string()),
        Ok("text/plain; charset=utf-8".to_owned())
    );
}

#[test]
fn display_const_no_spaces() {
    assert_eq!(
        Mime::try_constant("text/plain;charset=utf-8").map(|m| m.to_string()),
        Ok("text/plain; charset=utf-8".to_owned()),
    );
}

#[test]
fn display_new_no_spaces() {
    assert_eq!(
        Mime::new("text/plain;charset=utf-8").map(|m| m.to_string()),
        Ok("text/plain; charset=utf-8".to_owned())
    );
}
