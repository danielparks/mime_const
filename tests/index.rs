//! Test behavior of [`mime_const::index::Mime`].

use assert2::assert;
use mime_const::index::Mime;

#[test]
fn display_const_lowercase() {
    assert!(
        Mime::try_constant("text/plain; charset=utf-8").map(|m| m.to_string())
            == Ok("text/plain; charset=utf-8".to_owned())
    );
}

#[test]
fn display_new_lowercase() {
    assert!(
        Mime::new("text/plain; charset=utf-8").map(|m| m.to_string())
            == Ok("text/plain; charset=utf-8".to_owned())
    );
}

#[test]
fn display_const_mixed_case() {
    assert!(
        Mime::try_constant("Text/SGML; CharSet=UTF-8").map(|m| m.to_string())
            == Ok("Text/SGML; CharSet=UTF-8".to_owned()),
    );
}

#[test]
fn display_new_mixed_case() {
    assert!(
        Mime::new("Text/SGML; CharSet=UTF-8").map(|m| m.to_string())
            == Ok("Text/SGML; CharSet=UTF-8".to_owned())
    );
}

#[test]
fn display_const_extra_spaces() {
    assert!(
        Mime::try_constant("text/plain  ;   charset=utf-8")
            .map(|m| m.to_string())
            == Ok("text/plain; charset=utf-8".to_owned()),
    );
}

#[test]
fn display_new_extra_spaces() {
    assert!(
        Mime::new("text/plain   ;  charset=utf-8").map(|m| m.to_string())
            == Ok("text/plain; charset=utf-8".to_owned())
    );
}

#[test]
fn display_const_no_spaces() {
    assert!(
        Mime::try_constant("text/plain;charset=utf-8").map(|m| m.to_string())
            == Ok("text/plain; charset=utf-8".to_owned()),
    );
}

#[test]
fn display_new_no_spaces() {
    assert!(
        Mime::new("text/plain;charset=utf-8").map(|m| m.to_string())
            == Ok("text/plain; charset=utf-8".to_owned())
    );
}

#[test]
fn eq_const_spaces() {
    assert!(
        Mime::try_constant("text/plain;charset=utf-8")
            == Mime::try_constant("text/plain   ; charset=utf-8")
    );
}

#[test]
fn eq_new_spaces() {
    assert!(
        Mime::new("text/plain;charset=utf-8")
            == Mime::new("text/plain   ; charset=utf-8")
    );
}

#[test]
fn eq_const_parameters() {
    assert!(
        Mime::try_constant("a/b; k1=v1; k2=v2")
            == Mime::try_constant("a/b; k2=v2; k1=v1")
    );
}

#[test]
fn ne_const_parameters_different_len() {
    assert!(
        Mime::try_constant("a/b; k1=v1; k2=v2")
            != Mime::try_constant("a/b; k1=v1")
    );
}

#[test]
fn eq_const_mixed_case() {
    assert!(
        Mime::try_constant("A/b; K1=aaa; k2=v2")
            == Mime::try_constant("a/B; K2=v2; k1=aaa")
    );
}

#[test]
fn ne_const_mixed_case_parameter_values() {
    assert!(
        Mime::try_constant("a/b; k1=AAA; k2=v2")
            != Mime::try_constant("a/b; k1=aaa; k2=v2")
    );
}
