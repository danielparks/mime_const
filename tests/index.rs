//! Test behavior of [`mime_const::index::Mime`].

use assert2::assert;
use itertools::Itertools;
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

#[test]
fn sort_mime() {
    let source = &[
        Mime::constant("a/b"),
        Mime::constant("a/b; k=v"),
        Mime::constant("A/b; k=v; k2=v"),
        Mime::constant("b/a; k=v"),
        Mime::constant("b/B; k=v"),
        Mime::constant("b/b; k=v2"),
        Mime::constant("b/b; k2=2; k1=1"),
        Mime::constant("b/b; k2=1; k1=2"),
    ][..];

    fn stringify<T: ToString>(slice: &[T]) -> Vec<String> {
        slice.iter().map(|m| m.to_string()).collect()
    }

    let expected = stringify(source);
    for mut permution in source.iter().permutations(expected.len()) {
        permution.sort();
        assert!(expected == stringify(&permution));
    }
}
