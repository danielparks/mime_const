//! Macros and functions to make working in `const` context easier.

/// Get a byte from the input.
///
/// Returns `None` if `i` is past the end of `input`.
#[inline]
pub(crate) const fn get_byte(input: &[u8], i: usize) -> Option<u8> {
    if i < input.len() {
        Some(input[i])
    } else {
        None
    }
}
