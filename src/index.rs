//! MIME/media type stored as a slice with indices to its parts.

// FIXME should implement Eq, PartialEq, Ord, and PartialOrd manually
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mime<'a> {
    pub(crate) source: Source<'a>,
    pub(crate) slash: u16,
    pub(crate) plus: Option<u16>,
    pub(crate) end: u16,
    pub(crate) parameters: Parameters,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Source<'a> {
    Str(&'a str),
    #[expect(dead_code, reason = "FIXME")]
    Owned(String),
}

/// Parameters in a MIME type.
///
/// This can only store the parse information for two parameters because an
/// arbitrary number of parameters would require a `Vec` and we can’t fill a
/// `Vec` in a `const fn`.
///
/// Instead, we validate the parameters and re-parse when need to access them.
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum Parameters {
    None,
    One(Parameter),
    Two(Parameter, Parameter),
    /// More than two.
    Many,
}

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
///
/// This only contains indices, so it’s useless without the [`Mime`] struct and
/// its [`Source`];
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct Parameter {
    /// The index of the start of the parameter name.
    pub(crate) start: u16,

    /// The index of the `'='`. The start of the value is `equal + 1`.
    pub(crate) equal: u16,

    /// The index just past the last character in the value.
    pub(crate) end: u16,

    /// Whether or not the value is a quoted string.
    pub(crate) quoted: bool,
}
