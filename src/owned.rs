//! MIME/media type stored as `String`s. This cannot be constructed in `const.

use crate::slice;

/// A `Mime` that stores its parts in `String`s.
///
/// ```rust
/// use mime_const::slice;
/// use mime_const::owned::Mime;
///
/// let mime: Mime = slice::Mime::new(
///     "image",
///     "svg+xml",
///     Some("xml"),
///     Some(slice::Parameter::new("charset", "utf-8").unwrap()),
///     None,
/// )
/// .unwrap()
/// .into();
///
/// assert_eq!(mime.type_(), "image");
/// assert_eq!(mime.subtype(), "svg+xml");
/// assert_eq!(mime.suffix(), Some("xml"));
/// let one = mime.parameters().next().unwrap();
/// assert_eq!(one.name(), "charset");
/// assert_eq!(one.value(), "utf-8");
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mime {
    pub(crate) type_: String,
    pub(crate) subtype: String,
    pub(crate) suffix: Option<u16>,
    pub(crate) parameters: Vec<Parameter>,
}

impl Mime {
    #[must_use]
    pub fn type_(&self) -> &str {
        self.type_.as_str()
    }

    #[must_use]
    pub fn subtype(&self) -> &str {
        self.subtype.as_str()
    }

    #[must_use]
    pub fn suffix(&self) -> Option<&str> {
        self.suffix
            .map(|suffix| &self.subtype[usize::from(suffix)..])
    }

    pub fn parameters(&self) -> std::slice::Iter<'_, Parameter> {
        self.parameters.iter()
    }
}

impl From<slice::Mime<'_>> for Mime {
    fn from(mime: slice::Mime<'_>) -> Self {
        Self {
            type_: mime.type_.to_owned(),
            subtype: mime.subtype.to_owned(),
            suffix: mime.suffix.map(|suffix| {
                (mime.subtype.len() - suffix.len()).try_into().unwrap()
            }),
            parameters: mime.parameters().map(|p| p.into()).collect(),
        }
    }
}

/// A single parameter in a MIME type, e.g. “charset=utf-8”.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Parameter {
    pub(crate) name: String,
    pub(crate) value: String,
}

impl Parameter {
    #[must_use]
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    #[must_use]
    pub fn value(&self) -> &str {
        self.value.as_str()
    }
}

impl From<&slice::Parameter<'_>> for Parameter {
    fn from(other: &slice::Parameter<'_>) -> Self {
        Self { name: other.name.to_owned(), value: other.value.to_owned() }
    }
}
