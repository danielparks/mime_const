//! Filter ASCII characters against a byte filter.
//!
//! Used to quickly determine if characters in a string are an valid.
//!
//! ```
//! use mime_const::bytefilter::ByteFilter;
//!
//! const UPPER: ByteFilter = ByteFilter::from_str("A-Z");
//!
//! fn main() {
//!     assert!(UPPER.match_char('N'));
//!     assert!(!UPPER.match_char('n'));
//!     assert!(!UPPER.match_char(' '));
//!     assert!(!UPPER.match_char('π'));
//! }
//! ```

use std::error;
use std::fmt;
use std::ops::{Range, RangeInclusive};

/// The bit filter
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByteFilter(pub [bool; 256]);

impl ByteFilter {
    /// Create a `ByteFilter` from a range string.
    ///
    /// ```
    /// use mime_const::bytefilter::{ByteFilter, Error};
    ///
    /// assert!(ByteFilter::try_from_bytes(b"A").is_ok());
    /// assert_eq!(
    ///     Err(Error::InvalidRange { index: 1 }),
    ///     ByteFilter::try_from_bytes(b" z-a"),
    /// );
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`Error`] for invalid range strings.
    #[allow(clippy::arithmetic_side_effects)] // we check first
    pub const fn try_from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut filter = [false; 256];
        if bytes.is_empty() {
            return Ok(Self(filter));
        }

        // First byte; can be b'-'
        let mut i = 0;
        filter[bytes[i] as usize] = true;
        i += 1;

        if i >= bytes.len() {
            return Ok(Self(filter));
        }
        while i < bytes.len() - 1 {
            let b = bytes[i];
            if b == b'-' {
                // Found range
                if bytes[i - 1] > bytes[i + 1] {
                    return Err(Error::InvalidRange { index: i - 1 });
                }
                let mut b = bytes[i - 1] + 1; // Already added the start byte
                while b < bytes[i + 1] {
                    // Will add the end byte next loop
                    filter[b as usize] = true;
                    b += 1;
                }
            } else {
                filter[b as usize] = true;
            }

            i += 1;
        }

        // Last byte; can be b'-'
        filter[bytes[i] as usize] = true;

        Ok(Self(filter))
    }

    /// Create a `ByteFilter` from a range string, or panic.
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// const UPPER: ByteFilter = ByteFilter::from_bytes(b"A-Z");
    ///
    /// fn main() {
    ///     assert!(UPPER.match_byte(b'N'));
    ///     assert!(!UPPER.match_byte(b'n'));
    ///     assert!(!UPPER.match_byte(b' '));
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the bytes contain an invalid range.
    #[must_use]
    #[inline]
    pub const fn from_bytes(bytes: &[u8]) -> Self {
        match Self::try_from_bytes(bytes) {
            Ok(filter) => filter,
            Err(error) => error.panic(),
        }
    }

    /// Create a `ByteFilter` from a range string.
    ///
    /// ```
    /// use mime_const::bytefilter::{ByteFilter, Error};
    ///
    /// assert!(ByteFilter::try_from_str("A").is_ok());
    /// assert_eq!(
    ///     Err(Error::InvalidRange { index: 1 }),
    ///     ByteFilter::try_from_str(" z-a"),
    /// );
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`Error`] for invalid range strings.
    #[inline]
    pub const fn try_from_str(chars: &str) -> Result<Self, Error> {
        Self::try_from_bytes(chars.as_bytes())
    }

    /// Create a `ByteFilter` from a range string, or panic.
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// const UPPER: ByteFilter = ByteFilter::from_str("A-Z");
    ///
    /// fn main() {
    ///     assert!(UPPER.match_byte(b'N'));
    ///     assert!(!UPPER.match_byte(b'n'));
    ///     assert!(!UPPER.match_byte(b' '));
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the string contains an invalid range.
    #[must_use]
    #[inline]
    pub const fn from_str(chars: &str) -> Self {
        Self::from_bytes(chars.as_bytes())
    }

    /// Add a range of bytes to the filter.
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// const ALPHA: ByteFilter = ByteFilter::from_bytes(b"A-Z")
    ///     .with_range(b'a'..b'z');
    ///
    /// fn main() {
    ///     assert!(ALPHA.match_byte(b'N'));
    ///     assert!(ALPHA.match_byte(b'n'));
    ///     assert!(!ALPHA.match_byte(b'z'));
    ///     assert!(!ALPHA.match_byte(b' '));
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the bytes contain an invalid range.
    #[must_use]
    #[inline]
    pub const fn with_range(mut self, range: Range<u8>) -> Self {
        let mut i = range.start;
        while i < range.end {
            self.0[i as usize] = true;
            i += 1;
        }
        self
    }

    /// Add a range of bytes to the filter.
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// const ALPHA: ByteFilter = ByteFilter::from_bytes(b"A-Z")
    ///     .with_inclusive_range(b'a'..=b'z');
    ///
    /// fn main() {
    ///     assert!(ALPHA.match_byte(b'N'));
    ///     assert!(ALPHA.match_byte(b'n'));
    ///     assert!(ALPHA.match_byte(b'z'));
    ///     assert!(!ALPHA.match_byte(b' '));
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the bytes contain an invalid range.
    #[must_use]
    #[inline]
    pub const fn with_inclusive_range(
        mut self,
        range: RangeInclusive<u8>,
    ) -> Self {
        let mut i = *range.start();
        self.0[i as usize] = true;
        // Avoid u8::MAX + 1
        while i < *range.end() {
            i += 1;
            self.0[i as usize] = true;
        }
        self
    }

    /// Invert `ByteFilter`.
    ///
    /// Note this still won’t match non-ASCII chars. See
    /// [`Self::match_or_non_ascii()`].
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// let upper = ByteFilter::from_bytes(b"A-Z");
    ///
    /// assert!(upper.match_char('N'));
    /// assert!(!upper.match_char('n'));
    /// assert!(!upper.match_char(' '));
    /// assert!(!upper.match_char('π'));
    ///
    /// let non_upper = upper.inverted();
    ///
    /// assert!(!non_upper.match_char('N'));
    /// assert!(non_upper.match_char('n'));
    /// assert!(non_upper.match_char(' '));
    /// assert!(!non_upper.match_char('π'));
    /// ```
    #[must_use]
    #[inline]
    pub const fn inverted(&self) -> Self {
        let mut filter = [false; 256];
        let mut i = 0;
        while i < 256 {
            filter[i] = !self.0[i];
            i += 1;
        }
        Self(filter)
    }

    /// Check if a byte matches the filter
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// let UPPER = ByteFilter::from_bytes(b"A-Z");
    /// assert!(UPPER.match_byte(b'N'));
    /// assert!(!UPPER.match_byte(b'n'));
    /// assert!(!UPPER.match_byte(b' '));
    /// assert!(!UPPER.match_byte(128));
    /// ```
    #[must_use]
    #[inline]
    pub const fn match_byte(&self, b: u8) -> bool {
        self.0[b as usize]
    }

    /// Check if a char matches the filter
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// let UPPER = ByteFilter::from_bytes(b"A-Z");
    /// assert!(UPPER.match_char('N'));
    /// assert!(!UPPER.match_char('n'));
    /// assert!(!UPPER.match_char(' '));
    /// assert!(!UPPER.match_char('π'));
    /// ```
    #[must_use]
    #[inline]
    pub const fn match_char(&self, c: char) -> bool {
        c <= 255 as char && self.match_byte(c as u8)
    }

    /// Check if a char matches the filter, or isn’t ASCII
    ///
    /// ```
    /// use mime_const::bytefilter::ByteFilter;
    ///
    /// let UPPER = ByteFilter::from_bytes(b"A-Z");
    /// assert!(UPPER.match_or_non_ascii('N'));
    /// assert!(!UPPER.match_or_non_ascii('n'));
    /// assert!(!UPPER.match_or_non_ascii(' '));
    /// assert!(UPPER.match_or_non_ascii('π'));
    /// ```
    #[must_use]
    #[inline]
    pub const fn match_or_non_ascii(&self, c: char) -> bool {
        c > 255 as char || self.match_byte(c as u8)
    }
}

/// An error when creating a bit filter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    /// Invalid range: start is greater than end
    InvalidRange {
        /// The index of the start of the invalid range.
        index: usize,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRange { index } => {
                write!(
                    f,
                    "found range with start greater than end at {index}",
                    index = index
                )
            }
        }
    }
}

impl error::Error for Error {}

impl Error {
    /// Panic, displaying the basic error message.
    ///
    /// # Panics
    ///
    /// Always.
    pub const fn panic(&self) -> ! {
        match self {
            Self::InvalidRange { .. } => {
                panic!("found range with start greater than end ")
            }
        }
    }
}
