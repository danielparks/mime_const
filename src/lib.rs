//! # Minimum supported Rust version
//!
//! Currently the minimum supported Rust version (MSRV) is **1.46**. Future
//! increases in the MSRV will require a major version bump.

#![forbid(unsafe_code)]
// Enable doc_cfg on docsrs so that we get feature markers.
#![cfg_attr(docsrs, feature(doc_cfg))]

pub mod rfc7231;
pub use rfc7231::*;
