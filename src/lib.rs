//! # Minimum supported Rust version
//!
//! Currently the minimum supported Rust version (MSRV) is **1.46**. Future
//! increases in the MSRV will require a major version bump.

#![forbid(unsafe_code)]
// Enable doc_cfg on docsrs so that we get feature markers.
#![cfg_attr(docsrs, feature(doc_cfg))]

mod const_utils;
mod index_t;

pub use index_t::*;

pub mod index;
pub mod owned;
pub mod rfc7231;
pub mod slice;
