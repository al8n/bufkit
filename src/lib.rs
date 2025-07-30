//! A
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "varing")]
#[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
pub use varing::Varint;

pub use read_buf::*;
pub use write_buf::*;

/// Errors buffer I/O
pub mod error;

mod read_buf;
mod write_buf;

#[test]
fn t() {}
