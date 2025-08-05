#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
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

pub use buf::*;
pub use buf_mut::*;

/// Errors buffer I/O
pub mod error;

mod buf;
mod buf_mut;

/// Panic with a nice error message.
#[cold]
fn panic_advance(error_info: &error::TryAdvanceError) -> ! {
  panic!(
    "advance out of bounds: the len is {} but advancing by {}",
    error_info.available(),
    error_info.requested()
  );
}
