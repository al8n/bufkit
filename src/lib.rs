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

pub use chunk::*;
pub use chunk_mut::*;

/// Errors buffer I/O
pub mod error;

macro_rules! non_zero {
  ($($size:literal),+$(,)?) => {
    paste::paste! {
      $(
        const [<NON_ZERO_ $size>]: ::core::num::NonZeroUsize = core::num::NonZeroUsize::new($size).expect(concat!($size, "is non-zero"));
      )*
    }
  };
}

non_zero!(1);

mod chunk;
mod chunk_mut;

/// Panic with a nice error message.
#[cold]
fn panic_advance(error_info: &error::TryAdvanceError) -> ! {
  panic!(
    "advance out of bounds: the len is {} but advancing by {}",
    error_info.available(),
    error_info.requested()
  );
}

/// # Panics
/// This function panics if `size` is zero. Use only when you have already checked that `size` is non-zero.
#[inline]
const fn must_non_zero(size: usize) -> core::num::NonZeroUsize {
  match core::num::NonZeroUsize::new(size) {
    Some(nz) => nz,
    None => panic!("Already checked value is non-zero"),
  }
}

#[test]
#[should_panic]
fn test_must_non_zero_panic() {
  must_non_zero(0);
}