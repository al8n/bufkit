#[cfg(feature = "varing")]
#[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
pub use varing::{DecodeError as ReadVarintError, EncodeError as WriteVarintError};

use core::num::NonZeroUsize;

macro_rules! try_op_error {
  (
    #[doc = $doc:literal]
    #[error($msg:literal)]
    $op:ident
  ) => {
    paste::paste! {
      #[doc = $doc]
      #[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
      #[error($msg)]
      pub struct [< Try $op:camel Error >] {
        requested: NonZeroUsize,
        available: usize,
      }

      impl [< Try $op:camel Error >] {
        #[doc = "Creates a new `Try" $op:camel "Error` with the requested and available bytes."]
        ///
        /// # Panics
        ///
        /// - In debug builds, panics if `requested <= available` (this would not be an error condition).
        /// - The `requested` value must be a non-zero.
        #[inline]
        pub const fn new(requested: usize, available: usize) -> Self {
          debug_assert!(requested > available, concat!(stringify!([< Try $op:camel Error >]), ": requested must be greater than available"));

          Self {
            requested: NonZeroUsize::new(requested).expect(
              concat!(stringify!([< Try $op:camel Error >]), ": requested must be non-zero")
            ),
            available,
          }
        }

        /// Returns the number of bytes requested for the operation.
        ///
        /// This is the minimum number of bytes needed for the operation to succeed.
        #[inline]
        pub const fn requested(&self) -> usize {
          self.requested.get()
        }

        /// Returns the number of bytes available in the buffer.
        ///
        /// This is the actual number of bytes that were available when the operation failed.
        #[inline]
        pub const fn available(&self) -> usize {
          self.available
        }

        /// Returns the number of additional bytes needed for the operation to succeed.
        ///
        /// This is equivalent to `requested() - available()`.
        #[inline]
        pub const fn shortage(&self) -> usize {
          self.requested() - self.available()
        }
      }
    }
  };
}

try_op_error!(
  #[doc = "An error that occurs when trying to advance the buffer cursor beyond available data.
  
This error indicates that an attempt was made to move the buffer's read position forward
by more bytes than are currently available. This is a recoverable error - the buffer
position remains unchanged and the operation can be retried with a smaller advance amount."]
  #[error(
    "not enough bytes available to advance (requested {requested} but only {available} available)"
  )]
  advance
);

#[cfg(feature = "std")]
impl From<TryAdvanceError> for std::io::Error {
  fn from(e: TryAdvanceError) -> Self {
    std::io::Error::new(std::io::ErrorKind::UnexpectedEof, e)
  }
}

try_op_error!(
  #[doc = "An error that occurs when trying to read data from a buffer with insufficient bytes.
  
This error indicates that a read operation failed because the buffer does not contain
enough bytes to satisfy the request. Failed read operations do not consume any bytes - the buffer position remains unchanged."]
  #[error(
    "not enough bytes available to read value (requested {requested} but only {available} available)"
  )]
  read
);

#[cfg(feature = "std")]
impl From<TryReadError> for std::io::Error {
  fn from(e: TryReadError) -> Self {
    std::io::Error::new(std::io::ErrorKind::UnexpectedEof, e)
  }
}

try_op_error!(
  #[doc = "An error that occurs when trying to peek at data beyond the buffer's available bytes.
  
This error indicates that a peek operation failed because the buffer does not contain
enough bytes at the current position. Peek operations never modify the buffer position,
so this error leaves the buffer in its original state."]
  #[error(
    "not enough bytes available to peek value (requested {requested} but only {available} available)"
  )]
  peek
);

#[cfg(feature = "std")]
impl From<TryPeekError> for std::io::Error {
  fn from(e: TryPeekError) -> Self {
    std::io::Error::new(std::io::ErrorKind::UnexpectedEof, e)
  }
}

impl From<TryPeekError> for TryReadError {
  #[inline]
  fn from(e: TryPeekError) -> Self {
    TryReadError {
      requested: e.requested,
      available: e.available,
    }
  }
}

try_op_error!(
  #[doc = "An error that occurs when trying to write data to a buffer with insufficient space.
  
This error indicates that a write operation failed because the buffer does not have
enough remaining capacity to hold the data.

This error is particularly useful for Sans-I/O designs as it provides exact information
about space requirements, allowing the caller to allocate a larger buffer and retry:

```rust
# use bufkit::BufMut;
let mut small_buf = [0u8; 4];
let mut writer = &mut small_buf[..];

match writer.try_put_u64_le(0x123456789ABCDEF0) {
    Err(e) => {
        // Caller knows exactly how much space is needed
        assert_eq!(e.requested(), 8);
        assert_eq!(e.available(), 4);
        println!(\"Need {} more bytes\", e.shortage());
    }
    _ => panic!(\"Expected error\"),
}
```"]
  #[error(
    "not enough space available to write value (requested {requested} but only {available} available)"
  )]
  write
);

#[cfg(feature = "std")]
impl From<TryWriteError> for std::io::Error {
  fn from(e: TryWriteError) -> Self {
    std::io::Error::new(std::io::ErrorKind::WriteZero, e)
  }
}

/// An error that occurs when trying to create a segment with an invalid range.
///
/// This error indicates that the requested range extends beyond the buffer's boundaries
/// or is otherwise invalid (e.g., start > end). The original buffer remains unchanged.
///
/// # Examples
///
/// ```rust
/// # use bufkit::Buf;
/// let data = b"Hello";
/// let buf = &data[..];
///
/// // Range extends beyond buffer
/// match buf.try_segment(2..10) {
///     Err(e) => {
///         assert_eq!(e.start(), 2);
///         assert_eq!(e.end(), 10);
///         assert_eq!(e.available(), 5);
///     }
///     _ => panic!("Expected error"),
/// }
///
/// // Invalid range (start > end)
/// assert!(buf.try_segment(4..2).is_err());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("invalid segment range {start}..{end} for buffer with {available} bytes")]
pub struct TrySegmentError {
  start: usize,
  end: usize,
  available: usize,
}

impl TrySegmentError {
  /// Creates a new `TrySegmentError`.
  ///
  /// # Panics
  ///
  /// In debug builds, panics if the range is valid (would not be an error) or the available bytes are less than the requested range.
  #[inline]
  pub const fn new(start: usize, end: usize, available: usize) -> Self {
    debug_assert!(
      start > end || end > available,
      "TrySegmentError: invalid error - range is valid"
    );

    Self {
      start,
      end,
      available,
    }
  }

  /// Returns the start index of the requested range.
  #[inline]
  pub const fn start(&self) -> usize {
    self.start
  }

  /// Returns the end index of the requested range (exclusive).
  #[inline]
  pub const fn end(&self) -> usize {
    self.end
  }

  /// Returns the total number of bytes available in the buffer.
  #[inline]
  pub const fn available(&self) -> usize {
    self.available
  }

  /// Returns the length of the requested range.
  ///
  /// Returns 0 if start > end (invalid range).
  #[inline]
  pub const fn requested(&self) -> usize {
    self.end.saturating_sub(self.start)
  }

  /// Returns whether the range itself is invalid (start > end).
  #[inline]
  pub const fn is_inverted(&self) -> bool {
    self.start > self.end
  }

  /// Returns how many bytes the range extends beyond the buffer.
  ///
  /// Returns 0 if the range doesn't extend beyond the buffer
  /// (e.g., when the error is due to start > end).
  #[inline]
  pub const fn overflow(&self) -> usize {
    self.end.saturating_sub(self.available)
  }
}

#[cfg(feature = "std")]
impl From<TrySegmentError> for std::io::Error {
  fn from(e: TrySegmentError) -> Self {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
  }
}

/// An error that occurs when an offset is beyond the buffer's boundaries.
///
/// This error is typically used for operations that access a specific position
/// in the buffer, such as writing at an offset or splitting at a position.
///
/// # Example
///
/// ```rust
/// # use bufkit::BufMut;
/// let mut buf = [0u8; 10];
/// let mut writer = &mut buf[..];
///
/// // Trying to write at offset 15 in a 10-byte buffer
/// match writer.try_put_u32_le_at(42, 15) {
///     Err(e) => {
///         // Error contains OutOfBounds information
///     }
///     _ => panic!("Expected error"),
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("offset {offset} is out of bounds for buffer length {length}")]
pub struct OutOfBounds {
  offset: usize,
  length: usize,
}

impl OutOfBounds {
  /// Creates a new `OutOfBounds` error.
  ///
  /// # Panics
  ///
  /// In debug builds, panics if `offset < length` (would not be out of bounds).
  #[inline]
  pub const fn new(offset: usize, length: usize) -> Self {
    debug_assert!(offset >= length, "OutOfBounds: offset must be >= length");

    Self { offset, length }
  }

  /// Returns the offset that caused the error.
  #[inline]
  pub const fn offset(&self) -> usize {
    self.offset
  }

  /// Returns the actual length of the buffer.
  #[inline]
  pub const fn length(&self) -> usize {
    self.length
  }

  /// Returns how far beyond the buffer the offset extends.
  ///
  /// This is equivalent to `offset() - length() + 1`.
  #[inline]
  pub const fn excess(&self) -> usize {
    self.offset() - self.length() + 1
  }
}

#[cfg(feature = "std")]
impl From<OutOfBounds> for std::io::Error {
  fn from(e: OutOfBounds) -> Self {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
  }
}

/// An error indicating insufficient space at a specific offset in a buffer.
///
/// This error provides detailed information about space requirements when a write
/// operation fails due to insufficient remaining capacity from a given offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error(
  "not enough bytes available at {offset} (requested {requested} but only {available} available)"
)]
pub struct InsufficientSpaceAt {
  /// The number of bytes requested to write.
  requested: NonZeroUsize,
  /// The number of bytes available from the offset to the end of buffer.
  available: usize,
  /// The offset at which the write was attempted.
  offset: usize,
}

impl InsufficientSpaceAt {
  /// Creates a new `InsufficientSpaceAt` error.
  ///
  /// # Panics
  ///
  /// - In debug builds, panics if `requested <= available` (would not be an error).
  /// - The `requested` value must be a non-zero.
  #[inline]
  pub const fn new(requested: usize, available: usize, offset: usize) -> Self {
    debug_assert!(
      requested > available,
      "InsufficientSpaceAt: requested must be greater than available"
    );

    Self {
      requested: NonZeroUsize::new(requested)
        .expect("InsufficientSpaceAt: requested must be non-zero"),
      available,
      offset,
    }
  }

  /// Returns the number of bytes requested to write.
  #[inline]
  pub const fn requested(&self) -> usize {
    self.requested.get()
  }

  /// Returns the number of bytes available from the offset.
  #[inline]
  pub const fn available(&self) -> usize {
    self.available
  }

  /// Returns the offset at which the write was attempted.
  #[inline]
  pub const fn offset(&self) -> usize {
    self.offset
  }

  /// Returns the number of additional bytes needed for the operation to succeed.
  ///
  /// This is equivalent to `requested() - available()`.
  #[inline]
  pub const fn shortage(&self) -> usize {
    self.requested() - self.available()
  }
}

/// An error that occurs when trying to write at a specific offset in the buffer.
///
/// This error is returned when the offset is out of bounds or when there is insufficient space to write the requested data.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TryWriteAtError {
  /// An error that occurs when trying to write at an offset that is out of bounds for the buffer.
  #[error(transparent)]
  OutOfBounds(#[from] OutOfBounds),
  /// An error that occurs when there is not enough space in the buffer to write the requested data.
  #[error(transparent)]
  InsufficientSpace(#[from] InsufficientSpaceAt),
}

impl TryWriteAtError {
  /// Creates a new `TryWriteAtError::OutOfBounds` error.
  #[inline]
  pub const fn out_of_bounds(offset: usize, length: usize) -> Self {
    Self::OutOfBounds(OutOfBounds::new(offset, length))
  }

  /// Creates a new `TryWriteAtError::InsufficientSpace` error.
  ///
  /// # Panics
  ///
  /// - In debug builds, panics if `requested <= available` (would not be an error).
  /// - The `requested` value must be a non-zero.
  #[inline]
  pub const fn insufficient_space(requested: usize, available: usize, offset: usize) -> Self {
    Self::InsufficientSpace(InsufficientSpaceAt::new(requested, available, offset))
  }
}

#[cfg(feature = "std")]
impl From<TryWriteAtError> for std::io::Error {
  fn from(e: TryWriteAtError) -> Self {
    match e {
      TryWriteAtError::OutOfBounds(e) => std::io::Error::new(std::io::ErrorKind::InvalidInput, e),
      TryWriteAtError::InsufficientSpace(e) => {
        if e.offset() >= e.available() {
          std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
        } else {
          std::io::Error::new(std::io::ErrorKind::WriteZero, e)
        }
      }
    }
  }
}

/// An error that occurs when trying to write type in LEB128 format at a specific offset in the buffer.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
#[cfg(feature = "varing")]
#[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
pub enum WriteVarintAtError {
  /// The offset is out of bounds for the buffer length.
  #[error(transparent)]
  OutOfBounds(#[from] OutOfBounds),
  /// The buffer does not have enough capacity to encode the value.
  #[error(transparent)]
  InsufficientSpace(#[from] InsufficientSpaceAt),
  /// A custom error message.
  #[error("{0}")]
  #[cfg(not(any(feature = "std", feature = "alloc")))]
  Other(&'static str),

  /// A custom error message.
  #[error("{0}")]
  #[cfg(any(feature = "std", feature = "alloc"))]
  Other(std::borrow::Cow<'static, str>),
}

#[cfg(feature = "varing")]
impl WriteVarintAtError {
  /// Creates a new `WriteVarintAtError::OutOfBounds` error.
  #[inline]
  pub const fn out_of_bounds(offset: usize, length: usize) -> Self {
    Self::OutOfBounds(OutOfBounds::new(offset, length))
  }

  /// Creates a new `WriteVarintAtError::Insufficient` error.
  ///
  /// # Panics
  ///
  /// - In debug builds, panics if `requested <= available` (would not be an error).
  /// - The `requested` value must be a non-zero.
  #[inline]
  pub const fn insufficient_space(requested: usize, available: usize, offset: usize) -> Self {
    Self::InsufficientSpace(InsufficientSpaceAt::new(requested, available, offset))
  }

  /// Creates a new `WriteVarintAtError` error from `WriteVarintError`.
  #[inline]
  pub const fn from_write_varint_error(err: WriteVarintError, offset: usize) -> Self {
    match err {
      WriteVarintError::InsufficientSpace(e) => {
        Self::insufficient_space(e.requested(), e.available(), offset)
      }
      #[cfg(any(feature = "std", feature = "alloc"))]
      WriteVarintError::Other(msg) => Self::Other(std::borrow::Cow::Borrowed(msg)),
      #[cfg(not(any(feature = "std", feature = "alloc")))]
      WriteVarintError::Other(msg) => Self::other(msg),
      #[cfg(any(feature = "std", feature = "alloc"))]
      _ => Self::Other(std::borrow::Cow::Borrowed("unknown error")),
      #[cfg(not(any(feature = "std", feature = "alloc")))]
      _ => Self::Other("unknown error"),
    }
  }

  /// Creates a new `WriteVarintAtError::Other` error.
  #[cfg(not(any(feature = "std", feature = "alloc")))]
  #[inline]
  pub const fn other(msg: &'static str) -> Self {
    Self::Other(msg)
  }

  /// Creates a new `WriteVarintAtError::Other` error.
  #[cfg(any(feature = "std", feature = "alloc"))]
  #[inline]
  pub fn other(msg: impl Into<std::borrow::Cow<'static, str>>) -> Self {
    Self::Other(msg.into())
  }
}

#[cfg(all(feature = "varing", feature = "std"))]
impl From<WriteVarintAtError> for std::io::Error {
  fn from(e: WriteVarintAtError) -> Self {
    match e {
      WriteVarintAtError::OutOfBounds(e) => {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
      }
      WriteVarintAtError::InsufficientSpace(e) => {
        if e.offset() >= e.available() {
          std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
        } else {
          std::io::Error::new(std::io::ErrorKind::WriteZero, e)
        }
      }
      WriteVarintAtError::Other(msg) => std::io::Error::other(msg),
    }
  }
}

#[cfg(feature = "bytes_1")]
const _: () = {
  use bytes_1::TryGetError;

  impl From<TryGetError> for TryAdvanceError {
    fn from(e: TryGetError) -> Self {
      TryAdvanceError::new(e.requested, e.available)
    }
  }

  impl From<TryGetError> for TryReadError {
    fn from(e: TryGetError) -> Self {
      TryReadError::new(e.requested, e.available)
    }
  }
};
