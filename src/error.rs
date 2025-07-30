#[cfg(feature = "varing")]
#[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
pub use varing::{DecodeError as ReadVarintError, EncodeError as WriteVarintError};

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
        requested: usize,
        available: usize,
      }

      impl [< Try $op:camel Error >] {
        #[doc = "Creates a new `Try" $op:camel "Error` with the requested and available bytes."]
        #[inline]
        pub const fn new(requested: usize, available: usize) -> Self {
          Self {
            requested,
            available,
          }
        }

        /// Returns the number of bytes requested.
        #[inline]
        pub const fn requested(&self) -> usize {
          self.requested
        }

        /// Returns the number of bytes available.
        #[inline]
        pub const fn available(&self) -> usize {
          self.available
        }
      }

      #[cfg(feature = "std")]
      impl From<[< Try $op:camel Error >]> for std::io::Error {
        fn from(e: [< Try $op:camel Error >]) -> Self {
          std::io::Error::new(
            std::io::ErrorKind::UnexpectedEof,
            e,
          )
        }
      }
    }
  };
}

try_op_error!(
  #[doc = "An error that occurs when trying to advance the buffer."]
  #[error(
    "Not enough bytes available to advance (requested {requested} but only {available} available)"
  )]
  advance
);

try_op_error!(
  #[doc = "An error that occurs when trying to read a value from the buffer."]
  #[error(
    "Not enough bytes available to read value (requested {requested} but only {available} available)"
  )]
  read
);

try_op_error!(
  #[doc = "An error that occurs when trying to peek a value from the buffer."]
  #[error(
    "Not enough bytes available to peek value (requested {requested} but only {available} available)"
  )]
  peek
);

impl From<TryPeekError> for TryReadError {
  #[inline]
  fn from(e: TryPeekError) -> Self {
    TryReadError::new(e.requested, e.available)
  }
}

try_op_error!(
  #[doc = "An error that occurs when trying to write to the buffer."]
  #[error(
    "Not enough bytes available to write value (requested {requested} but only {available} available)"
  )]
  write
);

/// An error that occurs when trying to create a segment from the read buffer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Segment range out of bounds (range {start}..{end} but only {buffer_len} is available)")]
pub struct TrySegmentError {
  start: usize,
  end: usize,
  buffer_len: usize,
}

impl TrySegmentError {
  /// Creates a new `TrySegmentError`.
  #[inline]
  pub const fn new(start: usize, end: usize, buffer_len: usize) -> Self {
    Self {
      start,
      end,
      buffer_len,
    }
  }

  /// Returns the start of the requested range.
  #[inline]
  pub const fn start(&self) -> usize {
    self.start
  }

  /// Returns the end of the requested range.
  #[inline]
  pub const fn end(&self) -> usize {
    self.end
  }

  /// Returns the length of the buffer.
  #[inline]
  pub const fn available(&self) -> usize {
    self.buffer_len
  }
}

#[cfg(feature = "std")]
impl From<TrySegmentError> for std::io::Error {
  fn from(e: TrySegmentError) -> Self {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
  }
}

/// The error type returned when resizing a write buffer fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryResizeError {
  new_len: usize,
  current_len: usize,
  fill_value: u8,
}

impl core::fmt::Display for TryResizeError {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    if self.new_len > self.current_len {
      write!(
        f,
        "Cannot resize buffer to {} bytes with value {}, current length is {} bytes",
        self.new_len, self.fill_value, self.current_len
      )
    } else {
      write!(
        f,
        "Cannot shrink buffer to {} bytes, current length is {} bytes",
        self.new_len, self.current_len
      )
    }
  }
}

impl core::error::Error for TryResizeError {}

#[cfg(feature = "std")]
impl From<TryResizeError> for std::io::Error {
  fn from(e: TryResizeError) -> Self {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
  }
}

impl TryResizeError {
  /// Creates a new `ResizeError` instance.
  #[inline]
  pub const fn new(new_len: usize, current_len: usize, fill_value: u8) -> Self {
    Self {
      new_len,
      current_len,
      fill_value,
    }
  }

  /// Returns the new length of the resize error.
  #[inline]
  pub const fn new_len(&self) -> usize {
    self.new_len
  }

  /// Returns the current length of the resize error.
  #[inline]
  pub const fn current_len(&self) -> usize {
    self.current_len
  }

  /// Returns the fill value of the resize error.
  #[inline]
  pub const fn fill_value(&self) -> u8 {
    self.fill_value
  }
}

/// An error that occurs when trying to read or write a value at an offset that is out of bounds for the buffer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Offset {offset} is out of bounds for buffer length {length}")]
pub struct OutOfBounds {
  offset: usize,
  length: usize,
}

impl OutOfBounds {
  /// Creates a new `OutOfBounds` error.
  #[inline]
  pub const fn new(offset: usize, length: usize) -> Self {
    Self { offset, length }
  }

  /// Returns the offset that caused the error.
  #[inline]
  pub const fn offset(&self) -> usize {
    self.offset
  }

  /// Returns the length of the buffer.
  #[inline]
  pub const fn length(&self) -> usize {
    self.length
  }
}

#[cfg(feature = "std")]
impl From<OutOfBounds> for std::io::Error {
  fn from(e: OutOfBounds) -> Self {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
  }
}

/// An error that occurs when trying to write at a specific offset in the buffer.
///
/// This error is returned when the offset is out of bounds or when there is insufficient space to write the requested data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TryWriteAtError {
  /// An error that occurs when trying to write at an offset that is out of bounds for the buffer.
  #[error(transparent)]
  OutOfBounds(#[from] OutOfBounds),
  /// An error that occurs when there is not enough space in the buffer to write the requested data.
  #[error("Not enough bytes available to write value (requested {requested} but only {available} available at offset {offset})")]
  InsufficientSpace {
    /// The number of bytes requested to write.
    requested: usize,
    /// The number of bytes available in the buffer.
    available: usize,
    /// The offset at which the write was attempted.
    offset: usize,
  },
}

impl TryWriteAtError {
  /// Creates a new `TryWriteAtError::OutOfBounds` error.
  #[inline]
  pub const fn out_of_bounds(offset: usize, length: usize) -> Self {
    Self::OutOfBounds(OutOfBounds::new(offset, length))
  }

  /// Creates a new `TryWriteAtError::Insufficient` error.
  #[inline]
  pub const fn insufficient_space(requested: usize, available: usize, offset: usize) -> Self {
    Self::InsufficientSpace {
      requested,
      available,
      offset,
    }
  }
}

#[cfg(feature = "std")]
impl From<TryWriteAtError> for std::io::Error {
  fn from(e: TryWriteAtError) -> Self {
    match e {
      TryWriteAtError::OutOfBounds(e) => std::io::Error::new(std::io::ErrorKind::InvalidInput, e),
      TryWriteAtError::InsufficientSpace { .. } => {
        std::io::Error::new(std::io::ErrorKind::UnexpectedEof, e)
      }
    }
  }
}

/// An error that occurs when trying to write type in LEB128 format at a specific offset in the buffer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
#[cfg(feature = "varing")]
#[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
pub enum WriteVarintAtError {
  /// The offset is out of bounds for the buffer length.
  #[error(transparent)]
  OutOfBounds(#[from] OutOfBounds),
  /// The buffer does not have enough capacity to encode the value.
  #[error("Not enough bytes available to write value (requested {requested} but only {available} available at offset {offset})")]
  InsufficientSpace {
    /// The number of bytes requested to write.
    requested: usize,
    /// The number of bytes available in the buffer.
    available: usize,
    /// The offset at which the write was attempted.
    offset: usize,
  },
  /// A custom error message.
  #[error("{0}")]
  Custom(&'static str),
}

#[cfg(feature = "varing")]
impl WriteVarintAtError {
  /// Creates a new `WriteVarintAtError::OutOfBounds` error.
  #[inline]
  pub const fn out_of_bounds(offset: usize, length: usize) -> Self {
    Self::OutOfBounds(OutOfBounds::new(offset, length))
  }

  /// Creates a new `WriteVarintAtError::Insufficient` error.
  #[inline]
  pub const fn insufficient_space(requested: usize, available: usize, offset: usize) -> Self {
    Self::InsufficientSpace {
      requested,
      available,
      offset,
    }
  }

  /// Creates a new `WriteVarintAtError::Custom` error.
  #[inline]
  pub const fn custom(msg: &'static str) -> Self {
    Self::Custom(msg)
  }
}

#[cfg(all(feature = "varing", feature = "std"))]
impl From<WriteVarintAtError> for std::io::Error {
  fn from(e: WriteVarintAtError) -> Self {
    match e {
      WriteVarintAtError::OutOfBounds(e) => {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
      }
      WriteVarintAtError::InsufficientSpace {
        available,
        offset,
        ..
      } => {
        if (offset >= available) {
          std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
        } else {
          std::io::Error::new(std::io::ErrorKind::WriteZero, e)
        }
      }
      WriteVarintAtError::Custom(msg) => std::io::Error::other(msg),
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
