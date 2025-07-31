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

#[cfg(feature = "std")]
impl From<TryAdvanceError> for std::io::Error {
  fn from(e: TryAdvanceError) -> Self {
    std::io::Error::new(std::io::ErrorKind::UnexpectedEof, e)
  }
}

try_op_error!(
  #[doc = "An error that occurs when trying to read a value from the buffer."]
  #[error(
    "Not enough bytes available to read value (requested {requested} but only {available} available)"
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
  #[doc = "An error that occurs when trying to peek a value from the buffer."]
  #[error(
    "Not enough bytes available to peek value (requested {requested} but only {available} available)"
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
    TryReadError::new(e.requested, e.available)
  }
}

try_op_error!(
  #[doc = "An error that occurs when trying to write to the buffer."]
  #[error(
    "Not enough space available to write value (requested {requested} but only {available} available)"
  )]
  write
);

#[cfg(feature = "std")]
impl From<TryWriteError> for std::io::Error {
  fn from(e: TryWriteError) -> Self {
    std::io::Error::new(std::io::ErrorKind::WriteZero, e)
  }
}

/// An error that occurs when trying to create a segment from the read buffer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Segment range out of bounds (range {start}..{end} but only {available} is available)")]
pub struct TrySegmentError {
  start: usize,
  end: usize,
  available: usize,
}

impl TrySegmentError {
  /// Creates a new `TrySegmentError`.
  #[inline]
  pub const fn new(start: usize, end: usize, available: usize) -> Self {
    Self {
      start,
      end,
      available,
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
    self.available
  }
}

#[cfg(feature = "std")]
impl From<TrySegmentError> for std::io::Error {
  fn from(e: TrySegmentError) -> Self {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
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
      TryWriteAtError::InsufficientSpace {
        available, offset, ..
      } => {
        if offset >= available {
          std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
        } else {
          std::io::Error::new(std::io::ErrorKind::WriteZero, e)
        }
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

  /// Creates a new `WriteVarintAtError` error from `WriteVarintError`.
  #[inline]
  pub const fn from_write_varint_error(err: WriteVarintError, offset: usize) -> Self {
    match err {
      WriteVarintError::InsufficientSpace {
        requested,
        available,
      } => Self::insufficient_space(requested, available, offset),
      WriteVarintError::Custom(msg) => Self::custom(msg),
      _ => Self::Custom("Unknown error"),
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
        available, offset, ..
      } => {
        if offset >= available {
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
