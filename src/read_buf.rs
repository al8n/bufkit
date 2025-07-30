use super::error::{
  TryAdvanceError, TryPeekError, TryReadError, TrySegmentError, TrySplitOffError, TrySplitToError,
};

use core::ops::{Bound, RangeBounds};

#[cfg(feature = "varing")]
use varing::{DecodeError as ReadVarintError, Varint};

macro_rules! peek_fixed {
  ($($ty:ident), +$(,)?) => {
    paste::paste! {
      $(
        #[doc = "Peeks a `" $ty "` value from the buffer in little-endian byte order without advancing the cursor."]
        ///
        /// Returns the decoded value. The buffer position remains unchanged after this operation.
        ///
        /// # Panics
        ///
        #[doc = "Panics if the buffer has fewer than `size_of::<" $ty ">()` bytes available."]
        /// Use the `*_checked` or `try_*` variants for non-panicking peeks.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12, 0x78, 0x56];
        /// let buf = &data[..];
        #[doc = "assert_eq!(buf.peek_" $ty "_le(), 0x" $ty "::from_le_bytes([0x34, 0x12, ...]));"]
        /// assert_eq!(buf.available(), 4); // Cursor unchanged
        /// ```
        #[inline]
        fn [<peek_ $ty _le>](&self) -> $ty {
          <$ty>::from_le_bytes(self.peek_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in little-endian byte order without advancing the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`peek_" $ty "_le`](ReadBuf::peek_" $ty "_le)."]
        /// Returns `Some(value)` if sufficient data is available, otherwise returns `None`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let buf = &data[..];
        #[doc = "assert!(buf.peek_" $ty "_le_checked().is_some());"]
        ///
        /// let small_buf = &[0x34][..];
        #[doc = "assert!(small_buf.peek_" $ty "_le_checked().is_none()); // Not enough bytes"]
        /// ```
        #[inline]
        fn [<peek_ $ty _le_checked>](&self) -> Option<$ty> {
          self.peek_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in little-endian byte order without advancing the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`peek_" $ty "_le`](ReadBuf::peek_" $ty "_le)."]
        /// Returns `Ok(value)` on success, or `Err(TryPeekError)` with details about
        /// requested vs available bytes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let buf = &data[..];
        #[doc = "assert!(buf.try_peek_" $ty "_le().is_ok());"]
        ///
        /// let small_buf = &[0x34][..];
        #[doc = "let err = small_buf.try_peek_" $ty "_le().unwrap_err();"]
        /// // err contains details about requested vs available bytes
        /// ```
        #[inline]
        fn [<try_peek_ $ty _le>](&self) -> Result<$ty, TryPeekError> {
          self.try_peek_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in big-endian byte order without advancing the cursor."]
        ///
        /// Returns the decoded value. The buffer position remains unchanged after this operation.
        ///
        /// # Panics
        ///
        #[doc = "Panics if the buffer has fewer than `size_of::<" $ty ">()` bytes available."]
        /// Use the `*_checked` or `try_*` variants for non-panicking peeks.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x12, 0x34, 0x56, 0x78];
        /// let buf = &data[..];
        #[doc = "assert_eq!(buf.peek_" $ty "_be(), 0x" $ty "::from_be_bytes([0x12, 0x34, ...]));"]
        /// assert_eq!(buf.available(), 4); // Cursor unchanged
        /// ```
        #[inline]
        fn [<peek_ $ty _be>](&self) -> $ty {
          <$ty>::from_be_bytes(self.peek_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in big-endian byte order without advancing the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`peek_" $ty "_be`](ReadBuf::peek_" $ty "_be)."]
        /// Returns `Some(value)` if sufficient data is available, otherwise returns `None`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x12, 0x34];
        /// let buf = &data[..];
        #[doc = "assert!(buf.peek_" $ty "_be_checked().is_some());"]
        ///
        /// let small_buf = &[0x12][..];
        #[doc = "assert!(small_buf.peek_" $ty "_be_checked().is_none()); // Not enough bytes"]
        /// ```
        #[inline]
        fn [<peek_ $ty _be_checked>](&self) -> Option<$ty> {
          self.peek_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_be_bytes)
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in big-endian byte order without advancing the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`peek_" $ty "_be`](ReadBuf::peek_" $ty "_be)."]
        /// Returns `Ok(value)` on success, or `Err(TryPeekError)` with details about
        /// requested vs available bytes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x12, 0x34];
        /// let buf = &data[..];
        #[doc = "assert!(buf.try_peek_" $ty "_be().is_ok());"]
        ///
        /// let small_buf = &[0x12][..];
        #[doc = "let err = small_buf.try_peek_" $ty "_be().unwrap_err();"]
        /// // err contains details about requested vs available bytes
        /// ```
        #[inline]
        fn [<try_peek_ $ty _be>](&self) -> Result<$ty, TryPeekError> {
          self.try_peek_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_be_bytes)
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in native-endian byte order without advancing the cursor."]
        ///
        /// The byte order depends on the target platform's endianness (little-endian on x86/x64,
        /// big-endian on some embedded platforms).
        ///
        /// Returns the decoded value. The buffer position remains unchanged after this operation.
        ///
        /// # Panics
        ///
        #[doc = "Panics if the buffer has fewer than `size_of::<" $ty ">()` bytes available."]
        /// Use the `*_checked` or `try_*` variants for non-panicking peeks.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12, 0x78, 0x56];
        /// let buf = &data[..];
        #[doc = "let value = buf.peek_" $ty "_ne();"]
        /// assert_eq!(buf.available(), 4); // Cursor unchanged
        /// ```
        #[inline]
        fn [<peek_ $ty _ne>](&self) -> $ty {
          <$ty>::from_ne_bytes(self.peek_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in native-endian byte order without advancing the cursor."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`peek_" $ty "_ne`](ReadBuf::peek_" $ty "_ne)."]
        /// Returns `Some(value)` if sufficient data is available, otherwise returns `None`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let buf = &data[..];
        #[doc = "assert!(buf.peek_" $ty "_ne_checked().is_some());"]
        ///
        /// let small_buf = &[0x34][..];
        #[doc = "assert!(small_buf.peek_" $ty "_ne_checked().is_none()); // Not enough bytes"]
        /// ```
        #[inline]
        fn [<peek_ $ty _ne_checked>](&self) -> Option<$ty> {
          self.peek_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_ne_bytes)
        }

        #[doc = "Peeks a `" $ty "` value from the buffer in native-endian byte order without advancing the cursor."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`peek_" $ty "_ne`](ReadBuf::peek_" $ty "_ne)."]
        /// Returns `Ok(value)` on success, or `Err(TryPeekError)` with details about
        /// requested vs available bytes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let buf = &data[..];
        #[doc = "assert!(buf.try_peek_" $ty "_ne().is_ok());"]
        ///
        /// let small_buf = &[0x34][..];
        #[doc = "let err = small_buf.try_peek_" $ty "_ne().unwrap_err();"]
        /// // err contains details about requested vs available bytes
        /// ```
        #[inline]
        fn [<try_peek_ $ty _ne>](&self) -> Result<$ty, TryPeekError> {
          self.try_peek_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_ne_bytes)
        }
      )*
    }
  };
}

macro_rules! read_fixed {
  ($($ty:ident), +$(,)?) => {
    paste::paste! {
      $(
        #[doc = "Reads a `" $ty "` value from the buffer in little-endian byte order and advances the cursor."]
        ///
        #[doc = "Returns the decoded value and advances the cursor by `size_of::<" $ty ">()` bytes."]
        ///
        /// # Panics
        ///
        #[doc = "Panics if the buffer has fewer than `size_of::<" $ty ">()` bytes available."]
        /// Use the `*_checked` or `try_*` variants for non-panicking reads.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12, 0x78, 0x56];
        /// let mut buf = &data[..];
        #[doc = "let value = buf.read_" $ty "_le();"]
        #[doc = "assert_eq!(buf.available(), 4 - size_of::<" $ty ">()); // Cursor advanced"]
        /// ```
        #[inline]
        fn [<read_ $ty _le>](&mut self) -> $ty {
          <$ty>::from_le_bytes(self.read_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Reads a `" $ty "` value from the buffer in little-endian byte order and advances the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`read_" $ty "_le`](ReadBuf::read_" $ty "_le)."]
        /// Returns `Some(value)` and advances the cursor on success, or `None` if insufficient data.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let mut buf = &data[..];
        #[doc = "if let Some(value) = buf.read_" $ty "_le_checked() {"]
        #[doc = "    // Cursor advanced by size_of::<" $ty ">()"]
        /// } else {
        ///     // Not enough data, cursor unchanged
        /// }
        /// ```
        #[inline]
        fn [<read_ $ty _le_checked>](&mut self) -> Option<$ty> {
          self.read_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Reads a `" $ty "` value from the buffer in little-endian byte order and advances the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`read_" $ty "_le`](ReadBuf::read_" $ty "_le)."]
        /// Returns `Ok(value)` and advances the cursor on success, or `Err(TryReadError)` 
        /// with details about requested vs available bytes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let mut buf = &data[..];
        #[doc = "match buf.try_read_" $ty "_le() {"]
        ///     Ok(value) => {
        #[doc = "        // Cursor advanced by size_of::<" $ty ">()"]
        ///     },
        ///     Err(e) => {
        ///         // e contains details about requested vs available bytes
        ///     }
        /// }
        /// ```
        #[inline]
        fn [<try_read_ $ty _le>](&mut self) -> Result<$ty, TryReadError> {
          self.try_read_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Reads a `" $ty "` value from the buffer in big-endian byte order and advances the cursor."]
        ///
        #[doc = "Returns the decoded value and advances the cursor by `size_of::<" $ty ">()` bytes."]
        ///
        /// # Panics
        ///
        #[doc = "Panics if the buffer has fewer than `size_of::<" $ty ">()` bytes available."]
        /// Use the `*_checked` or `try_*` variants for non-panicking reads.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x12, 0x34, 0x56, 0x78];
        /// let mut buf = &data[..];
        #[doc = "let value = buf.read_" $ty "_be();"]
        #[doc = "assert_eq!(buf.available(), 4 - size_of::<" $ty ">()); // Cursor advanced"]
        /// ```
        #[inline]
        fn [<read_ $ty _be>](&mut self) -> $ty {
          <$ty>::from_be_bytes(self.read_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Reads a `" $ty "` value from the buffer in big-endian byte order and advances the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`read_" $ty "_be`](ReadBuf::read_" $ty "_be)."]
        /// Returns `Some(value)` and advances the cursor on success, or `None` if insufficient data.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x12, 0x34];
        /// let mut buf = &data[..];
        #[doc = "if let Some(value) = buf.read_" $ty "_be_checked() {"]
        #[doc = "    // Cursor advanced by size_of::<" $ty ">()"]
        /// } else {
        ///     // Not enough data, cursor unchanged
        /// }
        /// ```
        #[inline]
        fn [<read_ $ty _be_checked>](&mut self) -> Option<$ty> {
          self.read_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_be_bytes)
        }

        #[doc = "Reads a `" $ty "` value from the buffer in big-endian byte order and advances the cursor."]
        ///
        #[doc = "This is the non-panicking version of [`read_" $ty "_be`](ReadBuf::read_" $ty "_be)."]
        /// Returns `Ok(value)` and advances the cursor on success, or `Err(TryReadError)` 
        /// with details about requested vs available bytes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x12, 0x34];
        /// let mut buf = &data[..];
        #[doc = "match buf.try_read_" $ty "_be() {"]
        ///     Ok(value) => {
        #[doc = "        // Cursor advanced by size_of::<" $ty ">()"]
        ///     },
        ///     Err(e) => {
        ///         // e contains details about requested vs available bytes
        ///     }
        /// }
        /// ```
        #[inline]
        fn [<try_read_ $ty _be>](&mut self) -> Result<$ty, TryReadError> {
          self.try_read_array::<{ core::mem::size_of::<$ty>() }>().map(|val| { <$ty>::from_be_bytes(val) })
        }

        #[doc = "Reads a `" $ty "` value from the buffer in native-endian byte order and advances the cursor."]
        ///
        /// The byte order depends on the target platform's endianness (little-endian on x86/x64,
        /// big-endian on some embedded platforms).
        ///
        #[doc = "Returns the decoded value and advances the cursor by `size_of::<" $ty ">()` bytes."]
        ///
        /// # Panics
        ///
        #[doc = "Panics if the buffer has fewer than `size_of::<" $ty ">()` bytes available."]
        /// Use the `*_checked` or `try_*` variants for non-panicking reads.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12, 0x78, 0x56];
        /// let mut buf = &data[..];
        #[doc = "let value = buf.read_" $ty "_ne();"]
        #[doc = "assert_eq!(buf.available(), 4 - size_of::<" $ty ">()); // Cursor advanced"]
        /// ```
        #[inline]
        fn [<read_ $ty _ne>](&mut self) -> $ty {
          <$ty>::from_ne_bytes(self.read_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Reads a `" $ty "` value from the buffer in native-endian byte order and advances the cursor."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`read_" $ty "_ne`](ReadBuf::read_" $ty "_ne)."]
        /// Returns `Some(value)` and advances the cursor on success, or `None` if insufficient data.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let mut buf = &data[..];
        #[doc = "if let Some(value) = buf.read_" $ty "_ne_checked() {"]
        #[doc = "    // Cursor advanced by size_of::<" $ty ">()"]
        /// } else {
        ///     // Not enough data, cursor unchanged
        /// }
        /// ```
        #[inline]
        fn [<read_ $ty _ne_checked>](&mut self) -> Option<$ty> {
          self.read_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_ne_bytes)
        }

        #[doc = "Reads a `" $ty "` value from the buffer in native-endian byte order and advances the cursor."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`read_" $ty "_ne`](ReadBuf::read_" $ty "_ne)."]
        /// Returns `Ok(value)` and advances the cursor on success, or `Err(TryReadError)` 
        /// with details about requested vs available bytes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::ReadBuf;
        ///
        /// let data = [0x34, 0x12];
        /// let mut buf = &data[..];
        #[doc = "match buf.try_read_" $ty "_ne() {"]
        ///     Ok(value) => {
        #[doc = "        // Cursor advanced by size_of::<" $ty ">()"]
        ///     },
        ///     Err(e) => {
        ///         // e contains details about requested vs available bytes
        ///     }
        /// }
        /// ```
        #[inline]
        fn [<try_read_ $ty _ne>](&mut self) -> Result<$ty, TryReadError> {
          self.try_read_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_ne_bytes)
        }
      )*
    }
  };
}

/// A trait for implementing custom buffers that can read and navigate through byte sequences.
///
/// This trait provides a comprehensive set of methods for reading data from buffers with different
/// error handling strategies:
/// - **Panicking methods** (e.g., `read_*`): Fast operations that panic on insufficient data
/// - **Checked methods** (e.g., `*_checked`): Return `Option` - `None` on failure, `Some(value)` on success
/// - **Fallible methods** (e.g., `try_*`): Return `Result` with detailed error information
///
/// # Method Categories
///
/// - **Buffer inspection**: `available()`, `has_available()`, `buffer()`
/// - **Navigation**: `advance()`, `try_advance()`
/// - **Buffer manipulation**: `truncate()`, `split_to()`, `split_off()`, `segment()`
/// - **Peeking data**: `peek_u8()`, `peek_u16_le()`, etc. (read without advancing)
/// - **Reading data**: `read_u8()`, `read_u16_le()`, etc. (read and advance cursor)
pub trait ReadBuf {
  /// Returns an empty read buffer.
  ///
  /// Creates a new buffer instance with no data available for reading.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let buf = <&[u8]>::empty();
  /// assert_eq!(buf.available(), 0);
  /// assert!(!buf.has_available());
  /// ```
  fn empty() -> Self
  where
    Self: Sized;

  /// Returns the number of bytes available for reading in the buffer.
  ///
  /// This represents how many bytes can be read from the current cursor position
  /// to the end of the buffer.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  /// assert_eq!(buf.available(), 5);
  ///
  /// buf.advance(2);
  /// assert_eq!(buf.available(), 3);
  /// ```
  fn available(&self) -> usize;

  /// Returns the remaining bytes of the buffer as a slice.
  ///
  /// This provides direct access to all bytes from the current cursor position
  /// to the end of the buffer.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  /// assert_eq!(buf.buffer(), &[1, 2, 3, 4, 5]);
  ///
  /// buf.advance(2);
  /// assert_eq!(buf.buffer(), &[3, 4, 5]);
  /// ```
  fn buffer(&self) -> &[u8];

  /// Advances the internal cursor by the specified number of bytes.
  ///
  /// This moves the read position forward, making the advanced bytes no longer
  /// available for reading. The operation consumes the bytes without returning them.
  ///
  /// # Panics
  ///
  /// Panics if `cnt > self.available()`.
  /// Use [`try_advance`](ReadBuf::try_advance) for non-panicking advancement.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  /// 
  /// buf.advance(2);
  /// assert_eq!(buf.available(), 3);
  /// assert_eq!(buf.buffer(), &[3, 4, 5]);
  /// ```
  fn advance(&mut self, cnt: usize);

  /// Creates an independent buffer containing a segment of the current buffer's data.
  ///
  /// This method returns a new buffer instance that represents a portion of the current
  /// buffer defined by the given range. The original buffer remains unchanged,
  /// and the new buffer has its own independent cursor starting at the beginning of the segment.
  ///
  /// # Panics
  ///
  /// Panics if the range is out of bounds relative to the current buffer's available data.
  /// Use [`try_segment`](ReadBuf::try_segment) for non-panicking segmentation.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = b"Hello, World!";
  /// let buf = &data[..];
  ///
  /// let hello = buf.segment(0..5);
  /// let world = buf.segment(7..12);
  ///
  /// assert_eq!(hello.buffer(), b"Hello");
  /// assert_eq!(world.buffer(), b"World");
  /// // Original buffer unchanged
  /// assert_eq!(buf.available(), 13);
  /// ```
  fn segment(&self, range: impl RangeBounds<usize>) -> Self
  where
    Self: Sized;

  /// Shortens the buffer to the specified length, keeping the first `len` bytes.
  ///
  /// If `len` is greater than the buffer's current available bytes, this has no effect.
  /// This operation cannot fail and will never panic.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// buf.truncate(3);
  /// assert_eq!(buf.available(), 3);
  /// assert_eq!(buf.buffer(), &[1, 2, 3]);
  ///
  /// // Truncating to a length >= available has no effect
  /// buf.truncate(10);
  /// assert_eq!(buf.available(), 3);
  /// ```
  fn truncate(&mut self, len: usize);

  /// Splits the buffer into two at the given index.
  ///
  /// Afterwards `self` contains elements `[0, at)`, and the returned buffer
  /// contains elements `[at, available())`. The memory layout remains unchanged.
  ///
  /// **Implementor Notes:** This should be an `O(1)` operation.
  ///
  /// # Panics
  ///
  /// Panics if `at > self.available()`.
  /// Use [`split_off_checked`](ReadBuf::split_off_checked) or 
  /// [`try_split_off`](ReadBuf::try_split_off) for non-panicking splits.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// let tail = buf.split_off(2);
  /// assert_eq!(buf.buffer(), &[1, 2]);
  /// assert_eq!(tail.buffer(), &[3, 4, 5]);
  /// ```
  #[must_use = "consider ReadBuf::truncate if you don't need the other half"]
  fn split_off(&mut self, at: usize) -> Self
  where
    Self: Sized;

  /// Splits the buffer into two at the given index.
  ///
  /// This is the non-panicking version of [`split_off`](ReadBuf::split_off).
  /// Returns `Some((left, right))` if `at <= self.available()`, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// assert!(buf.split_off_checked(2).is_some());
  /// 
  /// let mut small_buf = &[1u8][..];
  /// assert!(small_buf.split_off_checked(5).is_none());
  /// ```
  #[must_use = "consider ReadBuf::truncate if you don't need the other half"]
  fn split_off_checked(&mut self, at: usize) -> Option<Self>
  where
    Self: Sized,
  {
    if at > self.available() {
      None
    } else {
      Some(self.split_off(at))
    }
  }

  /// Splits the buffer into two at the given index.
  ///
  /// This is the non-panicking version of [`split_off`](ReadBuf::split_off) that
  /// returns detailed error information on failure.
  /// Returns `Ok(right_half)` on success, or `Err(TrySplitOffError)` with details about
  /// the attempted split position and available bytes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// assert!(buf.try_split_off(2).is_ok());
  ///
  /// let mut small_buf = &[1u8][..];
  /// let err = small_buf.try_split_off(5).unwrap_err();
  /// // err contains details about requested vs available
  /// ```
  #[must_use = "consider ReadBuf::try_split_off if you don't need the other half"]
  fn try_split_off(&mut self, at: usize) -> Result<Self, TrySplitOffError>
  where
    Self: Sized,
  {
    if at > self.available() {
      Err(TrySplitOffError::new(at + 1, self.available()))
    } else {
      Ok(self.split_off(at))
    }
  }

  /// Splits the buffer into two at the given index.
  ///
  /// Afterwards `self` contains elements `[at, available())`, and the returned
  /// buffer contains elements `[0, at)`.
  ///
  /// **Implementor Notes:** This should be an `O(1)` operation.
  ///
  /// # Panics
  ///
  /// Panics if `at > self.available()`.
  /// Use [`split_to_checked`](ReadBuf::split_to_checked) or
  /// [`try_split_to`](ReadBuf::try_split_to) for non-panicking splits.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = b"hello world";
  /// let mut buf = &data[..];
  ///
  /// let hello = buf.split_to(5);
  /// assert_eq!(hello.buffer(), b"hello");
  /// assert_eq!(buf.buffer(), b" world");
  /// ```
  #[must_use = "consider ReadBuf::advance if you don't need the other half"]
  fn split_to(&mut self, at: usize) -> Self
  where
    Self: Sized;

  /// Splits the buffer into two at the given index.
  ///
  /// This is the non-panicking version of [`split_to`](ReadBuf::split_to).
  /// Returns `Some(left_half)` if `at <= self.available()`, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// assert!(buf.split_to_checked(3).is_some());
  /// assert!(buf.split_to_checked(10).is_none());
  /// ```
  #[must_use = "consider ReadBuf::advance if you don't need the other half"]
  fn split_to_checked(&mut self, at: usize) -> Option<Self>
  where
    Self: Sized,
  {
    if at > self.available() {
      None
    } else {
      Some(self.split_to(at))
    }
  }

  /// Splits the buffer into two at the given index.
  ///
  /// This is the non-panicking version of [`split_to`](ReadBuf::split_to) that
  /// returns detailed error information on failure.
  /// Returns `Ok(left_half)` on success, or `Err(TrySplitToError)` with details about
  /// the attempted split position and available bytes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// assert!(buf.try_split_to(3).is_ok());
  ///
  /// let err = buf.try_split_to(10).unwrap_err();
  /// // err contains detailed information about the failure
  /// ```
  #[must_use = "consider ReadBuf::try_split_to if you don't need the other half"]
  fn try_split_to(&mut self, at: usize) -> Result<Self, TrySplitToError>
  where
    Self: Sized,
  {
    if at > self.available() {
      Err(TrySplitToError::new(at + 1, self.available()))
    } else {
      Ok(self.split_to(at))
    }
  }

  /// Returns `true` if there are bytes available for reading in the buffer.
  ///
  /// This is equivalent to `self.available() > 0`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3];
  /// let mut buf = &data[..];
  /// assert!(buf.has_available());
  ///
  /// buf.advance(3);
  /// assert!(!buf.has_available());
  /// ```
  fn has_available(&self) -> bool {
    self.available() > 0
  }

  /// Attempts to advance the internal cursor by the specified number of bytes.
  ///
  /// This is the non-panicking version of [`advance`](ReadBuf::advance).
  /// Returns `Ok(())` if the advancement was successful, or `Err(TryAdvanceError)` 
  /// with details about requested vs available bytes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// assert!(buf.try_advance(3).is_ok());
  /// assert_eq!(buf.available(), 2);
  ///
  /// let err = buf.try_advance(5).unwrap_err();
  /// // err contains details about requested vs available
  /// ```
  fn try_advance(&mut self, cnt: usize) -> Result<(), TryAdvanceError> {
    let remaining = self.available();
    if remaining < cnt {
      return Err(TryAdvanceError::new(cnt, remaining));
    }

    self.advance(cnt);
    Ok(())
  }

  /// Attempts to create a new buffer containing a segment of the current buffer's data.
  ///
  /// The returned buffer is independent with its own cursor starting at the beginning of the segment.
  /// The original buffer remains unchanged. This is the non-panicking version of 
  /// [`segment`](ReadBuf::segment).
  ///
  /// Returns `Ok(segment)` if the range is valid, or `Err(TrySegmentError)` if the range
  /// extends beyond the current buffer's available data.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = b"Hello, World!";
  /// let buf = &data[..];
  ///
  /// assert!(buf.try_segment(0..5).is_ok());
  /// assert!(buf.try_segment(0..20).is_err()); // Out of bounds
  /// ```
  #[inline]
  fn try_segment(&self, range: impl RangeBounds<usize>) -> Result<Self, TrySegmentError>
  where
    Self: Sized,
  {
    check_segment(range, self.available()).map(|(start, end)| self.segment(start..end))
  }

  /// Peeks a fixed-size array from the beginning of the buffer without advancing the cursor.
  ///
  /// This method creates a copy of the first `N` bytes from the buffer without
  /// consuming them. The buffer position remains unchanged after this operation.
  ///
  /// # Panics
  ///
  /// Panics if the buffer contains fewer than `N` bytes.
  /// Use [`peek_array_checked`](ReadBuf::peek_array_checked) or
  /// [`try_peek_array`](ReadBuf::try_peek_array) for non-panicking peeks.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let buf = &data[..];
  ///
  /// let first_three: [u8; 3] = buf.peek_array();
  /// assert_eq!(first_three, [1, 2, 3]);
  /// // Buffer unchanged
  /// assert_eq!(buf.available(), 5);
  /// ```
  #[inline]
  fn peek_array<const N: usize>(&self) -> [u8; N] {
    self.buffer().try_into().expect("buffer too short")
  }

  /// Peeks a fixed-size array from the beginning of the buffer without advancing the cursor.
  ///
  /// This is the non-panicking version of [`peek_array`](ReadBuf::peek_array).
  /// Returns `Some(array)` if sufficient data is available, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3];
  /// let buf = &data[..];
  ///
  /// assert!(buf.peek_array_checked::<2>().is_some());
  /// assert!(buf.peek_array_checked::<5>().is_none());
  /// ```
  #[inline]
  fn peek_array_checked<const N: usize>(&self) -> Option<[u8; N]> {
    match self.buffer().try_into() {
      Ok(data) => Some(data),
      Err(_) => None,
    }
  }

  /// Peeks a fixed-size array from the beginning of the buffer without advancing the cursor.
  ///
  /// This is the non-panicking version of [`peek_array`](ReadBuf::peek_array) that
  /// returns detailed error information on failure.
  /// Returns `Ok(array)` on success, or `Err(TryPeekError)` with details about
  /// requested vs available bytes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3];
  /// let buf = &data[..];
  ///
  /// assert!(buf.try_peek_array::<2>().is_ok());
  ///
  /// let err = buf.try_peek_array::<5>().unwrap_err();
  /// // err contains details about requested vs available
  /// ```
  #[inline]
  fn try_peek_array<const N: usize>(&self) -> Result<[u8; N], TryPeekError> {
    match self.buffer().try_into() {
      Ok(data) => Ok(data),
      Err(_) => Err(TryPeekError::new(N, self.available())),
    }
  }

  // Macro generates peek methods for primitive types
  peek_fixed!(u16, u32, u64, u128, i16, i32, i64, i128, f32, f64);

  /// Reads a fixed-size array from the buffer and advances the internal cursor.
  ///
  /// This method creates a copy of the first `N` bytes from the buffer and
  /// advances the cursor by `N` bytes, consuming the data.
  ///
  /// # Panics
  ///
  /// Panics if the buffer contains fewer than `N` bytes.
  /// Use [`read_array_checked`](ReadBuf::read_array_checked) or
  /// [`try_read_array`](ReadBuf::try_read_array) for non-panicking reads.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let mut buf = &data[..];
  ///
  /// let first_three: [u8; 3] = buf.read_array();
  /// assert_eq!(first_three, [1, 2, 3]);
  /// assert_eq!(buf.available(), 2); // Cursor advanced
  /// ```
  #[inline]
  fn read_array<const N: usize>(&mut self) -> [u8; N] {
    let output = self.buffer().try_into().expect("buffer too short");
    self.advance(N);
    output
  }

  /// Reads a fixed-size array from the buffer and advances the internal cursor.
  ///
  /// This is the non-panicking version of [`read_array`](ReadBuf::read_array).
  /// Returns `Some(array)` and advances the cursor on success, or `None` if insufficient data.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3];
  /// let mut buf = &data[..];
  ///
  /// assert!(buf.read_array_checked::<2>().is_some());
  /// assert_eq!(buf.available(), 1);
  ///
  /// assert!(buf.read_array_checked::<2>().is_none());
  /// assert_eq!(buf.available(), 1); // Cursor not advanced on failure
  /// ```
  #[inline]
  fn read_array_checked<const N: usize>(&mut self) -> Option<[u8; N]> {
    match self.buffer().try_into() {
      Ok(data) => {
        self.advance(N);
        Some(data)
      }
      Err(_) => None,
    }
  }

  /// Reads a fixed-size array from the buffer and advances the internal cursor.
  ///
  /// This is the non-panicking version of [`read_array`](ReadBuf::read_array) that
  /// returns detailed error information on failure.
  /// Returns `Ok(array)` and advances the cursor on success, or `Err(TryReadError)` 
  /// with details about requested vs available bytes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3];
  /// let mut buf = &data[..];
  ///
  /// assert!(buf.try_read_array::<2>().is_ok());
  /// assert_eq!(buf.available(), 1);
  ///
  /// let err = buf.try_read_array::<2>().unwrap_err();
  /// // err contains details about requested vs available
  /// ```
  #[inline]
  fn try_read_array<const N: usize>(&mut self) -> Result<[u8; N], TryReadError> {
    match self.buffer().try_into() {
      Ok(data) => {
        self.advance(N);
        Ok(data)
      }
      Err(_) => Err(TryReadError::new(N, self.available())),
    }
  }

  // Macro generates read methods for primitive types
  read_fixed!(u16, u32, u64, u128, i16, i32, i64, i128, f32, f64);

  /// Peeks a `u8` value from the buffer without advancing the internal cursor.
  ///
  /// Returns the first byte from the buffer without consuming it.
  /// The buffer position remains unchanged after this operation.
  ///
  /// # Panics
  ///
  /// Panics if the buffer is empty.
  /// Use [`peek_u8_checked`](ReadBuf::peek_u8_checked) for non-panicking peeks.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [42, 1, 2, 3];
  /// let buf = &data[..];
  ///
  /// assert_eq!(buf.peek_u8(), 42);
  /// assert_eq!(buf.available(), 4); // Unchanged
  /// ```
  #[inline]
  fn peek_u8(&self) -> u8 {
    self.buffer()[0]
  }

  /// Peeks a `u8` value from the buffer without advancing the internal cursor.
  ///
  /// This is the non-panicking version of [`peek_u8`](ReadBuf::peek_u8).
  /// Returns `Some(byte)` if data is available, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [42];
  /// let buf = &data[..];
  /// assert_eq!(buf.peek_u8_checked(), Some(42));
  ///
  /// let empty_buf = &[][..];
  /// assert_eq!(empty_buf.peek_u8_checked(), None);
  /// ```
  #[inline]
  fn peek_u8_checked(&self) -> Option<u8> {
    self.buffer().get(0).copied()
  }

  /// Reads a `u8` value from the buffer and advances the internal cursor.
  ///
  /// Returns the first byte from the buffer and advances the cursor by 1 byte.
  ///
  /// # Panics
  ///
  /// Panics if the buffer is empty.
  /// Use [`read_u8_checked`](ReadBuf::read_u8_checked) for non-panicking reads.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [42, 1, 2, 3];
  /// let mut buf = &data[..];
  ///
  /// assert_eq!(buf.read_u8(), 42);
  /// assert_eq!(buf.available(), 3); // Cursor advanced
  /// ```
  #[inline]
  fn read_u8(&mut self) -> u8 {
    let val = self.peek_u8();
    self.advance(1);
    val
  }

  /// Reads a `u8` value from the buffer and advances the internal cursor.
  ///
  /// This is the non-panicking version of [`read_u8`](ReadBuf::read_u8).
  /// Returns `Some(byte)` and advances the cursor on success, or `None` if the buffer is empty.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [42];
  /// let mut buf = &data[..];
  ///
  /// assert_eq!(buf.read_u8_checked(), Some(42));
  /// assert_eq!(buf.available(), 0);
  ///
  /// assert_eq!(buf.read_u8_checked(), None); // Empty now
  /// ```
  #[inline]
  fn read_u8_checked(&mut self) -> Option<u8> {
    self.peek_u8_checked().inspect(|_| {
      self.advance(1);
    })
  }

  /// Peeks an `i8` value from the buffer without advancing the internal cursor.
  ///
  /// Returns the first byte from the buffer as a signed integer without consuming it.
  /// The buffer position remains unchanged after this operation.
  ///
  /// # Panics
  ///
  /// Panics if the buffer is empty.
  /// Use [`peek_i8_checked`](ReadBuf::peek_i8_checked) for non-panicking peeks.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [255u8, 1, 2, 3]; // 255 as i8 is -1
  /// let buf = &data[..];
  ///
  /// assert_eq!(buf.peek_i8(), -1);
  /// assert_eq!(buf.available(), 4); // Unchanged
  /// ```
  #[inline]
  fn peek_i8(&self) -> i8 {
    self.peek_u8() as i8
  }

  /// Peeks an `i8` value from the buffer without advancing the internal cursor.
  ///
  /// This is the non-panicking version of [`peek_i8`](ReadBuf::peek_i8).
  /// Returns `Some(byte)` if data is available, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [255u8]; // -1 as i8
  /// let buf = &data[..];
  /// assert_eq!(buf.peek_i8_checked(), Some(-1));
  ///
  /// let empty_buf = &[][..];
  /// assert_eq!(empty_buf.peek_i8_checked(), None);
  /// ```
  #[inline]
  fn peek_i8_checked(&self) -> Option<i8> {
    self.peek_u8_checked().map(|v| v as i8)
  }

  /// Reads an `i8` value from the buffer and advances the internal cursor.
  ///
  /// Returns the first byte from the buffer as a signed integer and advances the cursor by 1 byte.
  ///
  /// # Panics
  ///
  /// Panics if the buffer is empty.
  /// Use [`read_i8_checked`](ReadBuf::read_i8_checked) for non-panicking reads.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [255u8, 1, 2, 3]; // 255 as i8 is -1
  /// let mut buf = &data[..];
  ///
  /// assert_eq!(buf.read_i8(), -1);
  /// assert_eq!(buf.available(), 3); // Cursor advanced
  /// ```
  #[inline]
  fn read_i8(&mut self) -> i8 {
    let val = self.peek_i8();
    self.advance(1);
    val
  }

  /// Reads an `i8` value from the buffer and advances the internal cursor.
  ///
  /// This is the non-panicking version of [`read_i8`](ReadBuf::read_i8).
  /// Returns `Some(byte)` and advances the cursor on success, or `None` if the buffer is empty.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [255u8]; // -1 as i8
  /// let mut buf = &data[..];
  ///
  /// assert_eq!(buf.read_i8_checked(), Some(-1));
  /// assert_eq!(buf.available(), 0);
  ///
  /// assert_eq!(buf.read_i8_checked(), None); // Empty now
  /// ```
  #[inline]
  fn read_i8_checked(&mut self) -> Option<i8> {
    self.peek_i8_checked().inspect(|_| {
      self.advance(1);
    })
  }

  /// Converts the read buffer to a `Vec<u8>` instance.
  ///
  /// Creates a new vector containing a copy of all available bytes in the buffer.
  /// The original buffer remains unchanged.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::ReadBuf;
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let buf = &data[..];
  ///
  /// let vec = buf.to_vec();
  /// assert_eq!(vec, vec![1, 2, 3, 4, 5]);
  /// ```
  #[cfg(any(feature = "std", feature = "alloc"))]
  #[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
  fn to_vec(&self) -> Vec<u8> {
    self.buffer().to_vec()
  }

  /// Converts the read buffer to a `Bytes` instance.
  ///
  /// Creates a new `Bytes` instance containing a copy of all available bytes in the buffer.
  /// The original buffer remains unchanged.
  #[cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc")))]
  #[cfg_attr(
    docsrs,
    doc(cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc"))))
  )]
  fn to_bytes(&self) -> ::bytes_1::Bytes {
    ::bytes_1::Bytes::copy_from_slice(self.buffer())
  }

  /// Converts the read buffer to a `BytesMut` instance.
  ///
  /// Creates a new `BytesMut` instance containing a copy of all available bytes in the buffer.
  /// The original buffer remains unchanged.
  #[cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc")))]
  #[cfg_attr(
    docsrs,
    doc(cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc"))))
  )]
  fn to_bytes_mut(&self) -> ::bytes_1::BytesMut {
    ::bytes_1::BytesMut::from(self.to_bytes())
  }
}

/// Extension trait for `ReadBuf` that provides additional methods
pub trait ReadBufExt: ReadBuf {
  /// Peeks a variable-length encoded type from the buffer without advancing the internal cursor.
  ///
  /// Returns the length of the value and the value itself.
  #[cfg(feature = "varing")]
  #[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
  #[inline]
  fn peek_varint<V: Varint>(&self) -> Result<(usize, V), ReadVarintError> {
    V::decode(self.buffer())
  }

  /// Reads a variable-length encoded type from the buffer and advances the internal cursor.
  ///
  /// Returns the length of the value read and the value itself.
  #[cfg(feature = "varing")]
  #[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
  #[inline]
  fn read_varint<V: Varint>(&mut self) -> Result<(usize, V), ReadVarintError> {
    V::decode(self.buffer()).map(|(len, val)| {
      self.advance(len);
      (len, val)
    })
  }
}

impl<T: ReadBuf> ReadBufExt for T {}

impl ReadBuf for &[u8] {
  #[inline]
  fn empty() -> Self {
    &[]
  }

  #[inline]
  fn available(&self) -> usize {
    <[u8]>::len(self)
  }

  #[inline]
  fn has_available(&self) -> bool {
    <[u8]>::is_empty(self)
  }

  #[inline]
  fn advance(&mut self, cnt: usize) {
    if self.len() < cnt {
      panic_advance(&TryAdvanceError::new(cnt, self.len()));
    }

    *self = &self[cnt..];
  }

  #[inline]
  fn try_advance(&mut self, cnt: usize) -> Result<(), TryAdvanceError> {
    if self.len() < cnt {
      return Err(TryAdvanceError::new(cnt, self.len()));
    }

    *self = &self[cnt..];
    Ok(())
  }

  #[inline]
  fn truncate(&mut self, len: usize) {
    if len > self.len() {
      return;
    }

    *self = &self[..len];
  }

  #[inline]
  fn segment(&self, range: impl RangeBounds<usize>) -> Self {
    let len = self.len();

    let begin = match range.start_bound() {
      Bound::Included(&n) => n,
      Bound::Excluded(&n) => n.checked_add(1).expect("out of range"),
      Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
      Bound::Included(&n) => n.checked_add(1).expect("out of range"),
      Bound::Excluded(&n) => n,
      Bound::Unbounded => len,
    };

    &self[begin..end]
  }

  #[inline]
  fn try_segment(&self, range: impl RangeBounds<usize>) -> Result<Self, TrySegmentError> {
    check_segment(range, self.len()).map(|(begin, end)| &self[begin..end])
  }

  #[inline]
  fn split_off(&mut self, at: usize) -> Self {
    let (left, right) = self.split_at(at);
    *self = left;
    right
  }

  #[inline]
  fn split_off_checked(&mut self, at: usize) -> Option<Self> {
    let (left, right) = self.split_at_checked(at)?;
    *self = left;
    Some(right)
  }

  #[inline]
  fn split_to(&mut self, at: usize) -> Self {
    let (left, right) = self.split_at(at);
    *self = right;
    left
  }

  #[inline]
  fn split_to_checked(&mut self, at: usize) -> Option<Self> {
    let (left, right) = self.split_at_checked(at)?;
    *self = right;
    Some(left)
  }

  #[inline]
  fn try_split_off(&mut self, at: usize) -> Result<Self, TrySplitOffError> {
    self
      .split_at_checked(at)
      .ok_or_else(|| TrySplitOffError::new(at + 1, self.len()))
      .map(|(left, right)| {
        *self = left;
        right
      })
  }

  #[inline]
  fn try_split_to(&mut self, at: usize) -> Result<Self, TrySplitToError> {
    self
      .split_at_checked(at)
      .ok_or_else(|| TrySplitToError::new(at + 1, self.len()))
      .map(|(left, right)| {
        *self = right;
        left
      })
  }

  #[inline]
  fn buffer(&self) -> &[u8] {
    self
  }
}

/// Panic with a nice error message.
#[cold]
fn panic_advance(error_info: &TryAdvanceError) -> ! {
  panic!(
    "advance out of bounds: the len is {} but advancing by {}",
    error_info.available(),
    error_info.requested()
  );
}

#[cfg(feature = "bytes_1")]
const _: () = {
  use bytes_1::{Buf, Bytes};

  macro_rules! read_fixed_specification {
    ($($ty:ident), +$(,)?) => {
      paste::paste! {
        $(
          fn [<read_ $ty _le>](&mut self) -> $ty {
            self.[<get_ $ty _le>]()
          }

          fn [<read_ $ty _le_checked>](&mut self) -> Option<$ty> {
            self.[<try_get_ $ty _le>]().ok()
          }

          fn [<try_read_ $ty _le>](&mut self) -> Result<$ty, TryReadError> {
            self.[<try_get_ $ty _le>]().map_err(Into::into)
          }

          fn [<read_ $ty _be>](&mut self) -> $ty {
            self.[<get_ $ty>]()
          }

          fn [<read_ $ty _be_checked>](&mut self) -> Option<$ty> {
            self.[<try_get_ $ty>]().ok()
          }

          fn [<try_read_ $ty _be>](&mut self) -> Result<$ty, TryReadError> {
            self.[<try_get_ $ty>]().map_err(Into::into)
          }

          fn [<read_ $ty _ne>](&mut self) -> $ty {
            self.[<get_ $ty _ne>]()
          }

          fn [<read_ $ty _ne_checked>](&mut self) -> Option<$ty> {
            self.[<try_get_ $ty _ne>]().ok()
          }

          fn [<try_read_ $ty _ne>](&mut self) -> Result<$ty, TryReadError> {
            self.[<try_get_ $ty _ne>]().map_err(Into::into)
          }
        )*
      }
    };
  }

  impl ReadBuf for Bytes {
    #[inline]
    fn empty() -> Self {
      Bytes::new()
    }

    #[inline]
    fn available(&self) -> usize {
      self.len()
    }

    #[inline]
    fn has_available(&self) -> bool {
      self.is_empty()
    }

    #[inline]
    fn buffer(&self) -> &[u8] {
      self.as_ref()
    }

    #[inline]
    fn advance(&mut self, cnt: usize) {
      bytes_1::Buf::advance(self, cnt);
    }

    #[inline]
    fn truncate(&mut self, len: usize) {
      Bytes::truncate(self, len);
    }

    #[inline]
    fn segment(&self, range: impl RangeBounds<usize>) -> Self {
      Bytes::slice(self, range)
    }

    #[inline]
    fn split_off(&mut self, at: usize) -> Self {
      Bytes::split_off(self, at)
    }

    #[inline]
    fn split_to(&mut self, at: usize) -> Self {
      Bytes::split_to(self, at)
    }

    #[inline]
    fn read_u8(&mut self) -> u8 {
      self.get_u8()
    }

    #[inline]
    fn read_u8_checked(&mut self) -> Option<u8> {
      self.try_get_u8().ok()
    }

    #[inline]
    fn read_i8(&mut self) -> i8 {
      self.get_i8()
    }

    #[inline]
    fn read_i8_checked(&mut self) -> Option<i8> {
      self.try_get_i8().ok()
    }

    #[cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc")))]
    fn to_bytes(&self) -> ::bytes_1::Bytes {
      self.clone()
    }

    read_fixed_specification!(u16, u32, u64, u128, i16, i32, i64, i128, f32, f64);
  }
};

#[inline]
fn check_segment<R: RangeBounds<usize>>(
  range: R,
  len: usize,
) -> Result<(usize, usize), TrySegmentError> {
  let begin = match range.start_bound() {
    Bound::Included(&n) => n,
    Bound::Excluded(&n) => match n.checked_add(1) {
      Some(val) => val,
      None => usize::MAX,
    },
    Bound::Unbounded => 0,
  };

  let end = match range.end_bound() {
    Bound::Included(&n) => match n.checked_add(1) {
      Some(val) => val,
      None => usize::MAX,
    },
    Bound::Excluded(&n) => n,
    Bound::Unbounded => len,
  };

  if begin > len || end > len || begin > end {
    return Err(TrySegmentError::new(begin, end, len));
  }

  Ok((begin, end))
}
