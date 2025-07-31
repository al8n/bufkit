use super::error::{TryResizeError, TryWriteAtError, TryWriteError};

#[cfg(feature = "varing")]
use super::error::WriteVarintAtError;
#[cfg(feature = "varing")]
use varing::{EncodeError as WriteVarintError, Varint};

macro_rules! put_fixed {
  ($($ty:ty),+$(,)?) => {
    paste::paste! {
      $(
        #[doc = "Writes a `" $ty "` value in little-endian byte order to the buffer at the specified offset."]
        ///
        #[doc = "Returns the number of bytes written (always `size_of::<" $ty ">()` for this type)."]
        ///
        /// # Panics
        ///
        /// Panics if `offset >= self.mutable()` or if `offset + size_of::<T>() > self.mutable()`.
        /// Use the `*_checked` or `try_*` variants for non-panicking writes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "let written = slice.put_" $ty "_le_at(0x1234 as " $ty ", 2);"]
        #[doc = "assert_eq!(written, size_of::<" $ty ">());"]
        /// // Value is written in little-endian format starting at offset 2
        /// ```
        #[inline]
        fn [< put_ $ty _le_at>](&mut self, value: $ty, offset: usize) -> usize {
          self.put_slice_at(&value.to_le_bytes(), offset)
        }

        #[doc = "Tries to write a `" $ty "` value in little-endian byte order to the buffer at the specified offset."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_le_at`](BufMut::put_" $ty "_le_at)."]
        ///
        /// Returns `Some(bytes_written)` on success, or `None` if the offset is out of bounds
        /// or there's insufficient space for the value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.put_" $ty "_le_at_checked(0x1234 as " $ty ", 2).is_some());"]
        #[doc = "assert!(slice.put_" $ty "_le_at_checked(0x1234 as " $ty ", 30).is_none()); // Out of bounds"]
        /// ```
        #[inline]
        fn [< put_ $ty _le_at_checked>](&mut self, value: $ty, offset: usize) -> Option<usize> {
          self.put_slice_at_checked(&value.to_le_bytes(), offset)
        }

        #[doc = "Tries to write a `" $ty "` value in little-endian byte order to the buffer at the specified offset."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_le_at`](BufMut::put_" $ty "_le_at)."]
        ///
        /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteAtError)` with detailed
        /// error information if the offset is out of bounds or there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.try_put_" $ty "_le_at(0x1234 as " $ty ", 2).is_ok());"]
        ///
        #[doc = "let err = slice.try_put_" $ty "_le_at(0x1234 as " $ty ", 30).unwrap_err();"]
        /// // err contains detailed information about what went wrong
        /// ```
        #[inline]
        fn [< try_put_ $ty _le_at>](&mut self, value: $ty, offset: usize) -> Result<usize, TryWriteAtError> {
          self.try_put_slice_at(&value.to_le_bytes(), offset)
        }

        #[doc = "Writes a `" $ty "` value in big-endian byte order to the buffer at the specified offset."]
        ///
        #[doc = "Returns the number of bytes written (always `size_of::<" $ty ">()` for this type)."]
        ///
        /// # Panics
        ///
        /// Panics if `offset >= self.mutable()` or if `offset + size_of::<T>() > self.mutable()`.
        /// Use the `*_checked` or `try_*` variants for non-panicking writes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "let written = slice.put_" $ty "_be_at(0x1234 as " $ty ", 2);"]
        #[doc = "assert_eq!(written, size_of::<" $ty ">());"]
        /// // Value is written in big-endian format starting at offset 2
        /// ```
        #[inline]
        fn [< put_ $ty _be_at>](&mut self, value: $ty, offset: usize) -> usize {
          self.put_slice_at(&value.to_be_bytes(), offset)
        }

        #[doc = "Tries to write a `" $ty "` value in big-endian byte order to the buffer at the specified offset."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_be_at`](BufMut::put_" $ty "_be_at)."]
        ///
        /// Returns `Some(bytes_written)` on success, or `None` if the offset is out of bounds
        /// or there's insufficient space for the value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.put_" $ty "_be_at_checked(0x1234 as " $ty ", 2).is_some());"]
        #[doc = "assert!(slice.put_" $ty "_be_at_checked(0x1234 as " $ty ", 30).is_none()); // Out of bounds"]
        /// ```
        #[inline]
        fn [< put_ $ty _be_at_checked>](&mut self, value: $ty, offset: usize) -> Option<usize> {
          self.put_slice_at_checked(&value.to_be_bytes(), offset)
        }

        #[doc = "Tries to write a `" $ty "` value in big-endian byte order to the buffer at the specified offset."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_be_at`](BufMut::put_" $ty "_be_at)."]
        ///
        /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteAtError)` with detailed
        /// error information if the offset is out of bounds or there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.try_put_" $ty "_be_at(0x1234 as " $ty ", 2).is_ok());"]
        ///
        #[doc = "let err = slice.try_put_" $ty "_be_at(0x1234 as " $ty ", 30).unwrap_err();"]
        /// // err contains detailed information about what went wrong
        /// ```
        #[inline]
        fn [< try_put_ $ty _be_at>](&mut self, value: $ty, offset: usize) -> Result<usize, TryWriteAtError> {
          self.try_put_slice_at(&value.to_be_bytes(), offset)
        }

        #[doc = "Writes a `" $ty "` value in native-endian byte order to the buffer at the specified offset."]
        ///
        /// The byte order depends on the target platform's endianness (little-endian on x86/x64,
        /// big-endian on some embedded platforms).
        ///
        #[doc = "Returns the number of bytes written (always `size_of::<" $ty ">()` for this type)."]
        ///
        /// # Panics
        ///
        /// Panics if `offset >= self.mutable()` or if `offset + size_of::<T>() > self.mutable()`.
        /// Use the `*_checked` or `try_*` variants for non-panicking writes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "let written = slice.put_" $ty "_ne_at(0x1234 as " $ty ", 2);"]
        #[doc = "assert_eq!(written, size_of::<" $ty ">());"]
        /// // Value is written in native-endian format starting at offset 2
        /// ```
        #[inline]
        fn [< put_ $ty _ne_at>](&mut self, value: $ty, offset: usize) -> usize {
          self.put_slice_at(&value.to_ne_bytes(), offset)
        }

        #[doc = "Tries to write a `" $ty "` value in native-endian byte order to the buffer at the specified offset."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`put_" $ty "_ne_at`](BufMut::put_" $ty "_ne_at)."]
        ///
        /// Returns `Some(bytes_written)` on success, or `None` if the offset is out of bounds
        /// or there's insufficient space for the value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.put_" $ty "_ne_at_checked(0x1234 as " $ty ", 2).is_some());"]
        #[doc = "assert!(slice.put_" $ty "_ne_at_checked(0x1234 as " $ty ", 30).is_none()); // Out of bounds"]
        /// ```
        #[inline]
        fn [< put_ $ty _ne_at_checked>](&mut self, value: $ty, offset: usize) -> Option<usize> {
          self.put_slice_at_checked(&value.to_ne_bytes(), offset)
        }

        #[doc = "Tries to write a `" $ty "` value in native-endian byte order to the buffer at the specified offset."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`put_" $ty "_ne_at`](BufMut::put_" $ty "_ne_at)."]
        ///
        /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteAtError)` with detailed
        /// error information if the offset is out of bounds or there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.try_put_" $ty "_ne_at(0x1234 as " $ty ", 2).is_ok());"]
        ///
        #[doc = "let err = slice.try_put_" $ty "_ne_at(0x1234 as " $ty ", 30).unwrap_err();"]
        /// // err contains detailed information about what went wrong
        /// ```
        #[inline]
        fn [< try_put_ $ty _ne_at>](&mut self, value: $ty, offset: usize) -> Result<usize, TryWriteAtError> {
          self.try_put_slice_at(&value.to_ne_bytes(), offset)
        }

        #[doc = "Writes a `" $ty "` value in little-endian byte order to the beginning of the buffer."]
        ///
        #[doc = "Returns the number of bytes written (always `size_of::<" $ty ">()` for this type)."]
        ///
        /// # Panics
        ///
        /// Panics if the buffer has insufficient space to hold the value.
        /// Use the `*_checked` or `try_*` variants for non-panicking writes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "let written = slice.put_" $ty "_le(0x1234 as " $ty ");"]
        #[doc = "assert_eq!(written, size_of::<" $ty ">());"]
        /// // Value is written in little-endian format at the beginning
        /// ```
        #[inline]
        fn [< put_ $ty _le>](&mut self, value: $ty) -> usize {
          self.put_slice(&value.to_le_bytes())
        }

        #[doc = "Tries to write a `" $ty "` value in little-endian byte order to the beginning of the buffer."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_le`](BufMut::put_" $ty "_le)."]
        ///
        /// Returns `Some(bytes_written)` on success, or `None` if there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.put_" $ty "_le_checked(0x1234 as " $ty ").is_some());"]
        ///
        /// let mut small_buf = [0u8; 1];
        /// let mut small_slice = &mut small_buf[..];
        #[doc = "assert!(small_slice.put_" $ty "_le_checked(0x1234 as " $ty ").is_none()); // Not enough space"]
        /// ```
        #[inline]
        fn [< put_ $ty _le_checked>](&mut self, value: $ty) -> Option<usize> {
          self.put_slice_checked(&value.to_le_bytes())
        }

        #[doc = "Tries to write a `" $ty "` value in little-endian byte order to the beginning of the buffer."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_le`](BufMut::put_" $ty "_le)."]
        ///
        /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteError)` with detailed
        /// error information if there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.try_put_" $ty "_le(0x1234 as " $ty ").is_ok());"]
        ///
        /// let mut small_buf = [0u8; 1];
        /// let mut small_slice = &mut small_buf[..];
        #[doc = "let err = small_slice.try_put_" $ty "_le(0x1234 as " $ty ").unwrap_err();"]
        /// // err contains information about required vs available space
        /// ```
        #[inline]
        fn [< try_put_ $ty _le>](&mut self, value: $ty) -> Result<usize, TryWriteError> {
          self.try_put_slice(&value.to_le_bytes())
        }

        #[doc = "Writes a `" $ty "` value in big-endian byte order to the beginning of the buffer."]
        ///
        #[doc = "Returns the number of bytes written (always `size_of::<" $ty ">()` for this type)."]
        ///
        /// # Panics
        ///
        /// Panics if the buffer has insufficient space to hold the value.
        /// Use the `*_checked` or `try_*` variants for non-panicking writes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "let written = slice.put_" $ty "_be(0x1234 as " $ty ");"]
        #[doc = "assert_eq!(written, size_of::<" $ty ">());"]
        /// // Value is written in big-endian format at the beginning
        /// ```
        #[inline]
        fn [< put_ $ty _be>](&mut self, value: $ty) -> usize {
          self.put_slice(&value.to_be_bytes())
        }

        #[doc = "Tries to write a `" $ty "` value in big-endian byte order to the beginning of the buffer."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_be`](BufMut::put_" $ty "_be)."]
        ///
        /// Returns `Some(bytes_written)` on success, or `None` if there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.put_" $ty "_be_checked(0x1234 as " $ty ").is_some());"]
        ///
        /// let mut small_buf = [0u8; 1];
        /// let mut small_slice = &mut small_buf[..];
        #[doc = "assert!(small_slice.put_" $ty "_be_checked(0x1234 as " $ty ").is_none()); // Not enough space"]
        /// ```
        #[inline]
        fn [< put_ $ty _be_checked>](&mut self, value: $ty) -> Option<usize> {
          self.put_slice_checked(&value.to_be_bytes())
        }

        #[doc = "Tries to write a `" $ty "` value in big-endian byte order to the beginning of the buffer."]
        ///
        #[doc = "This is the non-panicking version of [`put_" $ty "_be`](BufMut::put_" $ty "_be)."]
        ///
        /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteError)` with detailed
        /// error information if there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.try_put_" $ty "_be(0x1234 as " $ty ").is_ok());"]
        ///
        /// let mut small_buf = [0u8; 1];
        /// let mut small_slice = &mut small_buf[..];
        #[doc = "let err = small_slice.try_put_" $ty "_be(0x1234 as " $ty ").unwrap_err();"]
        /// // err contains information about required vs available space
        /// ```
        #[inline]
        fn [< try_put_ $ty _be>](&mut self, value: $ty) -> Result<usize, TryWriteError> {
          self.try_put_slice(&value.to_be_bytes())
        }

        #[doc = "Writes a `" $ty "` value in native-endian byte order to the beginning of the buffer."]
        ///
        /// The byte order depends on the target platform's endianness (little-endian on x86/x64,
        /// big-endian on some embedded platforms).
        ///
        #[doc = "Returns the number of bytes written (always `size_of::<" $ty ">()` for this type)."]
        ///
        /// # Panics
        ///
        /// Panics if the buffer has insufficient space to hold the value.
        /// Use the `*_checked` or `try_*` variants for non-panicking writes.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "let written = slice.put_" $ty "_ne(0x1234 as " $ty ");"]
        #[doc = "assert_eq!(written, size_of::<" $ty ">());"]
        /// // Value is written in native-endian format at the beginning
        /// ```
        #[inline]
        fn [< put_ $ty _ne>](&mut self, value: $ty) -> usize {
          self.put_slice(&value.to_ne_bytes())
        }

        #[doc = "Tries to write a `" $ty "` value in native-endian byte order to the beginning of the buffer."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`put_" $ty "_ne`](BufMut::put_" $ty "_ne)."]
        ///
        /// Returns `Some(bytes_written)` on success, or `None` if there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.put_" $ty "_ne_checked(0x1234 as " $ty ").is_some());"]
        ///
        /// let mut small_buf = [0u8; 1];
        /// let mut small_slice = &mut small_buf[..];
        #[doc = "assert!(small_slice.put_" $ty "_ne_checked(0x1234 as " $ty ").is_none()); // Not enough space"]
        /// ```
        #[inline]
        fn [< put_ $ty _ne_checked>](&mut self, value: $ty) -> Option<usize> {
          self.put_slice_checked(&value.to_ne_bytes())
        }

        #[doc = "Tries to write a `" $ty "` value in native-endian byte order to the beginning of the buffer."]
        ///
        /// The byte order depends on the target platform's endianness.
        #[doc = "This is the non-panicking version of [`put_" $ty "_ne`](BufMut::put_" $ty "_ne)."]
        ///
        /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteError)` with detailed
        /// error information if there's insufficient space.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use bufkit::BufMut;
        ///
        /// let mut buf = [0u8; 24];
        /// let mut slice = &mut buf[..];
        #[doc = "assert!(slice.try_put_" $ty "_ne(0x1234 as " $ty ").is_ok());"]
        ///
        /// let mut small_buf = [0u8; 1];
        /// let mut small_slice = &mut small_buf[..];
        #[doc = "let err = small_slice.try_put_" $ty "_ne(0x1234 as " $ty ").unwrap_err();"]
        /// // err contains information about required vs available space
        /// ```
        #[inline]
        fn [< try_put_ $ty _ne>](&mut self, value: $ty) -> Result<usize, TryWriteError> {
          self.try_put_slice(&value.to_ne_bytes())
        }
      )*
    }
  };
  (@forward $($ty:ty),+$(,)?) => {
    paste::paste! {
      $(
        #[inline]
        fn [< put_ $ty _le_at>](&mut self, value: $ty, offset: usize) -> usize {
          (**self).[< put_ $ty _le_at>](value, offset)
        }

        #[inline]
        fn [< put_ $ty _le_at_checked>](&mut self, value: $ty, offset: usize) -> Option<usize> {
          (**self).[< put_ $ty _le_at_checked>](value, offset)
        }

        #[inline]
        fn [< try_put_ $ty _le_at>](&mut self, value: $ty, offset: usize) -> Result<usize, TryWriteAtError> {
          (**self).[< try_put_ $ty _le_at>](value, offset)
        }

        #[inline]
        fn [< put_ $ty _be_at>](&mut self, value: $ty, offset: usize) -> usize {
          (**self).[< put_ $ty _be_at>](value, offset)
        }

        #[inline]
        fn [< put_ $ty _be_at_checked>](&mut self, value: $ty, offset: usize) -> Option<usize> {
          (**self).[< put_ $ty _be_at_checked>](value, offset)
        }

        #[inline]
        fn [< try_put_ $ty _be_at>](&mut self, value: $ty, offset: usize) -> Result<usize, TryWriteAtError> {
          (**self).[< try_put_ $ty _be_at>](value, offset)
        }

        #[inline]
        fn [< put_ $ty _ne_at>](&mut self, value: $ty, offset: usize) -> usize {
          (**self).[< put_ $ty _ne_at>](value, offset)
        }

        #[inline]
        fn [< put_ $ty _ne_at_checked>](&mut self, value: $ty, offset: usize) -> Option<usize> {
          (**self).[< put_ $ty _ne_at_checked>](value, offset)
        }

        #[inline]
        fn [< try_put_ $ty _ne_at>](&mut self, value: $ty, offset: usize) -> Result<usize, TryWriteAtError> {
          (**self).[< try_put_ $ty _ne_at>](value, offset)
        }

        #[inline]
        fn [< put_ $ty _le>](&mut self, value: $ty) -> usize {
          (**self).[< put_ $ty _le>](value)
        }

        #[inline]
        fn [< put_ $ty _le_checked>](&mut self, value: $ty) -> Option<usize> {
          (**self).[< put_ $ty _le_checked>](value)
        }

        #[inline]
        fn [< try_put_ $ty _le>](&mut self, value: $ty) -> Result<usize, TryWriteError> {
          (**self).[< try_put_ $ty _le>](value)
        }

        #[inline]
        fn [< put_ $ty _be>](&mut self, value: $ty) -> usize {
          (**self).[< put_ $ty _be>](value)
        }

        #[inline]
        fn [< put_ $ty _be_checked>](&mut self, value: $ty) -> Option<usize> {
          (**self).[< put_ $ty _be_checked>](value)
        }

        #[inline]
        fn [< try_put_ $ty _be>](&mut self, value: $ty) -> Result<usize, TryWriteError> {
          (**self).[< try_put_ $ty _be>](value)
        }

        #[inline]
        fn [< put_ $ty _ne>](&mut self, value: $ty) -> usize {
          (**self).[< put_ $ty _ne>](value)
        }

        #[inline]
        fn [< put_ $ty _ne_checked>](&mut self, value: $ty) -> Option<usize> {
          (**self).[< put_ $ty _ne_checked>](value)
        }

        #[inline]
        fn [< try_put_ $ty _ne>](&mut self, value: $ty) -> Result<usize, TryWriteError> {
          (**self).[< try_put_ $ty _ne>](value)
        }
      )*
    }
  };
}

/// A trait for implementing custom buffers that can store and manipulate byte sequences.
///
/// **Implementers Notes:** Implementations for write methods should not have any hidden allocation logic.
///
/// This trait provides a comprehensive set of methods for writing data to buffers with different
/// error handling strategies:
/// - **Panicking methods** (e.g., `put_*`): Fast operations that panic on insufficient space
/// - **Checked methods** (e.g., `*_checked`): Return `Option` - `None` on failure, `Some(bytes_written)` on success
/// - **Fallible methods** (e.g., `try_*`): Return `Result` with detailed error information
///
/// # Method Categories
///
/// - **Buffer inspection**: `mutable()`, `has_mutable()`, `buffer()`, `buffer_mut()`
/// - **Buffer manipulation**: `resize()`, `truncate_mut()`, `fill()`
/// - **Slice operations**: `prefix_mut()`, `suffix_mut()`, `split_at_mut()`
/// - **Writing data**: `put_slice()`, `put_u8()`, `put_u16_le()`, etc.
/// - **Writing at offset**: `put_slice_at()`, `put_u8_at()`, `put_u16_le_at()`, etc.
pub trait BufMut {
  /// Returns `true` if the buffer has available space for writing.
  ///
  /// This is equivalent to `self.mutable() == 0`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  /// assert!(slice.has_mutable());
  ///
  /// let mut empty: &mut [u8] = &mut [];
  /// assert!(!empty.has_mutable());
  /// ```
  fn has_mutable(&self) -> bool {
    self.mutable() > 0
  }

  /// Returns the number of bytes available for writing in the buffer.
  ///
  /// For fixed-size buffers like `&mut [u8]`, this returns the total buffer size.
  /// For growable buffers like `Vec<u8>`, this typically returns the current length.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  /// assert_eq!(slice.mutable(), 24);
  /// ```
  fn mutable(&self) -> usize;

  /// Shortens the buffer to the specified length, keeping the first `len` bytes.
  ///
  /// If `len` is greater than or equal to the buffer's current length, this has no effect.
  /// This operation cannot fail and will never panic.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = vec![1, 2, 3, 4, 5];
  /// buf.truncate_mut(3);
  /// assert_eq!(buf, [1, 2, 3]);
  ///
  /// // Truncating to a length >= current length has no effect
  /// buf.truncate_mut(10);
  /// assert_eq!(buf, [1, 2, 3]);
  /// ```
  fn truncate_mut(&mut self, new_len: usize);

  /// Resizes the buffer to the specified length, filling new bytes with the given value.
  ///
  /// If `new_len` is less than the current length, the buffer is truncated.
  /// If `new_len` is greater than the current length, the buffer is extended with `fill_value`.
  ///
  /// # Panics
  ///
  /// May panic if the buffer cannot be resized (e.g., fixed-size buffers when growing).
  /// Use [`try_resize`](BufMut::try_resize) for non-panicking resize operations.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = vec![1, 2, 3];
  /// buf.resize(5, 0xFF);
  /// assert_eq!(buf, [1, 2, 3, 0xFF, 0xFF]);
  ///
  /// buf.resize(2, 0x00);
  /// assert_eq!(buf, [1, 2]);
  /// ```
  fn resize(&mut self, new_len: usize, fill_value: u8);

  /// Returns the entire initialized buffer as a mutable slice.
  ///
  /// This provides direct access to all buffer contents for efficient manipulation.
  /// The returned slice covers all initialized bytes in the buffer.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = vec![1, 2, 3, 4];
  /// let slice = buf.buffer_mut();
  /// slice[0] = 0xFF;
  /// assert_eq!(buf[0], 0xFF);
  /// ```
  fn buffer_mut(&mut self) -> &mut [u8];

  /// Tries to resize the buffer to the specified length, filling new bytes with the given value.
  ///
  /// This is the non-panicking version of [`resize`](BufMut::resize).
  /// Returns `Ok(())` on success, or `Err(TryResizeError)` if the resize operation fails
  /// (e.g., insufficient capacity in fixed-size buffers).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 5];
  /// let mut slice = &mut buf[..3];
  ///
  /// // This will succeed - shrinking
  /// assert!(slice.try_resize(2, 0xFF).is_ok());
  ///
  /// // This will fail - cannot grow a fixed slice beyond its bounds
  /// assert!(slice.try_resize(10, 0xFF).is_err());
  /// ```
  fn try_resize(&mut self, new_len: usize, fill_value: u8) -> Result<(), TryResizeError>;

  /// Fills the entire buffer with the specified byte value.
  ///
  /// This overwrites all bytes in the buffer with `value`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [1, 2, 3, 4];
  /// let mut slice = &mut buf[..];
  /// slice.fill(0xFF);
  /// assert_eq!(buf, [0xFF, 0xFF, 0xFF, 0xFF]);
  /// ```
  fn fill(&mut self, value: u8) {
    self.buffer_mut().fill(value);
  }

  /// Returns a mutable slice containing the first `len` bytes of the buffer.
  ///
  /// This provides access to a prefix of the buffer for efficient manipulation
  /// of a specific portion without affecting the rest of the buffer.
  ///
  /// # Panics
  ///
  /// Panics if `len > self.mutable()`.
  /// Use [`prefix_mut_checked`](BufMut::prefix_mut_checked) for non-panicking access.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [1, 2, 3, 4, 5];
  /// let mut slice = &mut buf[..];
  /// let prefix = slice.prefix_mut(3);
  /// prefix.fill(0xFF);
  /// assert_eq!(buf, [0xFF, 0xFF, 0xFF, 4, 5]);
  /// ```
  fn prefix_mut(&mut self, len: usize) -> &mut [u8] {
    &mut self.buffer_mut()[..len]
  }

  /// Returns a mutable slice containing the first `len` bytes of the buffer.
  ///
  /// This is the non-panicking version of [`prefix_mut`](BufMut::prefix_mut).
  /// Returns `Some(slice)` if `len <= self.mutable()`, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [1, 2, 3, 4, 5];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.prefix_mut_checked(3).is_some());
  /// assert!(slice.prefix_mut_checked(10).is_none());
  /// ```
  fn prefix_mut_checked(&mut self, len: usize) -> Option<&mut [u8]> {
    match self.mutable().checked_sub(len)? {
      0 => Some(&mut []),
      end => Some(&mut self.buffer_mut()[..end]),
    }
  }

  /// Returns a mutable slice containing the last `len` bytes of the buffer.
  ///
  /// This provides access to a suffix of the buffer for efficient manipulation
  /// of the trailing portion without affecting the rest of the buffer.
  ///
  /// # Panics
  ///
  /// Panics if `len > self.mutable()`.
  /// Use [`suffix_mut_checked`](BufMut::suffix_mut_checked) for non-panicking access.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [1, 2, 3, 4, 5];
  /// let mut slice = &mut buf[..];
  /// let suffix = slice.suffix_mut(2);
  /// suffix.fill(0xFF);
  /// assert_eq!(buf, [1, 2, 3, 0xFF, 0xFF]);
  /// ```
  fn suffix_mut(&mut self, len: usize) -> &mut [u8] {
    let total_len = self.mutable();
    &mut self.buffer_mut()[total_len - len..]
  }

  /// Returns a mutable slice containing the last `len` bytes of the buffer.
  ///
  /// This is the non-panicking version of [`suffix_mut`](BufMut::suffix_mut).
  /// Returns `Some(slice)` if `len <= self.mutable()`, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [1, 2, 3, 4, 5];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.suffix_mut_checked(2).is_some());
  /// assert!(slice.suffix_mut_checked(10).is_none());
  /// ```
  fn suffix_mut_checked(&mut self, len: usize) -> Option<&mut [u8]> {
    match self.mutable().checked_sub(len)? {
      0 => Some(&mut []),
      start => Some(&mut self.buffer_mut()[start..]),
    }
  }

  /// Divides the buffer into two mutable slices at the given index.
  ///
  /// Returns a tuple where the first slice contains indices `[0, mid)` and
  /// the second slice contains indices `[mid, len)`.
  ///
  /// # Panics
  ///
  /// Panics if `mid > self.mutable()`.
  /// Use [`split_at_mut_checked`](BufMut::split_at_mut_checked) for non-panicking splitting.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [1, 2, 3, 4, 5];
  /// let mut slice = &mut buf[..];
  /// let (left, right) = slice.split_at_mut(2);
  /// assert_eq!(left, &[1, 2]);
  /// assert_eq!(right, &[3, 4, 5]);
  /// ```
  fn split_at_mut(&mut self, mid: usize) -> (&mut [u8], &mut [u8]) {
    self.buffer_mut().split_at_mut(mid)
  }

  /// Divides the buffer into two mutable slices at the given index.
  ///
  /// This is the non-panicking version of [`split_at_mut`](BufMut::split_at_mut).
  /// Returns `Some((left, right))` if `mid <= self.mutable()`, otherwise returns `None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [1, 2, 3, 4, 5];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.split_at_mut_checked(2).is_some());
  /// assert!(slice.split_at_mut_checked(10).is_none());
  /// ```
  fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut [u8], &mut [u8])> {
    self.buffer_mut().split_at_mut_checked(mid)
  }

  /// Writes a slice of bytes to the beginning of the buffer.
  ///
  /// Copies all bytes from `slice` into the buffer starting at the beginning.
  /// Returns the number of bytes written (always equal to `slice.len()`).
  ///
  /// # Panics
  ///
  /// Panics if `slice.len() > self.mutable()`.
  /// Use [`put_slice_checked`](BufMut::put_slice_checked) or
  /// [`try_put_slice`](BufMut::try_put_slice) for non-panicking writes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  /// let written = slice.put_slice(&[1, 2, 3]);
  /// assert_eq!(written, 3);
  /// assert_eq!(&buf[..3], &[1, 2, 3]);
  /// ```
  fn put_slice(&mut self, slice: &[u8]) -> usize {
    let len = slice.len();
    self.buffer_mut()[..len].copy_from_slice(slice);
    len
  }

  /// Tries to write a slice of bytes to the beginning of the buffer.
  ///
  /// This is the non-panicking version of [`put_slice`](BufMut::put_slice).
  /// Returns `Some(bytes_written)` on success, or `None` if the buffer is too small.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 5];
  /// let mut slice = &mut buf[..];
  ///
  /// assert_eq!(slice.put_slice_checked(&[1, 2, 3]), Some(3));
  /// assert_eq!(slice.put_slice_checked(&[1, 2, 3, 4, 5, 6]), None);
  /// ```
  fn put_slice_checked(&mut self, slice: &[u8]) -> Option<usize> {
    let len = slice.len();
    if len <= self.mutable() {
      self.buffer_mut()[..len].copy_from_slice(slice);
      Some(len)
    } else {
      None
    }
  }

  /// Tries to write a slice of bytes to the beginning of the buffer.
  ///
  /// This is the non-panicking version of [`put_slice`](BufMut::put_slice) that
  /// returns detailed error information on failure.
  /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteError)` with details about
  /// the attempted write size and available space.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 5];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.try_put_slice(&[1, 2, 3]).is_ok());
  ///
  /// let err = slice.try_put_slice(&[1, 2, 3, 4, 5, 6]).unwrap_err();
  /// // err contains details about requested vs available space
  /// ```
  fn try_put_slice(&mut self, slice: &[u8]) -> Result<usize, TryWriteError> {
    let len = slice.len();
    let space = self.mutable();
    if len <= space {
      self.buffer_mut()[..len].copy_from_slice(slice);
      Ok(len)
    } else {
      Err(TryWriteError::new(slice.len(), space))
    }
  }

  /// Writes a slice of bytes to the buffer at the specified offset.
  ///
  /// Copies all bytes from `slice` into the buffer starting at the given `offset`.
  /// Returns the number of bytes written (always equal to `slice.len()`).
  ///
  /// # Panics
  ///
  /// Panics if `offset + slice.len() > self.mutable()` or if `offset >= self.mutable()`.
  /// Use [`put_slice_at_checked`](BufMut::put_slice_at_checked) or
  /// [`try_put_slice_at`](BufMut::try_put_slice_at) for non-panicking writes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  /// let written = slice.put_slice_at(&[1, 2, 3], 2);
  /// assert_eq!(written, 3);
  /// assert_eq!(&buf[2..5], &[1, 2, 3]);
  /// ```
  fn put_slice_at(&mut self, slice: &[u8], offset: usize) -> usize {
    let len = slice.len();
    self.buffer_mut()[offset..offset + len].copy_from_slice(slice);
    len
  }

  /// Tries to write a slice of bytes to the buffer at the specified offset.
  ///
  /// This is the non-panicking version of [`put_slice_at`](BufMut::put_slice_at).
  /// Returns `Some(bytes_written)` on success, or `None` if there's insufficient space
  /// or the offset is out of bounds.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  ///
  /// assert_eq!(slice.put_slice_at_checked(&[1, 2], 3), Some(2));
  /// assert_eq!(slice.put_slice_at_checked(&[1, 2, 3, 4, 5], 30), None); // Not enough space
  /// assert_eq!(slice.put_slice_at_checked(&[1], 30), None); // Offset out of bounds
  /// ```
  fn put_slice_at_checked(&mut self, slice: &[u8], offset: usize) -> Option<usize> {
    let len = slice.len();
    if len + offset <= self.mutable() {
      self.buffer_mut()[offset..offset + len].copy_from_slice(slice);
      Some(len)
    } else {
      None
    }
  }

  /// Tries to write a slice of bytes to the buffer at the specified offset.
  ///
  /// This is the non-panicking version of [`put_slice_at`](BufMut::put_slice_at) that
  /// returns detailed error information on failure.
  /// Returns `Ok(bytes_written)` on success, or `Err(TryWriteAtError)` with details about
  /// what went wrong (out of bounds offset, insufficient space, etc.).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.try_put_slice_at(&[1, 2], 3).is_ok());
  ///
  /// let err = slice.try_put_slice_at(&[1, 2, 3, 4, 5], 30).unwrap_err();
  /// // err contains detailed information about the failure
  /// ```
  fn try_put_slice_at(&mut self, slice: &[u8], offset: usize) -> Result<usize, TryWriteAtError> {
    let len = slice.len();
    let space = self.mutable();
    if offset >= space {
      return Err(TryWriteAtError::out_of_bounds(offset, space));
    }

    if len + offset <= space {
      self.buffer_mut()[offset..offset + len].copy_from_slice(slice);
      Ok(len)
    } else {
      Err(TryWriteAtError::insufficient_space(
        len,
        space - offset,
        offset,
      ))
    }
  }

  put_fixed!(u16, u32, u64, u128, i16, i32, i64, i128, f32, f64);

  /// Writes a `u8` value to the beginning of the buffer.
  ///
  /// Returns the number of bytes written (always `1` for this type).
  ///
  /// # Panics
  ///
  /// Panics if the buffer has no space available.
  /// Use [`put_u8_checked`](BufMut::put_u8_checked) for non-panicking writes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 5];
  /// let mut slice = &mut buf[..];
  /// let written = slice.put_u8(0xFF);
  /// assert_eq!(written, 1);
  /// assert_eq!(buf[0], 0xFF);
  /// ```
  #[inline]
  fn put_u8(&mut self, value: u8) -> usize {
    self.put_slice(&[value])
  }

  /// Tries to write a `u8` value to the beginning of the buffer.
  ///
  /// This is the non-panicking version of [`put_u8`](BufMut::put_u8).
  /// Returns `Some(1)` on success, or `None` if the buffer has no space.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 1];
  /// let mut slice = &mut buf[..];
  ///
  /// assert_eq!(slice.put_u8_checked(0xFF), Some(1));
  ///
  /// let mut empty = &mut [][..];
  /// assert_eq!(empty.put_u8_checked(0xFF), None);
  /// ```
  #[inline]
  fn put_u8_checked(&mut self, value: u8) -> Option<usize> {
    self.put_slice_checked(&[value])
  }

  /// Writes an `i8` value to the beginning of the buffer.
  ///
  /// Returns the number of bytes written (always `1` for this type).
  ///
  /// # Panics
  ///
  /// Panics if the buffer has no space available.
  /// Use [`put_i8_checked`](BufMut::put_i8_checked) for non-panicking writes.
  #[inline]
  fn put_i8(&mut self, value: i8) -> usize {
    self.put_slice(&[value as u8])
  }

  /// Tries to write an `i8` value to the beginning of the buffer.
  ///
  /// This is the non-panicking version of [`put_i8`](BufMut::put_i8).
  /// Returns `Some(1)` on success, or `None` if the buffer has no space.
  #[inline]
  fn put_i8_checked(&mut self, value: i8) -> Option<usize> {
    self.put_slice_checked(&[value as u8])
  }

  /// Writes a `u8` value to the buffer at the specified offset.
  ///
  /// Returns the number of bytes written (always `1` for this type).
  ///
  /// # Panics
  ///
  /// Panics if `offset >= self.mutable()`.
  /// Use [`put_u8_at_checked`](BufMut::put_u8_at_checked) for non-panicking writes.
  #[inline]
  fn put_u8_at(&mut self, value: u8, offset: usize) -> usize {
    self.put_slice_at(&[value], offset)
  }

  /// Tries to write a `u8` value to the buffer at the specified offset.
  ///
  /// This is the non-panicking version of [`put_u8_at`](BufMut::put_u8_at).
  /// Returns `Some(1)` on success, or `None` if the offset is out of bounds.
  #[inline]
  fn put_u8_at_checked(&mut self, value: u8, offset: usize) -> Option<usize> {
    self.put_slice_at_checked(&[value], offset)
  }

  /// Writes an `i8` value to the buffer at the specified offset.
  ///
  /// Returns the number of bytes written (always `1` for this type).
  ///
  /// # Panics
  ///
  /// Panics if `offset >= self.mutable()`.
  /// Use [`put_i8_at_checked`](BufMut::put_i8_at_checked) for non-panicking writes.
  #[inline]
  fn put_i8_at(&mut self, value: i8, offset: usize) -> usize {
    self.put_slice_at(&[value as u8], offset)
  }

  /// Tries to write an `i8` value to the buffer at the specified offset.
  ///
  /// This is the non-panicking version of [`put_i8_at`](BufMut::put_i8_at).
  /// Returns `Some(1)` on success, or `None` if the offset is out of bounds.
  #[inline]
  fn put_i8_at_checked(&mut self, value: i8, offset: usize) -> Option<usize> {
    self.put_slice_at_checked(&[value as u8], offset)
  }

  /// Tries to write a `u8` value to the beginning of the buffer.
  ///
  /// This is the non-panicking version of [`put_u8`](BufMut::put_u8) that
  /// returns detailed error information on failure.
  /// Returns `Ok(1)` on success, or `Err(TryWriteError)` with details about
  /// the available space if the buffer is full.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 5];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.try_put_u8(0xFF).is_ok());
  ///
  /// let mut empty = &mut [][..];
  /// let err = empty.try_put_u8(0xFF).unwrap_err();
  /// // err contains details about requested vs available space
  /// ```
  #[inline]
  fn try_put_u8(&mut self, value: u8) -> Result<usize, TryWriteError> {
    self.try_put_slice(&[value])
  }

  /// Tries to write an `i8` value to the beginning of the buffer.
  ///
  /// This is the non-panicking version of [`put_i8`](BufMut::put_i8) that
  /// returns detailed error information on failure.
  /// Returns `Ok(1)` on success, or `Err(TryWriteError)` with details about
  /// the available space if the buffer is full.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 5];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.try_put_i8(-42).is_ok());
  ///
  /// let mut empty = &mut [][..];
  /// let err = empty.try_put_i8(-42).unwrap_err();
  /// // err contains details about requested vs available space
  /// ```
  #[inline]
  fn try_put_i8(&mut self, value: i8) -> Result<usize, TryWriteError> {
    self.try_put_slice(&[value as u8])
  }

  /// Tries to write a `u8` value to the buffer at the specified offset.
  ///
  /// This is the non-panicking version of [`put_u8_at`](BufMut::put_u8_at) that
  /// returns detailed error information on failure.
  /// Returns `Ok(1)` on success, or `Err(TryWriteAtError)` with details about
  /// what went wrong (out of bounds offset, etc.).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.try_put_u8_at(0xFF, 5).is_ok());
  ///
  /// let err = slice.try_put_u8_at(0xFF, 30).unwrap_err();
  /// // err contains detailed information about the failure
  /// ```
  #[inline]
  fn try_put_u8_at(&mut self, value: u8, offset: usize) -> Result<usize, TryWriteAtError> {
    self.try_put_slice_at(&[value], offset)
  }

  /// Tries to write an `i8` value to the buffer at the specified offset.
  ///
  /// This is the non-panicking version of [`put_i8_at`](BufMut::put_i8_at) that
  /// returns detailed error information on failure.
  /// Returns `Ok(1)` on success, or `Err(TryWriteAtError)` with details about
  /// what went wrong (out of bounds offset, etc.).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::BufMut;
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  ///
  /// assert!(slice.try_put_i8_at(-42, 5).is_ok());
  ///
  /// let err = slice.try_put_i8_at(-42, 30).unwrap_err();
  /// // err contains detailed information about the failure
  /// ```
  #[inline]
  fn try_put_i8_at(&mut self, value: i8, offset: usize) -> Result<usize, TryWriteAtError> {
    self.try_put_slice_at(&[value as u8], offset)
  }
}

/// A trait that extends `BufMut` with additional methods.
pub trait BufMutExt: BufMut {
  /// Writes a type in LEB128 format to the buffer.
  ///
  /// Uses the LEB128 encoding format. The number of bytes written depends
  /// on the value being encoded.
  ///
  /// Returns `Ok(bytes_written)` on success, or `Err(WriteVarintError)` if there's
  /// insufficient space or an encoding error occurs.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, BufMutExt};
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  /// let written = slice.put_varint(&42u32).unwrap();
  /// // written will be 1 for small values like 42
  /// ```
  #[cfg(feature = "varing")]
  #[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
  #[inline]
  fn put_varint<V>(&mut self, value: &V) -> Result<usize, WriteVarintError>
  where
    V: Varint,
  {
    value.encode(self.buffer_mut())
  }

  /// Writes a type in LEB128 format to the buffer at the specified offset.
  ///
  /// Uses the LEB128 encoding format. The number of bytes written depends
  /// on the value being encoded.
  ///
  /// Returns `Ok(bytes_written)` on success, or `Err(WriteVarintAtError)` if the offset
  /// is out of bounds, there's insufficient space, or an encoding error occurs.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, BufMutExt};
  ///
  /// let mut buf = [0u8; 24];
  /// let mut slice = &mut buf[..];
  /// let written = slice.put_varint_at(&42u32, 3).unwrap();
  /// // The varint is written starting at offset 3
  /// ```
  #[inline]
  #[cfg(feature = "varing")]
  #[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
  fn put_varint_at<V>(&mut self, value: &V, offset: usize) -> Result<usize, WriteVarintAtError>
  where
    V: Varint,
  {
    match self.split_at_mut_checked(offset) {
      Some((_, suffix)) => match value.encode(suffix) {
        Ok(read) => Ok(read),
        Err(e) => match e {
          WriteVarintError::InsufficientSpace {
            requested,
            available,
          } => Err(WriteVarintAtError::insufficient_space(
            requested, available, offset,
          )),
          WriteVarintError::Custom(msg) => Err(WriteVarintAtError::custom(msg)),
          _ => Err(WriteVarintAtError::custom("unknown error")),
        },
      },
      None => Err(WriteVarintAtError::out_of_bounds(offset, self.mutable())),
    }
  }
}

impl<T: BufMut> BufMutExt for T {}

macro_rules! deref_forward_put_buf {
  () => {
    #[inline]
    fn has_mutable(&self) -> bool {
      (**self).has_mutable()
    }

    #[inline]
    fn mutable(&self) -> usize {
      (**self).mutable()
    }

    #[inline]
    fn truncate_mut(&mut self, new_len: usize) {
      (**self).truncate_mut(new_len)
    }

    #[inline]
    fn resize(&mut self, new_len: usize, fill_value: u8) {
      (**self).resize(new_len, fill_value)
    }

    #[inline]
    fn buffer_mut(&mut self) -> &mut [u8] {
      (**self).buffer_mut()
    }

    #[inline]
    fn try_resize(&mut self, new_len: usize, fill_value: u8) -> Result<(), TryResizeError> {
      (**self).try_resize(new_len, fill_value)
    }

    #[inline]
    fn fill(&mut self, value: u8) {
      (**self).fill(value)
    }

    #[inline]
    fn prefix_mut(&mut self, len: usize) -> &mut [u8] {
      (**self).prefix_mut(len)
    }

    #[inline]
    fn prefix_mut_checked(&mut self, len: usize) -> Option<&mut [u8]> {
      (**self).prefix_mut_checked(len)
    }

    #[inline]
    fn suffix_mut(&mut self, len: usize) -> &mut [u8] {
      (**self).suffix_mut(len)
    }

    #[inline]
    fn suffix_mut_checked(&mut self, len: usize) -> Option<&mut [u8]> {
      (**self).suffix_mut_checked(len)
    }

    #[inline]
    fn split_at_mut(&mut self, mid: usize) -> (&mut [u8], &mut [u8]) {
      (**self).split_at_mut(mid)
    }

    #[inline]
    fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut [u8], &mut [u8])> {
      (**self).split_at_mut_checked(mid)
    }

    #[inline]
    fn put_slice(&mut self, slice: &[u8]) -> usize {
      (**self).put_slice(slice)
    }

    #[inline]
    fn put_slice_checked(&mut self, slice: &[u8]) -> Option<usize> {
      (**self).put_slice_checked(slice)
    }

    #[inline]
    fn try_put_slice(&mut self, slice: &[u8]) -> Result<usize, TryWriteError> {
      (**self).try_put_slice(slice)
    }

    #[inline]
    fn put_slice_at(&mut self, slice: &[u8], offset: usize) -> usize {
      (**self).put_slice_at(slice, offset)
    }

    #[inline]
    fn put_slice_at_checked(&mut self, slice: &[u8], offset: usize) -> Option<usize> {
      (**self).put_slice_at_checked(slice, offset)
    }

    #[inline]
    fn try_put_slice_at(&mut self, slice: &[u8], offset: usize) -> Result<usize, TryWriteAtError> {
      (**self).try_put_slice_at(slice, offset)
    }

    #[inline]
    fn put_u8(&mut self, value: u8) -> usize {
      (**self).put_u8(value)
    }

    #[inline]
    fn put_u8_checked(&mut self, value: u8) -> Option<usize> {
      (**self).put_u8_checked(value)
    }

    #[inline]
    fn try_put_u8(&mut self, value: u8) -> Result<usize, TryWriteError> {
      (**self).try_put_u8(value)
    }

    #[inline]
    fn put_i8(&mut self, value: i8) -> usize {
      (**self).put_i8(value)
    }

    #[inline]
    fn put_i8_checked(&mut self, value: i8) -> Option<usize> {
      (**self).put_i8_checked(value)
    }

    #[inline]
    fn try_put_i8(&mut self, value: i8) -> Result<usize, TryWriteError> {
      (**self).try_put_i8(value)
    }

    #[inline]
    fn put_u8_at(&mut self, value: u8, offset: usize) -> usize {
      (**self).put_u8_at(value, offset)
    }

    #[inline]
    fn put_u8_at_checked(&mut self, value: u8, offset: usize) -> Option<usize> {
      (**self).put_u8_at_checked(value, offset)
    }

    #[inline]
    fn try_put_u8_at(&mut self, value: u8, offset: usize) -> Result<usize, TryWriteAtError> {
      (**self).try_put_u8_at(value, offset)
    }

    #[inline]
    fn put_i8_at(&mut self, value: i8, offset: usize) -> usize {
      (**self).put_i8_at(value, offset)
    }

    #[inline]
    fn put_i8_at_checked(&mut self, value: i8, offset: usize) -> Option<usize> {
      (**self).put_i8_at_checked(value, offset)
    }

    #[inline]
    fn try_put_i8_at(&mut self, value: i8, offset: usize) -> Result<usize, TryWriteAtError> {
      (**self).try_put_i8_at(value, offset)
    }

    put_fixed! {
      @forward
      u16, u32, u64, u128,
      i16, i32, i64, i128,
      f32, f64
    }
  };
}

impl<T: BufMut + ?Sized> BufMut for &mut T {
  deref_forward_put_buf!();
}

#[cfg(any(feature = "std", feature = "alloc"))]
impl<T: BufMut + ?Sized> BufMut for std::boxed::Box<T> {
  deref_forward_put_buf!();
}

impl BufMut for &mut [u8] {
  #[inline]
  fn truncate_mut(&mut self, len: usize) {
    if len >= self.len() {
      return;
    }

    // Lifetime dance taken from `impl Write for &mut [u8]`.
    let (a, _) = core::mem::take(self).split_at_mut(len);
    *self = a;
  }

  #[inline]
  fn buffer_mut(&mut self) -> &mut [u8] {
    self
  }

  #[inline]
  fn mutable(&self) -> usize {
    <[u8]>::len(self)
  }

  #[inline]
  fn has_mutable(&self) -> bool {
    !self.is_empty()
  }

  #[inline]
  fn resize(&mut self, new_len: usize, fill_value: u8) {
    let len = self.len();
    if new_len > len {
      panic_resize(&TryResizeError::new(new_len, self.len(), fill_value));
    }

    if new_len == len {
      return;
    }

    // Lifetime dance taken from `impl Write for &mut [u8]`.
    let (a, _) = core::mem::take(self).split_at_mut(new_len);
    *self = a;
  }

  fn try_resize(&mut self, new_len: usize, fill_value: u8) -> Result<(), TryResizeError> {
    if new_len > self.mutable() {
      return Err(TryResizeError::new(new_len, self.mutable(), fill_value));
    }
    self.resize(new_len, fill_value);
    Ok(())
  }
}

#[cfg(feature = "bytes_1")]
const _: () = {
  use bytes_1::BytesMut;

  impl BufMut for BytesMut {
    #[inline]
    fn has_mutable(&self) -> bool {
      !self.is_empty()
    }

    #[inline]
    fn mutable(&self) -> usize {
      self.len()
    }

    #[inline]
    fn truncate_mut(&mut self, new_len: usize) {
      self.truncate(new_len);
    }

    #[inline]
    fn resize(&mut self, new_len: usize, fill_value: u8) {
      self.resize(new_len, fill_value);
    }

    #[inline]
    fn try_resize(&mut self, new_len: usize, fill_value: u8) -> Result<(), TryResizeError> {
      self.resize(new_len, fill_value);
      Ok(())
    }

    #[inline]
    fn buffer_mut(&mut self) -> &mut [u8] {
      self.as_mut()
    }
  }
};

#[cfg(any(feature = "std", feature = "alloc"))]
const _: () = {
  use std::vec::Vec;

  impl BufMut for Vec<u8> {
    #[inline]
    fn resize(&mut self, new_len: usize, fill_value: u8) {
      self.resize(new_len, fill_value);
    }

    #[inline]
    fn truncate_mut(&mut self, new_len: usize) {
      self.truncate(new_len);
    }

    #[inline]
    fn buffer_mut(&mut self) -> &mut [u8] {
      self.as_mut_slice()
    }

    #[inline]
    fn mutable(&self) -> usize {
      self.len()
    }

    #[inline]
    fn has_mutable(&self) -> bool {
      !self.is_empty()
    }

    #[inline]
    fn try_resize(&mut self, new_len: usize, fill_value: u8) -> Result<(), TryResizeError> {
      self.resize(new_len, fill_value);
      Ok(())
    }
  }
};

/// Panic with a nice error message.
#[cold]
fn panic_resize(e: &TryResizeError) -> ! {
  panic!("resize failure: {e}",);
}

// The existence of this function makes the compiler catch if the BufMut
// trait is "object-safe" or not.
fn _assert_trait_object(_b: &dyn BufMut) {}
