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
        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in little-endian byte order."]
        ///
        /// Returns the length of the value and the value itself.
        ///
        /// # Panics
        /// - If the buffer is too short to contain the value.
        #[inline]
        fn [<peek_ $ty _le>](&self) -> $ty {
          <$ty>::from_le_bytes(self.peek_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in little-endian byte order, returning `None` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `None` if the buffer is too short.
        #[inline]
        fn [<peek_ $ty _le_checked>](&self) -> Option<$ty> {
          self.peek_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in little-endian byte order, returning `Err` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `Err` if the buffer is too short.
        #[inline]
        fn [<try_peek_ $ty _le>](&self) -> Result<$ty, TryPeekError> {
          self.try_peek_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in big-endian byte order."]
        ///
        /// Returns the length of the value and the value itself.
        ///
        /// # Panics
        /// - If the buffer is too short to contain the value.
        #[inline]
        fn [<peek_ $ty _be>](&self) -> $ty {
          <$ty>::from_be_bytes(self.peek_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in big-endian byte order, returning `None` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `None` if the buffer is too short.
        #[inline]
        fn [<peek_ $ty _be_checked>](&self) -> Option<$ty> {
          self.peek_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_be_bytes)
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in big-endian byte order, returning `Err` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `Err` if the buffer is too short.
        #[inline]
        fn [<try_peek_ $ty _be>](&self) -> Result<$ty, TryPeekError> {
          self.try_peek_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_be_bytes)
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in native-endian byte order."]
        ///
        /// Returns the length of the value and the value itself.
        ///
        /// # Panics
        /// - If the buffer is too short to contain the value.
        #[inline]
        fn [<peek_ $ty _ne>](&self) -> $ty {
          <$ty>::from_ne_bytes(self.peek_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in native-endian byte order, returning `None` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `None` if the buffer is too short.
        #[inline]
        fn [<peek_ $ty _ne_checked>](&self) -> Option<$ty> {
          self.peek_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_ne_bytes)
        }

        #[doc = "Peeks " $ty " from buffer without advancing the internal cursor in native-endian byte order, returning `Err` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `Err` if the buffer is too short.
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
        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in little-endian byte order."]
        ///
        /// Returns the length of the value and the value itself.
        ///
        /// # Panics
        /// - If the buffer is too short to contain the value.
        #[inline]
        fn [<read_ $ty _le>](&mut self) -> $ty {
          <$ty>::from_le_bytes(self.read_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in little-endian byte order, returning `None` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `None` if the buffer is too short.
        #[inline]
        fn [<read_ $ty _le_checked>](&mut self) -> Option<$ty> {
          self.read_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in little-endian byte order, returning `Err` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `Err` if the buffer is too short.
        #[inline]
        fn [<try_read_ $ty _le>](&mut self) -> Result<$ty, TryReadError> {
          self.try_read_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_le_bytes)
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in big-endian byte order."]
        ///
        /// Returns the length of the value and the value itself.
        ///
        /// # Panics
        /// - If the buffer is too short to contain the value.
        #[inline]
        fn [<read_ $ty _be>](&mut self) -> $ty {
          <$ty>::from_be_bytes(self.read_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in big-endian byte order, returning `None` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `None` if the buffer is too short.
        #[inline]
        fn [<read_ $ty _be_checked>](&mut self) -> Option<$ty> {
          self.read_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_be_bytes)
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in big-endian byte order, returning `Err` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `Err` if the buffer is too short.
        #[inline]
        fn [<try_read_ $ty _be>](&mut self) -> Result<$ty, TryReadError> {
          self.try_read_array::<{ core::mem::size_of::<$ty>() }>().map(|val| { <$ty>::from_be_bytes(val) })
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in native-endian byte order."]
        ///
        /// Returns the length of the value and the value itself.
        ///
        /// # Panics
        /// - If the buffer is too short to contain the value.
        #[inline]
        fn [<read_ $ty _ne>](&mut self) -> $ty {
          <$ty>::from_ne_bytes(self.read_array::<{ core::mem::size_of::<$ty>() }>())
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in native-endian byte order, returning `None` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `None` if the buffer is too short.
        #[inline]
        fn [<read_ $ty _ne_checked>](&mut self) -> Option<$ty> {
          self.read_array_checked::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_ne_bytes)
        }

        #[doc = "Reads " $ty " from buffer without advancing the internal cursor in native-endian byte order, returning `Err` if the buffer is too short."]
        ///
        /// Returns the length of the value and the value itself, or `Err` if the buffer is too short.
        #[inline]
        fn [<try_read_ $ty _ne>](&mut self) -> Result<$ty, TryReadError> {
          self.try_read_array::<{ core::mem::size_of::<$ty>() }>().map(<$ty>::from_ne_bytes)
        }
      )*
    }
  };
}

/// A trait for implementing custom buffers that can store and manipulate byte sequences.
pub trait ReadBuf {
  /// Returns an empty read buffer.
  fn empty() -> Self
  where
    Self: Sized;

  /// Returns the number of bytes remaining in the buffer.
  fn remaining(&self) -> usize;

  /// Returns the remaining bytes of the buffer.
  fn remaining_slice(&self) -> &[u8];

  /// Advance the internal cursor of the `ReadBuf` by the specified number of bytes.
  ///
  /// # Panics
  /// - This function may panic if `cnt > self.remaining()`.
  fn advance(&mut self, cnt: usize);

  /// Creates a read buffer containing a segment of the current read buffer's data.
  ///
  /// This method returns a segment of the read buffer instance that represents a portion of the current
  /// read buffer defined by the given range. The original read buffer remains unchanged,
  /// and the read buffer maintains its own independent cursor position starting at the beginning of the segment.
  ///
  /// # Panics
  /// - Panics if the range is out of bounds relative to the current buffer's remaining data.
  fn segment(&self, range: impl RangeBounds<usize>) -> Self
  where
    Self: Sized;

  /// Shortens the buffer, keeping the first `len` bytes and dropping the
  /// rest.
  ///
  /// If `len` is greater than the buffer's current length, this has no
  /// effect.
  ///
  /// The [split_off](`ReadBuf::split_off()`) method can emulate `truncate`, but this causes the
  /// excess bytes to be returned instead of dropped.
  fn truncate(&mut self, len: usize);

  /// Splits the bytes into two at the given index.
  ///
  /// Afterwards `self` contains elements `[0, at)`, and the returned `ReadBuf`
  /// contains elements `[at, len)`. It's guaranteed that the memory does not
  /// move, that is, the address of `self` does not change, and the address of
  /// the returned slice is `at` bytes after that.
  ///
  /// **Implementor Notes:** This should be an `O(1)` operation
  ///
  /// # Panics
  ///
  /// Panics if `at > len`.
  #[must_use = "consider ReadBuf::truncate if you don't need the other half"]
  fn split_off(&mut self, at: usize) -> Self
  where
    Self: Sized;

  /// Splits the bytes into two at the given index, returning `None` if the index is out of bounds.
  ///
  /// This is a non-panicking version of [`split_off`](ReadBuf::split_off).
  #[must_use = "consider ReadBuf::truncate if you don't need the other half"]
  fn split_off_checked(&mut self, at: usize) -> Option<Self>
  where
    Self: Sized,
  {
    if at > self.remaining() {
      None
    } else {
      Some(self.split_off(at))
    }
  }

  /// Splits the bytes into two at the given index, returning an error if the index is out of bounds.
  ///
  /// This is a non-panicking version of [`split_off`](ReadBuf::split_off).
  #[must_use = "consider ReadBuf::try_split_off if you don't need the other half"]
  fn try_split_off(&mut self, at: usize) -> Result<Self, TrySplitOffError>
  where
    Self: Sized,
  {
    if at > self.remaining() {
      Err(TrySplitOffError::new(at + 1, self.remaining()))
    } else {
      Ok(self.split_off(at))
    }
  }

  /// Splits the bytes into two at the given index.
  ///
  /// Afterwards `self` contains elements `[at, len)`, and the returned
  /// `ReadBuf` contains elements `[0, at)`.
  ///
  /// **Implementor Notes:** This should be an `O(1)` operation.
  ///
  /// # Examples
  ///
  /// ```
  /// use bytes::Bytes;
  ///
  /// let mut a = Bytes::from(&b"hello world"[..]);
  /// let b = a.split_to(5);
  ///
  /// assert_eq!(&a[..], b" world");
  /// assert_eq!(&b[..], b"hello");
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if `at > len`.
  #[must_use = "consider ReadBuf::advance if you don't need the other half"]
  fn split_to(&mut self, at: usize) -> Self
  where
    Self: Sized;

  /// Splits the bytes into two at the given index, returning `None` if the index is out of bounds.
  ///
  /// This is a non-panicking version of [`split_to`](ReadBuf::split_to).
  #[must_use = "consider ReadBuf::advance if you don't need the other half"]
  fn split_to_checked(&mut self, at: usize) -> Option<Self>
  where
    Self: Sized,
  {
    if at > self.remaining() {
      None
    } else {
      Some(self.split_to(at))
    }
  }

  /// Splits the bytes into two at the given index, returning an error if the index is out of bounds.
  ///
  /// This is a non-panicking version of [`split_to`](ReadBuf::split_to).
  #[must_use = "consider ReadBuf::try_split_to if you don't need the other half"]
  fn try_split_to(&mut self, at: usize) -> Result<Self, TrySplitToError>
  where
    Self: Sized,
  {
    if at > self.remaining() {
      Err(TrySplitToError::new(at + 1, self.remaining()))
    } else {
      Ok(self.split_to(at))
    }
  }

  /// Returns `true` if there are remaining bytes in the buffer.
  fn has_remaining(&self) -> bool {
    self.remaining() > 0
  }

  /// Attempts to advance the internal cursor of the `ReadBuf` by the specified number of bytes.
  ///
  /// Returns `Ok(())` if the advancement was successful, or an error if there are not enough bytes remaining.
  fn try_advance(&mut self, cnt: usize) -> Result<(), TryAdvanceError> {
    let remaining = self.remaining();
    if remaining < cnt {
      return Err(TryAdvanceError::new(cnt, remaining));
    }

    self.advance(cnt);
    Ok(())
  }

  /// Attempts to create a new buffer containing a segment of the current buffer's remaining data.
  ///
  /// The returned buffer is independent with its own cursor starting at the beginning of the segment.
  /// The original buffer remains unchanged. This is the non-panicking version of `segment`.
  ///
  /// Returns `None` if the range extends beyond the current buffer's remaining data.
  #[inline]
  fn try_segment(&self, range: impl RangeBounds<usize>) -> Result<Self, TrySegmentError>
  where
    Self: Sized,
  {
    check_segment(range, self.remaining()).map(|(start, end)| self.segment(start..end))
  }

  /// Peeks a fixed-size array from the beginning of the buffer without advancing the internal cursor.
  ///
  /// This method creates a copy of the first `N` bytes from the buffer without
  /// consuming them. The buffer position remains unchanged after this operation.
  ///
  /// # Panics
  /// Panics if the buffer contains fewer than `N` bytes.
  #[inline]
  fn peek_array<const N: usize>(&self) -> [u8; N] {
    self.remaining_slice().try_into().expect("buffer too short")
  }

  /// Peeks a fixed-size array from the beginning of the buffer without advancing the internal cursor,
  /// returning `None` if insufficient data.
  ///
  /// This method safely attempts to create a copy of the first `N` bytes from the buffer
  /// without consuming them. The buffer position remains unchanged after this operation.
  ///
  /// This is a non-panicking version of [`peek_array`](ReadBuf::peek_array).
  #[inline]
  fn peek_array_checked<const N: usize>(&self) -> Option<[u8; N]> {
    match self.remaining_slice().try_into() {
      Ok(data) => Some(data),
      Err(_) => None,
    }
  }

  /// Peeks a fixed-size array from the beginning of the buffer without advancing the internal cursor,
  /// returning `Err` if insufficient data.
  ///
  /// This method safely attempts to create a copy of the first `N` bytes from the buffer
  /// without consuming them. The buffer position remains unchanged after this operation.
  ///
  /// This is a non-panicking version of [`peek_array`](ReadBuf::peek_array).
  #[inline]
  fn try_peek_array<const N: usize>(&self) -> Result<[u8; N], TryPeekError> {
    match self.remaining_slice().try_into() {
      Ok(data) => Ok(data),
      Err(_) => Err(TryPeekError::new(N, self.remaining())),
    }
  }

  peek_fixed!(u16, u32, u64, u128, i16, i32, i64, i128, f32, f64);

  /// Peeks a variable-length encoded type from the buffer without advancing the internal cursor.
  ///
  /// Returns the length of the value and the value itself.
  #[cfg(feature = "varing")]
  #[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
  #[inline]
  fn peek_varint<V: Varint>(&self) -> Result<(usize, V), ReadVarintError> {
    V::decode(self.remaining_slice())
  }

  /// Reads a fixed-size array from the buffer and advances the internal cursor.
  ///
  /// This method creates a copy of the first `N` bytes from the buffer without
  /// consuming them. The buffer position remains unchanged after this operation.
  ///
  /// # Panics
  /// Panics if the buffer contains fewer than `N` bytes.
  #[inline]
  fn read_array<const N: usize>(&mut self) -> [u8; N] {
    let output = self.remaining_slice().try_into().expect("buffer too short");
    self.advance(N);
    output
  }

  /// Try reads a fixed-size array from the beginning of the buffer and advances the internal cursor,
  /// returning `None` if insufficient data.
  ///
  /// This method safely attempts to create a copy of the first `N` bytes from the buffer
  /// without consuming them. The buffer position remains unchanged after this operation.
  ///
  /// This is a non-panicking version of [`read_array`](ReadBuf::read_array).
  #[inline]
  fn read_array_checked<const N: usize>(&mut self) -> Option<[u8; N]> {
    match self.remaining_slice().try_into() {
      Ok(data) => {
        self.advance(N);
        Some(data)
      }
      Err(_) => None,
    }
  }

  /// Try reads a fixed-size array from the beginning of the buffer and advances the internal cursor,
  /// returning `Err` if insufficient data.
  ///
  /// This method safely attempts to create a copy of the first `N` bytes from the buffer
  /// without consuming them. The buffer position remains unchanged after this operation.
  ///
  /// This is a non-panicking version of [`read_array`](ReadBuf::read_array).
  #[inline]
  fn try_read_array<const N: usize>(&mut self) -> Result<[u8; N], TryReadError> {
    match self.remaining_slice().try_into() {
      Ok(data) => {
        self.advance(N);
        Ok(data)
      }
      Err(_) => Err(TryReadError::new(N, self.remaining())),
    }
  }

  read_fixed!(u16, u32, u64, u128, i16, i32, i64, i128, f32, f64);

  /// Peeks an `u8` value from the buffer without advancing the internal cursor.
  ///
  /// # Panics
  /// - If the buffer is too short to read an `u8` value.
  #[inline]
  fn peek_u8(&self) -> u8 {
    self.remaining_slice()[0]
  }

  /// Try to peek an `u8` value from the buffer without advancing the internal cursor,
  /// returning `None` if the buffer is too short.
  ///
  /// This is a non-panicking version of [`peek_u8`](ReadBuf::peek_u8).
  #[inline]
  fn peek_u8_checked(&self) -> Option<u8> {
    self.remaining_slice().get(0).copied()
  }

  /// Reads an `u8` value from the buffer and advances the internal cursor.
  ///
  /// # Panics
  ///
  /// - If the buffer is too short to read an `u8` value.
  #[inline]
  fn read_u8(&mut self) -> u8 {
    let val = self.peek_u8();
    self.advance(1);
    val
  }

  /// Try to read an `u8` value from the buffer and advances the internal cursor,
  /// returning `None` if the buffer is too short.
  ///
  /// This is a non-panicking version of [`read_u8`](ReadBuf::read_u8).
  #[inline]
  fn read_u8_checked(&mut self) -> Option<u8> {
    self.peek_u8_checked().inspect(|_| {
      self.advance(1);
    })
  }

  /// Peeks an `i8` value from the buffer without advancing the internal cursor.
  ///
  /// # Panics
  ///
  /// - If the buffer is too short to read an `i8` value.
  #[inline]
  fn peek_i8(&self) -> i8 {
    self.peek_u8() as i8
  }

  /// Try to peek an `i8` value from the buffer without advancing the internal cursor,
  /// returning `None` if the buffer is too short.
  ///
  /// This is a non-panicking version of [`peek_i8`](ReadBuf::peek_i8).
  #[inline]
  fn peek_i8_checked(&self) -> Option<i8> {
    self.peek_u8_checked().map(|v| v as i8)
  }

  /// Reads an `i8` value from the buffer and advances the internal cursor.
  ///
  /// # Panics
  ///
  /// - If the buffer is too short to read an `i8` value.
  #[inline]
  fn read_i8(&mut self) -> i8 {
    let val = self.peek_i8();
    self.advance(1);
    val
  }

  /// Try to read an `i8` value from the buffer and advances the internal cursor,
  /// returning `None` if the buffer is too short.
  ///
  /// This is a non-panicking version of [`read_i8`](ReadBuf::read_i8).
  #[inline]
  fn read_i8_checked(&mut self) -> Option<i8> {
    self.peek_i8_checked().inspect(|_| {
      self.advance(1);
    })
  }

  /// Reads a variable-length encoded type from the buffer and advances the internal cursor.
  ///
  /// Returns the length of the value read and the value itself.
  #[cfg(feature = "varing")]
  #[cfg_attr(docsrs, doc(cfg(feature = "varing")))]
  #[inline]
  fn read_varint<V: Varint>(&mut self) -> Result<(usize, V), ReadVarintError> {
    V::decode(self.remaining_slice()).map(|(len, val)| {
      self.advance(len);
      (len, val)
    })
  }

  #[cfg(any(feature = "std", feature = "alloc"))]
  #[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
  /// Converts the read buffer to a `Vec<u8>` instance.
  fn to_vec(&self) -> Vec<u8> {
    self.remaining_slice().to_vec()
  }

  #[cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc")))]
  #[cfg_attr(
    docsrs,
    doc(cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc"))))
  )]
  /// Converts the read buffer to a `Bytes` instance.
  fn to_bytes(&self) -> ::bytes_1::Bytes {
    ::bytes_1::Bytes::copy_from_slice(self.remaining_slice())
  }

  #[cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc")))]
  #[cfg_attr(
    docsrs,
    doc(cfg(all(feature = "bytes_1", any(feature = "std", feature = "alloc"))))
  )]
  /// Converts the read buffer to a `BytesMut` instance.
  fn to_bytes_mut(&self) -> ::bytes_1::BytesMut {
    ::bytes_1::BytesMut::from(self.to_bytes())
  }
}

impl ReadBuf for &[u8] {
  #[inline]
  fn empty() -> Self {
    &[]
  }

  #[inline]
  fn remaining(&self) -> usize {
    <[u8]>::len(self)
  }

  #[inline]
  fn has_remaining(&self) -> bool {
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
  fn remaining_slice(&self) -> &[u8] {
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
    fn remaining(&self) -> usize {
      self.len()
    }

    #[inline]
    fn has_remaining(&self) -> bool {
      self.is_empty()
    }

    #[inline]
    fn remaining_slice(&self) -> &[u8] {
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
