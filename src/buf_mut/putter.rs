use crate::error::TryAdvanceError;

use super::{BufMut, WriteBuf};

/// A putter for writing to a buffer without modifying the original buffer's cursor.
///
/// `Putter` provides a non-destructive way to write buffer contents by maintaining
/// its own independent cursor position. This is particularly useful when you need to:
/// - Preview write operations before committing them
/// - Write data that might need to be rolled back
/// - Implement transactional write operations
/// - Share write access to the same buffer data from different positions
/// - Test serialization without modifying the original buffer
///
/// The putter can be constrained to a specific range within the buffer, making it
/// safe for write operations that should not exceed certain boundaries.
///
/// # Examples
///
/// ```rust
/// use bufkit::{BufMut, Putter};
///
/// let mut data = [0u8; 10];
/// let mut putter = Putter::new(&mut data[..]);  // No need for &mut &mut
///
/// // Write without affecting the original buffer's cursor
/// putter.put_u8(0x42);
/// putter.put_u16_le(0x1234);
///
/// // Original buffer's state is unchanged until we access it
/// // The writes are staged in the putter's view
/// ```
#[derive(Debug)]
pub struct Putter<B: ?Sized> {
  /// Current cursor position relative to the buffer's current position
  cursor: usize,
  /// The original start position of the putter, used for reset_positionting.
  start: usize,
  /// The original limit of the putter, used for reset_positionting.
  end: Option<usize>,
  /// Current limit of the putter
  limit: Option<usize>,
  /// The underlying buffer wrapped in WriteBuf for ergonomic access
  buf: WriteBuf<B>,
}

impl<B: BufMut> From<B> for Putter<B> {
  #[inline]
  fn from(buf: B) -> Self {
    Self::new(buf)
  }
}

impl<B> Putter<B> {
  /// Creates a new `Putter` instance with the given buffer.
  ///
  /// The putter starts at the beginning of the buffer's current position
  /// and can write to all remaining space in the buffer.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, Putter};
  ///
  /// let mut data = [0u8; 10];
  /// let putter = Putter::new(&mut data[..]);
  /// assert_eq!(putter.remaining_mut(), 10);
  /// ```
  #[inline]
  pub fn new(buf: impl Into<WriteBuf<B>>) -> Self
  where
    B: BufMut,
  {
    Self {
      buf: buf.into(),
      cursor: 0,
      start: 0,
      end: None,
      limit: None,
    }
  }

  /// Creates a new `Putter` instance with the given buffer.
  ///
  /// The putter starts at the beginning of the buffer's current position
  /// and can write to all remaining space in the buffer.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, Putter};
  ///
  /// let mut data = [0u8; 10];
  /// let mut slice: &mut [u8] = &mut data[..];
  /// let putter = Putter::const_new(&mut slice);
  /// assert_eq!(putter.remaining_mut(), 10);
  /// ```
  #[inline]
  pub const fn const_new(buf: B) -> Self {
    Self {
      buf: WriteBuf::new(buf),
      cursor: 0,
      start: 0,
      end: None,
      limit: None,
    }
  }

  /// Creates a new `Putter` constrained to a specific length.
  ///
  /// This is useful when you want to ensure the putter cannot write beyond
  /// a certain number of bytes, providing additional safety for serialization operations.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, Putter};
  ///
  /// let mut data = [0u8; 10];
  /// let putter = Putter::with_limit(&mut data[..], 5); // Only write first 5 bytes
  /// assert_eq!(putter.remaining_mut(), 5);
  /// ```
  #[inline]
  pub fn with_limit(buf: impl Into<WriteBuf<B>>, limit: usize) -> Self
  where
    B: BufMut,
  {
    let write_buf = buf.into();
    let actual_limit = limit.min(write_buf.remaining_mut());
    Self::with_cursor_and_limit_inner(write_buf, 0, Some(actual_limit))
  }

  /// Returns the number of bytes that have been written through the putter.
  ///
  /// This represents how far the putter's cursor has advanced from its starting position.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, Putter};
  ///
  /// let mut data = [0u8; 10];
  /// let mut putter = Putter::new(&mut data[..]);
  ///
  /// assert_eq!(putter.written(), 0);
  /// putter.put_u8(0x42);
  /// assert_eq!(putter.written(), 1);
  /// putter.advance_mut(2);
  /// assert_eq!(putter.written(), 3);
  /// ```
  #[inline]
  pub const fn written(&self) -> usize {
    self.cursor.saturating_sub(self.start)
  }

  /// Resets the putter's to the initial state.
  ///
  /// After calling this method, the putter will start writing from the same
  /// position and the same limit where it was initially created.
  ///
  /// This method will not clean the dirty state of the putter, which means
  /// any previously written data will still be present in the buffer. See also [`reset`](Putter::reset).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, Putter};
  ///
  /// let mut data = [0u8; 10];
  /// let mut putter = Putter::new(&mut data[..]);
  ///
  /// putter.advance_mut(3);
  /// assert_eq!(putter.written(), 3);
  ///
  /// putter.reset_position();
  /// assert_eq!(putter.written(), 0);
  /// assert_eq!(putter.remaining_mut(), 10);
  /// ```
  #[inline]
  pub const fn reset_position(&mut self) {
    self.cursor = self.start;
    self.limit = self.end;
  }

  /// Resets the putter's buffer to its initial state, filling the written area with zeros.
  ///
  /// This method clears the buffer's contents from the start position to the limit position,
  /// effectively resetting the buffer to a clean state.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{BufMut, Putter};
  ///
  /// let mut data = [0u8; 10];
  /// let mut putter = Putter::new(&mut data[..]);
  ///
  /// putter.put_u8(0x42);
  /// assert_eq!(putter.buffer_mut()[0], 0x42);
  ///
  /// putter.reset();
  /// assert_eq!(putter.buffer_mut()[0], 0x00); // The first byte is reset to zero
  ///
  /// let mut data = [1u8; 10];
  ///
  /// let mut putter = Putter::with_limit(&mut data[..], 5);
  /// putter.put_u8(0x42);
  /// assert_eq!(putter.buffer_mut()[0], 0x42);
  ///
  /// putter.reset();
  /// assert_eq!(&putter.buffer_mut()[..5], [0x00; 5].as_slice()); // The first five bytes are reset to zero
  ///
  /// drop(putter);
  /// assert_eq!(&data[..5], [0x00; 5].as_slice()); // The first five bytes of the original buffer are reset to zero
  /// assert_eq!(&data[5..], [1; 5].as_slice()); // The rest remains unchanged
  /// ```
  pub fn reset(&mut self)
  where
    B: BufMut,
  {
    match self.end {
      Some(end) => {
        let start = self.start;
        self.buf.buffer_mut()[start..end].fill(0);
      }
      None => {
        let start = self.start;
        self.buf.buffer_mut_from(start).fill(0);
      }
    }

    self.reset_position();
  }

  #[inline]
  fn with_cursor_and_limit_inner(buf: WriteBuf<B>, cursor: usize, limit: Option<usize>) -> Self {
    Self {
      buf,
      cursor,
      start: cursor,
      end: limit,
      limit,
    }
  }
}

impl<B: BufMut + ?Sized> BufMut for Putter<B> {
  #[inline]
  fn remaining_mut(&self) -> usize {
    match self.limit {
      Some(end) => end.saturating_sub(self.cursor),
      None => self.buf.remaining_mut().saturating_sub(self.cursor),
    }
  }

  #[inline]
  fn buffer_mut(&mut self) -> &mut [u8] {
    let start = self.cursor.min(self.buf.remaining_mut());
    match self.limit {
      Some(end) => &mut self.buf.buffer_mut()[start..end],
      None => self.buf.buffer_mut_from(start),
    }
  }

  #[inline]
  fn advance_mut(&mut self, cnt: usize) {
    let remaining = self.remaining_mut();
    if cnt > remaining {
      super::panic_advance(&TryAdvanceError::new(cnt, remaining));
    }
    self.cursor += cnt;
  }

  #[inline]
  fn try_advance_mut(&mut self, cnt: usize) -> Result<(), TryAdvanceError> {
    let remaining = self.remaining_mut();
    if cnt > remaining {
      return Err(TryAdvanceError::new(cnt, remaining));
    }
    self.cursor += cnt;
    Ok(())
  }

  #[inline]
  fn truncate_mut(&mut self, new_len: usize) {
    let current_remaining = self.remaining_mut();
    if new_len >= current_remaining {
      return; // No truncation needed
    }

    let new_end = self.cursor + new_len;

    match self.limit {
      Some(existing_end) => {
        self.limit = Some(new_end.min(existing_end));
      }
      None => {
        self.limit = Some(new_end);
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_putter_basic_functionality() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    assert_eq!(putter.remaining_mut(), 10);
    assert_eq!(putter.written(), 0);

    // Write a byte
    putter.write_u8(0x42);
    assert_eq!(putter.remaining_mut(), 9);
    assert_eq!(putter.written(), 1);

    // Check that the data was written
    assert_eq!(data[0], 0x42);
  }

  #[test]
  fn test_putter_ergonomic_api() {
    // Test the improved ergonomics - no need for &mut &mut
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]); // Clean!

    putter.put_u8(0x11);
    assert_eq!(data[0], 0x11);
  }

  #[test]
  fn test_putter_with_limit() {
    let mut data = [0u8; 10];
    let mut putter = Putter::with_limit(&mut data[..], 3);

    assert_eq!(putter.remaining_mut(), 3);

    // Write within limit
    putter.write_u8(0x11);
    putter.write_u8(0x22);
    putter.write_u8(0x33);

    // Should be at limit now
    assert_eq!(putter.remaining_mut(), 0);

    // Check that data was written correctly
    assert_eq!(data[0], 0x11);
    assert_eq!(data[1], 0x22);
    assert_eq!(data[2], 0x33);
    assert_eq!(data[3], 0x00); // Unchanged
  }

  #[test]
  fn test_putter_reset_position() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    putter.advance_mut(3);
    assert_eq!(putter.written(), 3);
    assert_eq!(putter.remaining_mut(), 7);

    putter.reset_position();
    assert_eq!(putter.written(), 0);
    assert_eq!(putter.remaining_mut(), 10);
  }

  #[test]
  fn test_putter_truncate() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    putter.truncate_mut(3);
    assert_eq!(putter.remaining_mut(), 3);

    // Should only be able to write 3 bytes
    putter.write_u8(0x11);
    putter.write_u8(0x22);
    putter.write_u8(0x33);
    assert_eq!(putter.remaining_mut(), 0);

    // Check data
    assert_eq!(data[0], 0x11);
    assert_eq!(data[1], 0x22);
    assert_eq!(data[2], 0x33);
    assert_eq!(data[3], 0x00); // Unchanged
  }

  #[test]
  fn test_putter_try_advance() {
    let mut data = [0u8; 5];
    let mut putter = Putter::new(&mut data[..]);

    assert!(putter.try_advance_mut(2).is_ok());
    assert_eq!(putter.written(), 2);

    // Should fail when trying to advance beyond available space
    assert!(putter.try_advance_mut(5).is_err());
    assert_eq!(putter.written(), 2); // Should remain unchanged
  }

  #[test]
  #[should_panic(expected = "advance")]
  fn test_putter_advance_panic() {
    let mut data = [0u8; 3];
    let mut putter = Putter::new(&mut data[..]);

    putter.advance_mut(5); // Should panic
  }

  #[test]
  fn test_putter_with_different_integer_types() {
    let mut data = [0u8; 20];
    let mut putter = Putter::new(&mut data[..]);

    // Test little-endian writes
    putter.write_u16_le(0x1234);
    putter.write_u32_le(0x56789ABC);
    assert_eq!(putter.written(), 6);

    // Verify the data was written correctly
    assert_eq!(&data[0..2], &[0x34, 0x12]); // u16 LE
    assert_eq!(&data[2..6], &[0xBC, 0x9A, 0x78, 0x56]); // u32 LE
  }

  #[test]
  fn test_putter_write_slice() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    let test_data = [0x11, 0x22, 0x33, 0x44];
    putter.write_slice(&test_data);

    assert_eq!(putter.written(), 4);
    assert_eq!(&data[0..4], &test_data);
    assert_eq!(data[4], 0x00); // Unchanged
  }

  #[test]
  fn test_putter_with_advanced_buffer() {
    let mut data = [0u8; 10];
    let mut buf = &mut data[..];

    // Advance the original buffer
    buf.advance_mut(3);
    assert_eq!(buf.remaining_mut(), 7);

    // Putter should work with the advanced buffer
    let mut putter = Putter::new(buf);
    assert_eq!(putter.remaining_mut(), 7);
    putter.put_u8(0x42);

    drop(putter);

    // Should write to the correct position
    assert_eq!(data[3], 0x42); // Position 3 in original array
  }

  #[test]
  fn test_putter_buffer_mut_access() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    // Write some data first
    putter.write_u8(0x11);
    putter.write_u8(0x22);

    // Access the remaining buffer
    let remaining_buffer = putter.buffer_mut();
    remaining_buffer[0] = 0x99; // Should write to position 2 in original

    assert_eq!(data[0], 0x11);
    assert_eq!(data[1], 0x22);
    assert_eq!(data[2], 0x99);
  }

  #[test]
  fn test_putter_state_consistency() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    // Verify invariants are maintained through operations
    let initial_remaining = putter.remaining_mut();
    let initial_written = putter.written();

    // After advance
    putter.advance_mut(3);
    assert_eq!(putter.remaining_mut() + putter.written(), initial_remaining);

    // After truncate
    putter.truncate_mut(5);
    assert_eq!(putter.remaining_mut(), 5);
    assert_eq!(putter.written(), 3);

    // After reset_position
    putter.reset_position();
    assert_eq!(putter.written(), initial_written);
    assert_eq!(putter.remaining_mut(), initial_remaining); // back to initial state
  }

  #[test]
  fn test_putter_exhaustive_write() {
    let mut data = [0u8; 3];
    let mut putter = Putter::new(&mut data[..]);

    // Write all bytes one by one
    assert_eq!(putter.write_u8(0x11), 1);
    assert_eq!(putter.remaining_mut(), 2);

    assert_eq!(putter.write_u8(0x22), 1);
    assert_eq!(putter.remaining_mut(), 1);

    assert_eq!(putter.write_u8(0x33), 1);
    assert_eq!(putter.remaining_mut(), 0);

    drop(putter);

    // Verify data
    assert_eq!(data, [0x11, 0x22, 0x33]);
  }

  #[test]
  fn test_putter_from_trait() {
    let mut data = [0u8; 10];

    // Test From trait implementation
    let putter: Putter<_> = (&mut data[..]).into();
    assert_eq!(putter.remaining_mut(), 10);
  }

  #[test]
  fn test_putter_endianness() {
    let mut data = [0u8; 16];
    let mut putter = Putter::new(&mut data[..]);

    // Test different endianness
    putter.write_u16_le(0x1234);
    putter.write_u16_be(0x1234);
    putter.write_u32_le(0x12345678);
    putter.write_u32_be(0x12345678);

    // Verify little-endian
    assert_eq!(&data[0..2], &[0x34, 0x12]);
    // Verify big-endian
    assert_eq!(&data[2..4], &[0x12, 0x34]);
    // Verify little-endian u32
    assert_eq!(&data[4..8], &[0x78, 0x56, 0x34, 0x12]);
    // Verify big-endian u32
    assert_eq!(&data[8..12], &[0x12, 0x34, 0x56, 0x78]);
  }

  #[test]
  fn test_putter_signed_values() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    // Test signed values
    putter.write_i8(-1);
    putter.write_i16_le(-1);
    putter.write_i32_be(-1);

    // Verify i8
    assert_eq!(data[0], 0xFF);
    // Verify i16 LE
    assert_eq!(&data[1..3], &[0xFF, 0xFF]);
    // Verify i32 BE
    assert_eq!(&data[3..7], &[0xFF, 0xFF, 0xFF, 0xFF]);
  }

  #[test]
  fn test_putter_reset_position_preserves_limits() {
    let mut data = [0u8; 10];
    let mut putter = Putter::with_limit(&mut data[..], 5);

    putter.advance_mut(3);
    assert_eq!(putter.written(), 3);
    assert_eq!(putter.remaining_mut(), 2);

    putter.reset_position();
    assert_eq!(putter.written(), 0);
    assert_eq!(putter.remaining_mut(), 5); // Should still be limited to 5
  }

  #[test]
  fn test_putter_truncate_after_advance() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    putter.advance_mut(3);
    assert_eq!(putter.remaining_mut(), 7);

    putter.truncate_mut(4);
    assert_eq!(putter.remaining_mut(), 4);

    // Write to verify the truncation works
    putter.write_slice(&[0x11, 0x22, 0x33, 0x44]);
    assert_eq!(putter.remaining_mut(), 0);

    // Verify data was written starting from position 3
    assert_eq!(&data[3..7], &[0x11, 0x22, 0x33, 0x44]);
  }

  #[test]
  fn test_putter_truncate_limited_putter() {
    let mut data = [0u8; 10];
    let mut putter = Putter::with_limit(&mut data[..], 6);

    assert_eq!(putter.remaining_mut(), 6);

    // Truncate within the limit
    putter.truncate_mut(4);
    assert_eq!(putter.remaining_mut(), 4);

    // Further truncation
    putter.truncate_mut(2);
    assert_eq!(putter.remaining_mut(), 2);
  }

  #[test]
  fn test_error_details() {
    let mut data = [0u8; 3];
    let mut putter = Putter::new(&mut data[..]);

    // Test TryAdvanceError
    let advance_err = putter.try_advance_mut(5).unwrap_err();
    assert_eq!(advance_err.requested(), 5);
    assert_eq!(advance_err.available(), 3);
  }

  #[test]
  fn test_putter_large_data() {
    // Test with larger buffer to ensure no performance issues
    let mut large_data = [0u8; 1000];
    let mut putter = Putter::new(&mut large_data[..]);

    assert_eq!(putter.remaining_mut(), 1000);

    // Write some data
    for i in 0..100 {
      putter.write_u8(i as u8);
    }

    assert_eq!(putter.remaining_mut(), 900);
    assert_eq!(putter.written(), 100);

    // Verify data
    for i in 0..100 {
      assert_eq!(large_data[i], i as u8);
    }
  }

  #[test]
  fn test_putter_boundary_conditions() {
    // Test with single byte buffer
    let mut single_byte = [0u8; 1];
    let mut putter = Putter::new(&mut single_byte[..]);

    assert_eq!(putter.remaining_mut(), 1);
    putter.write_u8(0x42);
    assert_eq!(putter.remaining_mut(), 0);

    // Operations on exhausted putter
    assert!(putter.try_advance_mut(1).is_err());
    assert_eq!(putter.put_u8_checked(0x99), None);
    assert!(putter.try_put_u8(0x99).is_err());

    // Reset should work
    putter.reset_position();
    assert_eq!(putter.remaining_mut(), 1);
  }

  #[test]
  fn test_putter_with_limit_larger_than_buffer() {
    let mut data = [0u8; 3];
    let putter = Putter::with_limit(&mut data[..], 10);

    // Should be limited by buffer size, not the requested limit
    assert_eq!(putter.remaining_mut(), 3);
  }

  #[test]
  fn test_putter_with_limit_zero() {
    let mut data = [0u8; 5];
    let putter = Putter::with_limit(&mut data[..], 0);

    assert_eq!(putter.remaining_mut(), 0);
  }

  #[test]
  fn test_written_calculation() {
    let mut data = [0u8; 10];
    let mut putter = Putter::new(&mut data[..]);

    // Test written calculation with different operations
    assert_eq!(putter.written(), 0);

    putter.advance_mut(2);
    assert_eq!(putter.written(), 2);

    putter.write_u8(0x42);
    assert_eq!(putter.written(), 3);

    putter.write_slice(&[1, 2, 3]);
    assert_eq!(putter.written(), 6);

    // Reset and verify
    putter.reset_position();
    assert_eq!(putter.written(), 0);
  }

  #[test]
  fn test_putter_ergonomic_comparison() {
    let mut data = [0u8; 10];

    // Before: awkward double reference
    // let mut buf = &mut data[..];
    // let mut putter = Putter::new(&mut buf);  // &mut &mut [u8]

    // After: clean and natural
    let mut putter = Putter::new(&mut data[..]); // Just &mut [u8]

    putter.write_u8(0x42);
    assert_eq!(putter.written(), 1);

    drop(putter);
    assert_eq!(data[0], 0x42);
  }
}
