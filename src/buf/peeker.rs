use core::ops::Bound;

use crate::error::TryAdvanceError;

use super::Buf;

/// A peeker for reading from a buffer without advancing the original buffer's cursor.
/// 
/// `Peeker` provides a non-destructive way to examine buffer contents by maintaining
/// its own independent cursor position. This is particularly useful when you need to:
/// - Look ahead in a buffer before deciding how to process the data
/// - Parse data that might need to be rolled back
/// - Implement backtracking algorithms
/// - Share read access to the same buffer data from different positions
///
/// The peeker can be constrained to a specific range within the buffer, making it
/// safe for parsing operations that should not read beyond certain boundaries.
///
/// # Examples
///
/// ```rust
/// use bufkit::{Buf, Peeker};
///
/// let data = b"Hello, World!";
/// let buf = &data[..];
/// let mut peeker = Peeker::new(&buf);
///
/// // Read without affecting the original buffer
/// assert_eq!(peeker.read_u8(), b'H');
/// assert_eq!(peeker.read_u8(), b'e');
/// assert_eq!(buf.remaining(), 13); // Original buffer unchanged
/// 
/// // Create a constrained peeker for safe parsing
/// let mut word_peeker = peeker.segment(0..5); // "Hello"
/// assert_eq!(word_peeker.remaining(), 5);
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct Peeker<'a, B: ?Sized> {
  buf: &'a B,
  cursor: usize,
  start: usize,
  end: Option<usize>,
}

impl<'a, B: 'a + ?Sized> From<&'a B> for Peeker<'a, B> {
  #[inline]
  fn from(buf: &'a B) -> Self {
    Self::new(buf)
  }
}

impl<'a, B: 'a + ?Sized> Clone for Peeker<'a, B> {
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, B: 'a + ?Sized> Copy for Peeker<'a, B> {}

impl<'a, B: 'a + ?Sized> Peeker<'a, B> {
  /// Creates a new `Peeker` instance with the given buffer.
  ///
  /// The peeker starts at the beginning of the buffer's current position
  /// and can read all remaining bytes in the buffer.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{Buf, Peeker};
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let buf = &data[..];
  /// let peeker = Peeker::new(&buf);
  /// assert_eq!(peeker.remaining(), 5);
  /// ```
  #[inline]
  pub const fn new(buf: &'a B) -> Self {
    Self {
      buf,
      cursor: 0,
      start: 0,
      end: None,
    }
  }

  /// Creates a new `Peeker` constrained to a specific length.
  ///
  /// This is useful when you want to ensure the peeker cannot read beyond
  /// a certain number of bytes, providing additional safety for parsing operations.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{Buf, Peeker};
  ///
  /// let data = b"Hello, World!";
  /// let buf = &data[..];
  /// let peeker = Peeker::with_limit(&buf, 5); // Only peek first 5 bytes
  /// assert_eq!(peeker.remaining(), 5);
  /// ```
  #[inline]
  pub fn with_limit(buf: &'a B, limit: usize) -> Self
  where
    B: Buf,
  {
    Self::with_cursor_and_limit_inner(buf, 0, Some(limit.min(buf.remaining())))
  }

  /// Returns the number of bytes that have been peeked (read) from the underlying buffer.
  ///
  /// This represents how far the peeker's cursor has advanced from its starting position.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{Buf, Peeker};
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let buf = &data[..];
  /// let mut peeker = Peeker::new(&buf);
  ///
  /// assert_eq!(peeker.peeked(), 0);
  /// peeker.read_u8();
  /// assert_eq!(peeker.peeked(), 1);
  /// peeker.advance(2);
  /// assert_eq!(peeker.peeked(), 3);
  /// ```
  #[inline]
  pub const fn peeked(&self) -> usize {
    self.cursor
  }

  /// Resets the peeker's cursor to the beginning.
  ///
  /// After calling this method, the peeker will start reading from the same
  /// position where it was initially created.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bufkit::{Buf, Peeker};
  ///
  /// let data = [1, 2, 3, 4, 5];
  /// let buf = &data[..];
  /// let mut peeker = Peeker::new(&buf);
  ///
  /// peeker.advance(3);
  /// assert_eq!(peeker.peeked(), 3);
  ///
  /// peeker.reset();
  /// assert_eq!(peeker.peeked(), 0);
  /// assert_eq!(peeker.remaining(), 5);
  /// ```
  #[inline]
  pub fn reset(&mut self) {
    self.cursor = 0;
  }

  #[inline]
  const fn with_cursor_and_limit_inner(buf: &'a B, cursor: usize, end: Option<usize>) -> Self {
    Self { buf, cursor, start: cursor, end }
  }
}

impl<'a, B: 'a + Buf + ?Sized> Buf for Peeker<'a, B> {
  #[inline]
  fn remaining(&self) -> usize {
    match self.end {
      Some(end) => end.saturating_sub(self.cursor),
      None => self.buf.remaining().saturating_sub(self.cursor),
    }
  }

  #[inline]
  fn buffer(&self) -> &[u8] {
    let start = self.cursor.min(self.buf.remaining());
    match self.end {
      Some(end) => {
        let actual_end = end.min(self.buf.remaining());
        if start >= actual_end {
          &[]
        } else {
          &self.buf.buffer()[start..actual_end]
        }
      }
      None => {
        if start >= self.buf.remaining() {
          &[]
        } else {
          self.buf.buffer_from(start)
        }
      }
    }
  }

  #[inline]
  fn advance(&mut self, cnt: usize) {
    let remaining = self.remaining();
    if cnt > remaining {
      super::panic_advance(&TryAdvanceError::new(cnt, remaining));
    }
    self.cursor += cnt;
  }

  #[inline]
  fn try_advance(&mut self, cnt: usize) -> Result<(), TryAdvanceError> {
    let remaining = self.remaining();
    if cnt > remaining {
      return Err(TryAdvanceError::new(cnt, remaining));
    }
    self.cursor += cnt;
    Ok(())
  }

  #[inline]
  fn segment(&self, range: impl core::ops::RangeBounds<usize>) -> Self
  where
    Self: Sized,
  {
    let current_remaining = self.remaining();

    let begin = match range.start_bound() {
      Bound::Included(&n) => n,
      Bound::Excluded(&n) => n.checked_add(1).expect("range start overflow"),
      Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
      Bound::Included(&n) => n.checked_add(1).expect("range end overflow"),
      Bound::Excluded(&n) => n,
      Bound::Unbounded => current_remaining,
    };

    assert!(
      begin <= end,
      "range start must not be greater than end: {begin} <= {end}",
    );
    assert!(
      end <= current_remaining,
      "range end out of bounds: {end} <= {current_remaining}",
    );

    if end == begin {
      return Self::with_cursor_and_limit_inner(self.buf, self.cursor, Some(self.cursor));
    }

    Self::with_cursor_and_limit_inner(self.buf, self.cursor + begin, Some(self.cursor + end))
  }

  #[inline]
  fn truncate(&mut self, len: usize) {
    let current_remaining = self.remaining();
    if len >= current_remaining {
      return; // No truncation needed
    }

    let new_end = self.cursor + len;

    match self.end {
      Some(existing_end) => {
        self.end = Some(new_end.min(existing_end));
      }
      None => {
        self.end = Some(new_end);
      }
    }
  }

  #[inline]
  fn split_off(&mut self, at: usize) -> Self
  where
    Self: Sized,
  {
    let remaining = self.remaining();
    assert!(
      at <= remaining,
      "split_off out of bounds: {at} <= {remaining}",
    );

    let new_cursor = self.cursor + at;
    let old_end = self.end;

    // Truncate self to [0, at)
    self.end = Some(self.cursor + at);

    // Return the right part [at, end)
    Self::with_cursor_and_limit_inner(self.buf, new_cursor, old_end)
  }

  #[inline]
  fn split_to(&mut self, at: usize) -> Self
  where
    Self: Sized,
  {
    let remaining = self.remaining();
    assert!(
      at <= remaining,
      "split_to out of bounds: {at} <= {remaining}",
    );

    let old_cursor = self.cursor;
    let new_end = self.cursor + at;

    // Advance self to [at, end)
    self.cursor += at;

    // Return the left part [0, at)
    Self::with_cursor_and_limit_inner(self.buf, old_cursor, Some(new_end))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_peeker_basic_functionality() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    assert_eq!(peeker.remaining(), 5);
    assert_eq!(peeker.peeked(), 0);

    // Read a byte
    assert_eq!(peeker.read_u8(), 1);
    assert_eq!(peeker.remaining(), 4);
    assert_eq!(peeker.peeked(), 1);

    // Original buffer should be unchanged
    assert_eq!(buf.remaining(), 5);
  }

  #[test]
  fn test_peeker_with_limit() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let mut peeker = Peeker::with_limit(&buf, 3);

    assert_eq!(peeker.remaining(), 3);

    // Read within limit
    assert_eq!(peeker.read_u8(), 1);
    assert_eq!(peeker.read_u8(), 2);
    assert_eq!(peeker.read_u8(), 3);

    // Should be at limit now
    assert_eq!(peeker.remaining(), 0);
  }

  #[test]
  fn test_peeker_reset() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    peeker.advance(3);
    assert_eq!(peeker.peeked(), 3);
    assert_eq!(peeker.remaining(), 2);

    peeker.reset();
    assert_eq!(peeker.peeked(), 0);
    assert_eq!(peeker.remaining(), 5);
  }

  #[test]
  fn test_peeker_segment() {
    let data = b"Hello, World!";
    let buf = &data[..];
    let peeker = Peeker::new(&buf);

    // Segment "Hello"
    let mut hello_peeker = peeker.segment(0..5);
    assert_eq!(hello_peeker.remaining(), 5);
    assert_eq!(hello_peeker.read_u8(), b'H');
    assert_eq!(hello_peeker.read_u8(), b'e');

    // Segment "World"
    let mut world_peeker = peeker.segment(7..12);
    assert_eq!(world_peeker.remaining(), 5);
    assert_eq!(world_peeker.read_u8(), b'W');
    assert_eq!(world_peeker.read_u8(), b'o');
  }

  #[test]
  fn test_peeker_truncate() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let mut peeker = Peeker::from(&buf);

    peeker.truncate(3);
    assert_eq!(peeker.remaining(), 3);

    // Should only be able to read 3 bytes
    assert_eq!(peeker.read_u8(), 1);
    assert_eq!(peeker.read_u8(), 2);
    assert_eq!(peeker.read_u8(), 3);
    assert_eq!(peeker.remaining(), 0);

    let mut peeker = Peeker::with_limit(&buf, 3);
    assert_eq!(peeker.remaining(), 3);
    peeker.truncate(2);

    assert_eq!(peeker.remaining(), 2);
  }

  #[test]
  #[should_panic]
  fn test_peeker_split_off_panic() {
    let data = [1u8, 2, 3];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    // This should panic because we are trying to split_off more than available
    let _ = peeker.split_off(5);
  }

  #[test]
  fn test_peeker_split_off() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    let right_peeker = peeker.split_off(2);

    // Left part should have first 2 bytes
    assert_eq!(peeker.remaining(), 2);
    assert_eq!(peeker.read_u8(), 1);
    assert_eq!(peeker.read_u8(), 2);

    // Right part should have remaining bytes
    assert_eq!(right_peeker.remaining(), 3);
    let mut right = right_peeker;
    assert_eq!(right.read_u8(), 3);
    assert_eq!(right.read_u8(), 4);
    assert_eq!(right.read_u8(), 5);
  }

  #[test]
  #[should_panic]
  fn test_peeker_split_to_panic() {
    let data = [1u8, 2, 3];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    // This should panic because we are trying to split_to more than available
    let _ = peeker.split_to(5);
  }

  #[test]
  fn test_peeker_split_to() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    let left_peeker = peeker.split_to(2);

    // Left part should have first 2 bytes
    assert_eq!(left_peeker.remaining(), 2);
    let mut left = left_peeker;
    assert_eq!(left.read_u8(), 1);
    assert_eq!(left.read_u8(), 2);

    // Remaining peeker should have rest
    assert_eq!(peeker.remaining(), 3);
    assert_eq!(peeker.read_u8(), 3);
    assert_eq!(peeker.read_u8(), 4);
    assert_eq!(peeker.read_u8(), 5);
  }

  #[test]
  fn test_peeker_try_advance() {
    let data = [1u8, 2, 3];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    assert!(peeker.try_advance(2).is_ok());
    assert_eq!(peeker.peeked(), 2);

    // Should fail when trying to advance beyond available data
    assert!(peeker.try_advance(5).is_err());
    assert_eq!(peeker.peeked(), 2); // Should remain unchanged
  }

  #[test]
  #[should_panic(expected = "advance")]
  fn test_peeker_advance_panic() {
    let data = [1u8, 2, 3];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    peeker.advance(5); // Should panic
  }

  #[test]
  fn test_peeker_empty_segment() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let peeker = Peeker::new(&buf);

    let empty_peeker = peeker.segment(2..2);
    assert_eq!(empty_peeker.remaining(), 0);
  }

  #[test]
  fn test_peeker_clone_and_copy() {
    let data = [1u8, 2, 3, 4, 5];
    let buf = &data[..];
    let mut peeker = Peeker::new(&buf);

    peeker.advance(2);

    let peeker_clone = peeker.clone();
    let peeker_copy = peeker;

    assert_eq!(peeker_clone.peeked(), 2);
    assert_eq!(peeker_copy.peeked(), 2);
    assert_eq!(peeker_clone.remaining(), peeker_copy.remaining());
  }

  #[test]
  fn test_peeker_with_advanced_buffer() {
    let data = [1u8, 2, 3, 4, 5];
    let mut buf = &data[..];

    // Advance the original buffer
    buf.advance(2);
    assert_eq!(buf.remaining(), 3);

    // Peeker should work with the advanced buffer
    let mut peeker = Peeker::new(&buf);
    assert_eq!(peeker.remaining(), 3);
    assert_eq!(peeker.read_u8(), 3); // Should read the 3rd byte
  }

  #[test]
  #[should_panic]
  fn test_peeker_segment_panic_1() {
    let data = b"Hello, World!";
    let buf = &data[..];
    let peeker = Peeker::new(&buf);

    // This should panic because the segment end is out of bounds
    let _ = peeker.segment(3..1);
  }

  #[test]
  #[should_panic]
  fn test_peeker_segment_panic_2() {
    let data = b"Hello, World!";
    let buf = &data[..];
    let peeker = Peeker::new(&buf);

    // This should panic because the segment end is out of bounds
    let _ = peeker.segment(..20);
  }

  #[test]
  fn test_peeker_multi_level_segments() {
    let data = b"Hello, World!";
    let buf = &data[..];
    let peeker = Peeker::new(&buf);

    // Create a segment, then segment that
    let hello_comma = peeker.segment(0..6); // "Hello,"
    let hello = hello_comma.segment(0..5); // "Hello"

    assert_eq!(hello.remaining(), 5);
    let mut hello_mut = hello;
    assert_eq!(hello_mut.read_u8(), b'H');
    assert_eq!(hello_mut.read_u8(), b'e');
  }
}
