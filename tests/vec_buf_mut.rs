#[cfg(test)]
#[cfg(any(feature = "std", feature = "alloc"))]
mod vec_buf_mut_tests {
  use bufkit::{BufMut, BufMutExt};

  #[test]
  fn test_mutable() {
    let buf = vec![1, 2, 3, 4, 5];
    assert_eq!(buf.mutable(), 5);
    assert!(buf.has_mutable());

    let empty: Vec<u8> = vec![];
    assert_eq!(empty.mutable(), 0);
    assert!(!empty.has_mutable());
  }

  #[test]
  fn test_buffer_mut() {
    let mut buf = vec![1, 2, 3, 4, 5];
    let slice = buf.buffer_mut();
    assert_eq!(slice, &[1, 2, 3, 4, 5]);

    // Modify through buffer_mut
    slice[0] = 10;
    assert_eq!(buf[0], 10);
  }

  #[test]
  fn test_resize() {
    let mut buf = vec![1, 2, 3];

    // Grow
    buf.resize(5, 0xFF);
    assert_eq!(buf, vec![1, 2, 3, 0xFF, 0xFF]);

    // Shrink
    buf.resize(2, 0x00);
    assert_eq!(buf, vec![1, 2]);

    // Same size
    buf.resize(2, 0x11);
    assert_eq!(buf, vec![1, 2]);
  }

  #[test]
  fn test_try_resize() {
    let mut buf = vec![1, 2, 3];

    // Try grow - should succeed for Vec
    assert!(buf.try_resize(5, 0xFF).is_ok());
    assert_eq!(buf, vec![1, 2, 3, 0xFF, 0xFF]);

    // Try shrink
    assert!(buf.try_resize(2, 0x00).is_ok());
    assert_eq!(buf, vec![1, 2]);
  }

  #[test]
  fn test_truncate_mut() {
    let mut buf = vec![1, 2, 3, 4, 5];

    buf.truncate_mut(3);
    assert_eq!(buf, vec![1, 2, 3]);

    // Truncating to larger size has no effect
    buf.truncate_mut(10);
    assert_eq!(buf, vec![1, 2, 3]);

    buf.truncate_mut(0);
    assert_eq!(buf, vec![]);
  }

  #[test]
  fn test_fill() {
    let mut buf = vec![1, 2, 3, 4];
    buf.fill(0xFF);
    assert_eq!(buf, vec![0xFF, 0xFF, 0xFF, 0xFF]);
  }

  #[test]
  fn test_prefix_suffix_mut() {
    let mut buf = vec![1, 2, 3, 4, 5];

    // Prefix
    let prefix = buf.prefix_mut(3);
    prefix.fill(0xFF);
    assert_eq!(buf, vec![0xFF, 0xFF, 0xFF, 4, 5]);

    // Suffix
    let mut buf = vec![1, 2, 3, 4, 5];
    let suffix = buf.suffix_mut(2);
    suffix.fill(0xAA);
    assert_eq!(buf, vec![1, 2, 3, 0xAA, 0xAA]);
  }

  #[test]
  fn test_split_at_mut() {
    let mut buf = vec![1, 2, 3, 4, 5];
    let (left, right) = buf.split_at_mut(2);

    left.fill(0xFF);
    right.fill(0xAA);
    assert_eq!(buf, vec![0xFF, 0xFF, 0xAA, 0xAA, 0xAA]);
  }

  #[test]
  fn test_put_slice() {
    let mut buf = vec![0; 10];

    let written = buf.put_slice(&[1, 2, 3]);
    assert_eq!(written, 3);
    assert_eq!(&buf[..3], &[1, 2, 3]);

    // Put at start again (overwrites)
    let written = buf.put_slice(&[4, 5]);
    assert_eq!(written, 2);
    assert_eq!(&buf[..3], &[4, 5, 3]);
  }

  #[test]
  fn test_put_slice_at() {
    let mut buf = vec![0; 10];

    let written = buf.put_slice_at(&[1, 2, 3], 2);
    assert_eq!(written, 3);
    assert_eq!(&buf[2..5], &[1, 2, 3]);

    let written = buf.put_slice_at(&[4, 5], 7);
    assert_eq!(written, 2);
    assert_eq!(&buf[7..9], &[4, 5]);
  }

  #[test]
  #[should_panic]
  fn test_put_slice_at_panic() {
    let mut buf = vec![0; 5];
    buf.put_slice_at(&[1, 2, 3], 4); // Should panic
  }

  #[test]
  fn test_put_primitives() {
    let mut buf = vec![0; 20];

    // u8
    assert_eq!(buf.put_u8(0xFF), 1);
    assert_eq!(buf[0], 0xFF);

    // u16
    assert_eq!(buf.put_u16_le(0x1234), 2);
    assert_eq!(&buf[0..2], &[0x34, 0x12]);

    assert_eq!(buf.put_u16_be(0x5678), 2);
    assert_eq!(&buf[0..2], &[0x56, 0x78]);

    // u32
    assert_eq!(buf.put_u32_le(0x12345678), 4);
    assert_eq!(&buf[0..4], &[0x78, 0x56, 0x34, 0x12]);

    // f32
    assert_eq!(buf.put_f32_le(1.0), 4);
    assert_eq!(&buf[0..4], &1.0f32.to_le_bytes());
  }

  #[test]
  fn test_put_primitives_at() {
    let mut buf = vec![0; 20];

    assert_eq!(buf.put_u8_at(0xFF, 5), 1);
    assert_eq!(buf[5], 0xFF);

    assert_eq!(buf.put_u16_le_at(0x1234, 10), 2);
    assert_eq!(&buf[10..12], &[0x34, 0x12]);

    assert_eq!(buf.put_u32_be_at(0x12345678, 15), 4);
    assert_eq!(&buf[15..19], &[0x12, 0x34, 0x56, 0x78]);
  }

  #[test]
  fn test_checked_methods() {
    let mut buf = vec![0; 5];

    assert!(buf.put_slice_checked(&[1, 2, 3]).is_some());
    assert!(buf.put_slice_checked(&[1, 2, 3, 4, 5, 6]).is_none());

    assert!(buf.put_u32_le_checked(0x12345678).is_some());

    let mut small_buf = vec![0; 1];
    assert!(small_buf.put_u32_le_checked(0x12345678).is_none());
  }

  #[test]
  fn test_try_methods() {
    let mut buf = vec![0; 5];

    assert!(buf.try_put_slice(&[1, 2, 3]).is_ok());

    let err = buf.try_put_slice(&[1, 2, 3, 4, 5, 6]).unwrap_err();
    assert_eq!(err.requested(), 6);
    assert_eq!(err.available(), 5);

    assert!(buf.try_put_u32_le(0x12345678).is_ok());

    let mut small_buf = vec![0; 1];
    let err = small_buf.try_put_u32_le(0x12345678).unwrap_err();
    assert_eq!(err.requested(), 4);
    assert_eq!(err.available(), 1);
  }

  #[test]
  fn test_vec_growth() {
    let mut buf = vec![1, 2, 3];

    // Vec can grow beyond initial capacity
    buf.resize(10, 0xFF);
    assert_eq!(buf.len(), 10);
    assert_eq!(&buf[3..], &[0xFF; 7]);

    // Can put data in grown area
    assert_eq!(buf.put_slice_at(&[0xAA, 0xBB], 8), 2);
    assert_eq!(&buf[8..10], &[0xAA, 0xBB]);
  }

  #[cfg(feature = "varing")]
  #[test]
  fn test_put_varint() {
    let mut buf = vec![0; 10];

    let written = buf.put_varint(&42u32).unwrap();
    assert!(written > 0);

    let written = buf.put_varint_at(&100u64, 5).unwrap();
    assert!(written > 0);
  }
}
