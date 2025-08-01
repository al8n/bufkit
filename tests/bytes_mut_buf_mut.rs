#![allow(unused_imports)]

#[cfg(test)]
#[cfg(all(feature = "bytes_1", feature = "std"))]
mod bytes_mut_buf_mut_tests {
  use bufkit::{error::TryWriteAtError, BufMut, BufMutExt};
  use bytes_1::BytesMut;

  #[test]
  fn test_mutable() {
    let buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);
    assert_eq!(buf.mutable(), 5);
    assert!(buf.has_mutable());

    let empty = BytesMut::new();
    assert_eq!(empty.mutable(), 0);
    assert!(!empty.has_mutable());
  }

  #[test]
  fn test_buffer_mut() {
    let mut buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);
    let slice = buf.buffer_mut();
    assert_eq!(slice, &[1, 2, 3, 4, 5]);

    // Modify through buffer_mut
    slice[0] = 10;
    assert_eq!(buf[0], 10);
  }

  #[test]
  fn test_truncate_mut() {
    let mut buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);

    buf.truncate_mut(3);
    assert_eq!(&buf[..], &[1, 2, 3]);

    // Truncating to larger size has no effect
    buf.truncate_mut(10);
    assert_eq!(&buf[..], &[1, 2, 3]);

    buf.truncate_mut(0);
    assert!(!buf.has_mutable());
  }

  #[test]
  fn test_fill() {
    let mut buf = BytesMut::from(&[1, 2, 3, 4][..]);
    buf.fill(0xFF);
    assert_eq!(&buf[..], &[0xFF, 0xFF, 0xFF, 0xFF]);
  }

  #[test]
  fn test_prefix_suffix_mut() {
    let mut buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);

    // Prefix
    let prefix = buf.prefix_mut(3);
    prefix.fill(0xFF);
    assert_eq!(&buf[..], &[0xFF, 0xFF, 0xFF, 4, 5]);

    // Suffix
    let mut buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);
    let suffix = buf.suffix_mut(2);
    suffix.fill(0xAA);
    assert_eq!(&buf[..], &[1, 2, 3, 0xAA, 0xAA]);
  }

  #[test]
  fn test_split_at_mut() {
    let mut buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);
    let (left, right) = buf.split_at_mut(2);

    left.fill(0xFF);
    right.fill(0xAA);
    assert_eq!(&buf[..], &[0xFF, 0xFF, 0xAA, 0xAA, 0xAA]);
  }

  #[test]
  fn test_put_slice() {
    let mut buf = BytesMut::from(&[0; 10][..]);

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
    let mut buf = BytesMut::from(&[0; 10][..]);

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
    let mut buf = BytesMut::from(&[0; 5][..]);
    buf.put_slice_at(&[1, 2, 3], 4); // Should panic
  }

  #[test]
  fn test_put_primitives() {
    let mut buf = BytesMut::from(&[0; 20][..]);

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
    let mut buf = BytesMut::from(&[0; 20][..]);

    assert_eq!(buf.put_u8_at(0xFF, 5), 1);
    assert_eq!(buf[5], 0xFF);

    assert_eq!(buf.put_u16_le_at(0x1234, 10), 2);
    assert_eq!(&buf[10..12], &[0x34, 0x12]);

    assert_eq!(buf.put_u32_be_at(0x12345678, 15), 4);
    assert_eq!(&buf[15..19], &[0x12, 0x34, 0x56, 0x78]);
  }

  #[test]
  fn test_checked_methods() {
    let mut buf = BytesMut::from(&[0; 5][..]);

    assert!(buf.put_slice_checked(&[1, 2, 3]).is_some());
    assert!(buf.put_slice_checked(&[1, 2, 3, 4, 5, 6]).is_none());

    assert!(buf.put_u32_le_checked(0x12345678).is_some());

    let mut small_buf = BytesMut::from(&[0; 1][..]);
    assert!(small_buf.put_u32_le_checked(0x12345678).is_none());
  }

  #[test]
  fn test_try_methods() {
    let mut buf = BytesMut::from(&[0; 5][..]);

    assert!(buf.try_put_slice(&[1, 2, 3]).is_ok());

    let err = buf.try_put_slice(&[1, 2, 3, 4, 5, 6]).unwrap_err();
    assert_eq!(err.requested(), 6);
    assert_eq!(err.available(), 5);

    assert!(buf.try_put_u32_le(0x12345678).is_ok());

    let mut small_buf = BytesMut::from(&[0; 1][..]);
    let err = small_buf.try_put_u32_le(0x12345678).unwrap_err();
    assert_eq!(err.requested(), 4);
    assert_eq!(err.available(), 1);
  }

  #[test]
  fn test_bytes_mut_specific_features() {
    // Test capacity management
    let mut buf = BytesMut::with_capacity(100);
    assert!(buf.capacity() >= 100);

    buf.extend_from_slice(&[1, 2, 3, 4, 5]);
    assert_eq!(buf.mutable(), 5);

    // Test split_off behavior
    let buf2 = buf.split_off(3);
    assert_eq!(&buf[..], &[1, 2, 3]);
    assert_eq!(&buf2[..], &[4, 5]);

    // Test freeze to immutable Bytes
    let bytes = buf.freeze();
    assert_eq!(&bytes[..], &[1, 2, 3]);
  }

  #[test]
  fn test_native_endian() {
    let mut buf = BytesMut::from(&[0; 20][..]);

    assert_eq!(buf.put_u16_ne(0x1234), 2);
    assert_eq!(&buf[0..2], &0x1234u16.to_ne_bytes());

    assert_eq!(buf.put_u32_ne(0x12345678), 4);
    assert_eq!(&buf[0..4], &0x12345678u32.to_ne_bytes());
    assert_eq!(buf.put_u64_ne(0x123456789ABCDEF0), 8);
    assert_eq!(&buf[0..8], &0x123456789ABCDEF0u64.to_ne_bytes());
  }

  #[test]
  fn test_signed_integers() {
    let mut buf = BytesMut::from(&[0; 20][..]);

    assert_eq!(buf.put_i8(-42), 1);
    assert_eq!(buf[0] as i8, -42);

    assert_eq!(buf.put_i16_le(-1000), 2);
    assert_eq!(&buf[0..2], &(-1000i16).to_le_bytes());

    assert_eq!(buf.put_i32_be(-123456), 4);
    assert_eq!(&buf[0..4], &(-123456i32).to_be_bytes());

    assert_eq!(buf.put_i64_ne(-999999999), 8);
    assert_eq!(&buf[0..8], &(-999999999i64).to_ne_bytes());
  }

  #[test]
  fn test_floating_point() {
    let mut buf = BytesMut::from(&[0; 20][..]);

    assert_eq!(buf.put_f32_le(3.14159), 4);
    assert_eq!(&buf[0..4], &3.14159f32.to_le_bytes());

    assert_eq!(buf.put_f64_be(2.71828), 8);
    assert_eq!(&buf[0..8], &2.71828f64.to_be_bytes());

    assert_eq!(buf.put_f32_ne(-0.5), 4);
    assert_eq!(&buf[0..4], &(-0.5f32).to_ne_bytes());
  }

  #[test]
  fn test_128_bit_integers() {
    let mut buf = BytesMut::from(&[0; 32][..]);

    let val_u128 = 0x0123456789ABCDEF0123456789ABCDEFu128;
    let val_i128 = -0x0123456789ABCDEF0123456789ABCDEFi128;

    assert_eq!(buf.put_u128_le(val_u128), 16);
    assert_eq!(&buf[0..16], &val_u128.to_le_bytes());

    assert_eq!(buf.put_i128_be(val_i128), 16);
    assert_eq!(&buf[0..16], &val_i128.to_be_bytes());
  }

  #[test]
  fn test_try_put_at_methods() {
    let mut buf = BytesMut::from(&[0; 10][..]);

    // Success cases
    assert!(buf.try_put_u8_at(0xFF, 5).is_ok());
    assert!(buf.try_put_u16_le_at(0x1234, 8).is_ok());

    // Out of bounds offset
    let err = buf.try_put_u8_at(0xFF, 10).unwrap_err();
    match err {
      TryWriteAtError::OutOfBounds(e) => {
        assert_eq!(e.offset(), 10);
        assert_eq!(e.length(), 10);
      }
      _ => panic!("Expected OutOfBounds error"),
    }

    // Insufficient space
    let err = buf.try_put_u32_le_at(0x12345678, 8).unwrap_err();
    match err {
      TryWriteAtError::InsufficientSpace(e) => {
        assert_eq!(e.requested(), 4);
        assert_eq!(e.available(), 2);
        assert_eq!(e.offset(), 8);
      }
      _ => panic!("Expected InsufficientSpace error"),
    }
  }

  #[cfg(feature = "varing")]
  #[test]
  fn test_put_varint() {
    let mut buf = BytesMut::from(&[0; 10][..]);

    let written = buf.put_varint(&42u32).unwrap();
    assert!(written > 0);

    let written = buf.put_varint_at(&100u64, 5).unwrap();
    assert!(written > 0);

    // Test insufficient space
    let mut small_buf = BytesMut::from(&[0; 1][..]);
    let result = small_buf.put_varint(&u64::MAX); // This will need more than 1 byte
    assert!(result.is_err());
  }

  #[test]
  fn test_prefix_suffix_checked() {
    let mut buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);

    assert!(buf.prefix_mut_checked(3).is_some());
    assert!(buf.prefix_mut_checked(10).is_none());

    assert!(buf.suffix_mut_checked(2).is_some());
    assert!(buf.suffix_mut_checked(10).is_none());
  }

  #[test]
  fn test_split_at_mut_checked() {
    let mut buf = BytesMut::from(&[1, 2, 3, 4, 5][..]);

    assert!(buf.split_at_mut_checked(3).is_some());
    assert!(buf.split_at_mut_checked(10).is_none());
  }
}
