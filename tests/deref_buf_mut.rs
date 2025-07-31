#![allow(unused_imports)]

#[cfg(test)]
mod deref_impl_tests {
  use bufkit::{BufMut, BufMutExt};

  #[test]
  fn test_buf_mut_deref_impl() {
    // Test that &mut T where T: BufMut also implements BufMut
    let mut data = vec![0u8; 20];
    let mut buf_mut_ref: &mut dyn BufMut = &mut data;

    // Test through double reference
    let buf_mut_ref_ref = &mut buf_mut_ref;

    assert_eq!(buf_mut_ref_ref.mutable(), 20);
    assert!(buf_mut_ref_ref.has_mutable());

    // Test all forwarded methods work correctly
    assert_eq!(buf_mut_ref_ref.put_u8(0xFF), 1);
    assert_eq!(buf_mut_ref_ref.put_u16_le(0x1234), 2);
    assert_eq!(buf_mut_ref_ref.put_u32_be(0x12345678), 4);

    buf_mut_ref_ref.fill(0xAA);
    assert!(data.iter().all(|&b| b == 0xAA));
  }

  #[test]
  #[cfg(any(feature = "std", feature = "alloc"))]
  fn test_box_buf_mut_impl() {
    use std::boxed::Box;

    // Test that Box<T> where T: BufMut also implements BufMut
    let data = vec![0u8; 10];
    let mut boxed: Box<Vec<u8>> = Box::new(data);

    assert_eq!(boxed.mutable(), 10);
    assert!(boxed.has_mutable());

    assert_eq!(boxed.put_slice(&[1, 2, 3]), 3);
    assert_eq!(&boxed[..3], &[1, 2, 3]);

    boxed.resize(5, 0xFF);
    assert_eq!(boxed.len(), 5);

    // Test with trait object
    let mut boxed_trait: Box<dyn BufMut> = Box::new(vec![0u8; 15]);
    assert_eq!(boxed_trait.mutable(), 15);
    assert_eq!(boxed_trait.put_u64_le(0x123456789ABCDEF0), 8);
  }

  #[test]
  fn test_multiple_deref_levels() {
    let mut data = [0u8; 10];
    let mut slice = &mut data[..];
    let mut ref1 = &mut slice;
    let ref2 = &mut ref1;

    // Should work through multiple levels of indirection
    assert_eq!(ref2.put_u32_le(0x12345678), 4);
    assert_eq!(&data[..4], &[0x78, 0x56, 0x34, 0x12]);
  }

  #[test]
  fn test_buf_mut_ext_through_deref() {
    let mut data = vec![0u8; 10];
    let buf_ref = &mut data;

    // BufMutExt methods should also work through deref
    #[cfg(feature = "varing")]
    {
      let result = buf_ref.put_varint(&42u32);
      assert!(result.is_ok());
    }
  }

  #[test]
  fn test_checked_and_try_methods_through_deref() {
    let mut data = vec![0u8; 3];
    let buf_ref: &mut dyn BufMut = &mut data;

    // Checked methods
    assert!(buf_ref.put_slice_checked(&[1, 2, 3]).is_some());
    assert!(buf_ref.put_slice_checked(&[1, 2, 3, 4, 5, 6]).is_none());

    // Try methods
    assert!(buf_ref.try_put_u16_le(0x1234).is_ok());
    assert!(buf_ref.try_put_u32_le(0x12345678).is_err());
  }

  #[test]
  fn test_at_methods_through_deref() {
    let mut data = [0u8; 20];
    let mut slice = &mut data[..];
    let buf_ref = &mut slice;

    assert_eq!(buf_ref.put_u8_at(0xFF, 5), 1);
    assert_eq!(buf_ref.put_u16_le_at(0x1234, 10), 2);
    assert_eq!(buf_ref.put_u32_be_at(0x12345678, 15), 4);

    assert_eq!(data[5], 0xFF);
    assert_eq!(&data[10..12], &[0x34, 0x12]);
    assert_eq!(&data[15..19], &[0x12, 0x34, 0x56, 0x78]);
  }

  #[test]
  fn test_complex_types_through_deref() {
    let mut data = vec![0u8; 50];
    let buf_ref: &mut dyn BufMut = &mut data;

    // Test all numeric types
    assert_eq!(buf_ref.put_i8(-42), 1);
    assert_eq!(buf_ref.put_i16_le(-1000), 2);
    assert_eq!(buf_ref.put_i32_be(-123456), 4);
    assert_eq!(buf_ref.put_i64_ne(-999999999), 8);
    assert_eq!(buf_ref.put_i128_le(-1), 16);

    assert_eq!(buf_ref.put_f32_le(3.14), 4);
    assert_eq!(buf_ref.put_f64_be(2.718), 8);
  }

  #[test]
  fn test_resize_and_truncate_through_deref() {
    let mut data = vec![1, 2, 3, 4, 5];
    let buf_ref: &mut dyn BufMut = &mut data;

    buf_ref.truncate_mut(3);
    assert_eq!(buf_ref.mutable(), 3);

    buf_ref.resize(5, 0xFF);
    assert_eq!(buf_ref.mutable(), 5);

    // Verify the data
    assert_eq!(&data[..], &[1, 2, 3, 0xFF, 0xFF]);
  }

  #[test]
  fn test_split_and_prefix_suffix_through_deref() {
    let mut data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let mut slice = &mut data[..];
    let buf_ref = &mut slice;

    // Test prefix/suffix
    let prefix = buf_ref.prefix_mut(3);
    prefix.fill(0xFF);
    assert_eq!(&data[..3], &[0xFF, 0xFF, 0xFF]);

    let mut data2 = [1, 2, 3, 4, 5];
    let mut slice2 = &mut data2[..];
    let buf_ref2 = &mut slice2;

    let suffix = buf_ref2.suffix_mut(2);
    suffix.fill(0xAA);
    assert_eq!(&data2[3..], &[0xAA, 0xAA]);
  }
}
