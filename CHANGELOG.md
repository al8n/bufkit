# RELEASED

## 0.5.0 (Aug 14th, 2025)

- Add consume and scan varint related methods for `ChunkExt`
- Change type of `requested` from `usize` to `NonZeroUsize`
- Bumpup `varing` to `0.10`
- Change feature `varing` to feature `varint`

## 0.4.0 (Aug 11st, 2025)

- Rename `bufkit::{Buf, BufMut}` to `bufkit::{Chunk, ChunkMut}` to avoid collisions with `bytes::{Buf, BufMut}`.

## 0.3.0 (Aug 8th, 2025)

- Add `RefPeeker`, `Peeker` and `Putter`

## 0.2.2 (Aug 6th, 2025)

- Add `WriteBuf` for convenient trait API design

## 0.2.0 (Aug 6th, 2025)

- Remove `BufMut` implementation for `BytesMut` and `Vec<u8>`
- Add `advance_mut` and `try_advance_mut` for `BufMut`
- Add `write_*` and `try_write_*` APIs

## 0.1.4 (Aug 5th, 2025)

- Add `buffer_from` and `buffer_from_checked`

## 0.1.3 (Aug 3rd, 2025)

- Change `requested: usize` to `requested: NonZeroUsize`

## 0.1.2 (Aug 2nd, 2025)

- Finish basic implementation
