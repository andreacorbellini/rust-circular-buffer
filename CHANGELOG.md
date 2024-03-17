# Changelog

## circular-buffer 0.1.7

### New features

* Implemented the traits
  [`Index<usize>`](https://doc.rust-lang.org/std/ops/trait.Index.html) and
  [`IndexMut<usize>`](https://doc.rust-lang.org/std/ops/trait.IndexMut.html)
  for `CircularBuffer`. Now elements of the buffer can be accessed and modified
  with indexing operations (`buf[index]`), like in the following example:

  ```rust
  use circular_buffer::CircularBuffer;
  let mut buf = CircularBuffer::<5, char>::from(['a', 'b', 'c']);
  assert_eq!(buf[0], 'a');
  buf[1] = 'd';
  assert_eq!(buf[1], 'd');
  ```

* Added new methods to fill the whole buffer, or the spare capacity of the
  buffer:
  [`fill()`](https://docs.rs/circular-buffer/0.1.7/circular_buffer/struct.CircularBuffer.html#method.fill),
  [`fill_with()`](https://docs.rs/circular-buffer/0.1.7/circular_buffer/struct.CircularBuffer.html#method.fill_with),
  [`fill_spare()`](https://docs.rs/circular-buffer/0.1.7/circular_buffer/struct.CircularBuffer.html#method.fill_spare),
  [`fill_spare_with()`](https://docs.rs/circular-buffer/0.1.7/circular_buffer/struct.CircularBuffer.html#method.fill_spare_with).

* Added a new `alloc` feature that brings heap-allocation features to `no_std`
  environments through the [`alloc`](https://doc.rust-lang.org/stable/alloc/)
  crate ([contributed by
  Haoud](https://github.com/andreacorbellini/rust-circular-buffer/pull/11)).

* Implemented the
  [`BufRead`](https://doc.rust-lang.org/std/io/trait.BufRead.html) trait for
  `CircularBuffer` (not available in `no_std` environments).

### Bug fixes

* Fixed an out-of-bounds read in
  [`remove()`](https://docs.rs/circular-buffer/0.1.7/circular_buffer/struct.CircularBuffer.html#method.remove).

* Removed `#[must_use]` from
  [`drain()`](https://docs.rs/circular-buffer/0.1.7/circular_buffer/struct.CircularBuffer.html#method.drain):
  it is perfectly acceptable to ignore the return value from this method.

### Other changes

* Raised the minimum rustc version to 1.65

## circular-buffer 0.1.6

* Fixed a bug in bug in bug in the `PartialEq` implementation that would lead
  to a panic in some circumstances.

## circular-buffer 0.1.5

* Added `try_push_back()` and `try_push_front()` as non-overwriting
  alternatives to `push_back()` and `push_front()` ([contributed by Rinat
  Shigapov](https://github.com/andreacorbellini/rust-circular-buffer/pull/5)).
* Added `drain()` to remove ranges of elements.
* Added `make_contiguous()` to return a contiguous mutable slice of elements.
* `Iter` and `IterMut` now implement the `Default` trait.

## circular-buffer 0.1.4

* Fixed a bug in `range()` and `range_mut()` that made them return more
  elements than requested in some circumstances.

## circular-buffer 0.1.3

* Fixed `range()` and `range_mut()` when passing an empty range ([contributed
  by Icxolu](https://github.com/andreacorbellini/rust-circular-buffer/pull/4)).

## circular-buffer 0.1.2

* Made `extend_from_slice()` safe by ensuring that all cloned elements get
  dropped in case a panic occurs.
* Optimized all `PartialEq` implementations.
* Fixed a [strict-provenance](https://github.com/rust-lang/rust/issues/95228)
  error in `swap()` ([contributed by René
  Kijewski](https://github.com/andreacorbellini/rust-circular-buffer/pull/2)).

## circular-buffer 0.1.1

* Made circular-buffer compatible with the stable version of rustc.

## circular-buffer 0.1.0

* Initial release.
