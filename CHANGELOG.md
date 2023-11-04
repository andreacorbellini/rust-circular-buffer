# Changelog

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
