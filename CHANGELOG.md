# Changelog

## circular-buffer 0.1.3

* Fix `range()` and `range_mut()` when passing an empty range (contributed by
  Icxolu)

## circular-buffer 0.1.2

* Make `extend_from_slice()` safe by ensuring that all cloned elements get
  dropped in case a panic occurs.
* Optimized all `PartialEq` implementations.
* Fix a [strict-provenance](https://github.com/rust-lang/rust/issues/95228)
  error in `swap()` (contributed by René Kijewski).

## circular-buffer 0.1.1

* Make circular-buffer compatible with the stable version of rustc.

## circular-buffer 0.1.0

* Initial release.
