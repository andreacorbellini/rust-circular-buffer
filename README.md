# Circular Buffer for Rust

[![Crate](https://img.shields.io/crates/v/circular-buffer)](https://crates.io/crates/circular-buffer) [![Documentation](https://img.shields.io/docsrs/circular-buffer)](https://docs.rs/circular-buffer/latest/circular_buffer/) [![License](https://img.shields.io/crates/l/circular-buffer)](https://choosealicense.com/licenses/bsd-3-clause/)

This is a Rust crate that implements a [circular buffer], also known as cyclic
buffer, circular queue or ring.

This circular buffer has a fixed maximum capacity, does not automatically grow,
and once its maximum capacity is reached, elements at the start of the buffer
are overwritten. It's useful for implementing fast FIFO (_first in, first out_)
and LIFO (_last in, first out_) queues with a fixed memory capacity.

For more information and examples, check out the [documentation]!

[circular buffer]: https://en.wikipedia.org/wiki/Circular_buffer
[documentation]: https://docs.rs/circular-buffer/latest/circular_buffer/
