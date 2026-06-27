// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(any(feature = "embedded-io", feature = "embedded-io-async"))]

use crate::CircularBuffer;
use crate::FixedCircularBuffer;
use core::convert::Infallible;
use core::ops::DerefMut;

#[cfg(feature = "alloc")]
use crate::HeapCircularBuffer;

#[cfg(feature = "embedded-io")]
use embedded_io::ErrorType;

#[cfg(all(feature = "embedded-io-async", not(feature = "embedded-io")))]
use embedded_io_async::ErrorType;

impl ErrorType for CircularBuffer<u8> {
    type Error = Infallible;
}

#[cfg(feature = "embedded-io")]
impl embedded_io::Write for CircularBuffer<u8> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> Result<usize, Self::Error> {
        self.extend_from_slice(src);
        Ok(src.len())
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[cfg(feature = "embedded-io")]
impl embedded_io::Read for CircularBuffer<u8> {
    fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        let (mut front, mut back) = self.as_slices();
        let mut count = front.read(dst)?;
        count += back.read(&mut dst[count..])?;
        let truncate_to = self.len() - count;
        self.truncate_front(truncate_to);
        Ok(count)
    }
}

#[cfg(feature = "embedded-io")]
impl embedded_io::BufRead for CircularBuffer<u8> {
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        let (front, back) = self.as_slices();
        if !front.is_empty() {
            Ok(front)
        } else {
            Ok(back)
        }
    }

    fn consume(&mut self, amt: usize) {
        let amt = core::cmp::min(amt, self.len());
        self.drain(..amt);
    }
}

#[cfg(feature = "embedded-io-async")]
impl embedded_io_async::Write for CircularBuffer<u8> {
    #[inline]
    async fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    #[inline]
    async fn write(&mut self, src: &[u8]) -> Result<usize, Self::Error> {
        self.extend_from_slice(src);
        Ok(src.len())
    }
}

#[cfg(feature = "embedded-io-async")]
impl embedded_io_async::Read for CircularBuffer<u8> {
    async fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        let (mut front, mut back) = self.as_slices();
        let mut count = front.read(dst).await?;
        count += back.read(&mut dst[count..]).await?;
        let truncate_to = self.len() - count;
        self.truncate_front(truncate_to);
        Ok(count)
    }
}

#[cfg(feature = "embedded-io-async")]
impl embedded_io_async::BufRead for CircularBuffer<u8> {
    async fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        let (front, back) = self.as_slices();
        if !front.is_empty() {
            Ok(front)
        } else {
            Ok(back)
        }
    }

    fn consume(&mut self, amt: usize) {
        let amt = core::cmp::min(amt, self.len());
        self.drain(..amt);
    }
}

impl<const N: usize> ErrorType for FixedCircularBuffer<u8, N> {
    type Error = Infallible;
}

#[cfg(feature = "embedded-io")]
impl<const N: usize> embedded_io::Write for FixedCircularBuffer<u8, N> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> Result<usize, Self::Error> {
        self.deref_mut().write(src)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Self::Error> {
        self.deref_mut().flush()
    }
}

#[cfg(feature = "embedded-io")]
impl<const N: usize> embedded_io::Read for FixedCircularBuffer<u8, N> {
    #[inline]
    fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        self.deref_mut().read(dst)
    }
}

#[cfg(feature = "embedded-io")]
impl<const N: usize> embedded_io::BufRead for FixedCircularBuffer<u8, N> {
    #[inline]
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        self.deref_mut().fill_buf()
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        self.deref_mut().consume(amt)
    }
}

#[cfg(feature = "embedded-io-async")]
impl<const N: usize> embedded_io_async::Write for FixedCircularBuffer<u8, N> {
    #[inline]
    async fn flush(&mut self) -> Result<(), Self::Error> {
        self.deref_mut().flush().await
    }

    #[inline]
    async fn write(&mut self, src: &[u8]) -> Result<usize, Self::Error> {
        self.deref_mut().write(src).await
    }
}

#[cfg(feature = "embedded-io-async")]
impl<const N: usize> embedded_io_async::Read for FixedCircularBuffer<u8, N> {
    #[inline]
    async fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        self.deref_mut().read(dst).await
    }
}

#[cfg(feature = "embedded-io-async")]
impl<const N: usize> embedded_io_async::BufRead for FixedCircularBuffer<u8, N> {
    #[inline]
    async fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        self.deref_mut().fill_buf().await
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        self.deref_mut().consume(amt)
    }
}

#[cfg(feature = "alloc")]
impl ErrorType for HeapCircularBuffer<u8> {
    type Error = Infallible;
}

#[cfg(feature = "alloc")]
#[cfg(feature = "embedded-io")]
impl embedded_io::Write for HeapCircularBuffer<u8> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> Result<usize, Self::Error> {
        self.deref_mut().write(src)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Self::Error> {
        self.deref_mut().flush()
    }
}

#[cfg(feature = "alloc")]
#[cfg(feature = "embedded-io")]
impl embedded_io::Read for HeapCircularBuffer<u8> {
    #[inline]
    fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        self.deref_mut().read(dst)
    }
}

#[cfg(feature = "alloc")]
#[cfg(feature = "embedded-io")]
impl embedded_io::BufRead for HeapCircularBuffer<u8> {
    #[inline]
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        self.deref_mut().fill_buf()
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        self.deref_mut().consume(amt)
    }
}

#[cfg(feature = "alloc")]
#[cfg(feature = "embedded-io-async")]
impl embedded_io_async::Write for HeapCircularBuffer<u8> {
    #[inline]
    async fn flush(&mut self) -> Result<(), Self::Error> {
        self.deref_mut().flush().await
    }

    #[inline]
    async fn write(&mut self, src: &[u8]) -> Result<usize, Self::Error> {
        self.deref_mut().write(src).await
    }
}

#[cfg(feature = "alloc")]
#[cfg(feature = "embedded-io-async")]
impl embedded_io_async::Read for HeapCircularBuffer<u8> {
    #[inline]
    async fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        self.deref_mut().read(dst).await
    }
}

#[cfg(feature = "alloc")]
#[cfg(feature = "embedded-io-async")]
impl embedded_io_async::BufRead for HeapCircularBuffer<u8> {
    #[inline]
    async fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        self.deref_mut().fill_buf().await
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        self.deref_mut().consume(amt)
    }
}
