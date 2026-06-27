// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::FixedCircularBuffer;
use std::cmp;
use std::io::BufRead;
use std::io::Read;
use std::io::Result;
use std::io::Write;

impl<const N: usize> Write for FixedCircularBuffer<u8, N> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> Result<usize> {
        self.extend_from_slice(src);
        Ok(src.len())
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

impl<const N: usize> Read for FixedCircularBuffer<u8, N> {
    fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
        let (mut front, mut back) = self.as_slices();
        let mut count = front.read(dst)?;
        count += back.read(&mut dst[count..])?;
        let truncate_to = self.len() - count;
        self.truncate_front(truncate_to);
        Ok(count)
    }
}

impl<const N: usize> BufRead for FixedCircularBuffer<u8, N> {
    fn fill_buf(&mut self) -> Result<&[u8]> {
        let (front, back) = self.as_slices();
        if !front.is_empty() {
            Ok(front)
        } else {
            Ok(back)
        }
    }

    fn consume(&mut self, amt: usize) {
        let amt = cmp::min(amt, self.len());
        self.drain(..amt);
    }
}
