

use core::convert::Infallible;

use crate::CircularBuffer;

impl<const N: usize> embedded_io::ErrorType for CircularBuffer<N,u8>
{
    type Error = Infallible;
}

impl<const N: usize>  embedded_io::Write for CircularBuffer<N,u8>{
    #[inline]
    fn write(&mut self, src: &[u8]) -> Result<usize,Self::Error> {
        self.extend_from_slice(src);
        Ok(src.len())
    }

    #[inline]
    fn flush(&mut self) -> Result<(),Self::Error> {
        Ok(())
    }
}

impl<const N: usize>  embedded_io::Read for CircularBuffer<N,u8>
{
    fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        let (mut front, mut back) = self.as_slices();
        let mut count = front.read(dst)?;
        count += back.read(&mut dst[count..])?;
        self.truncate_front(self.len() - count);
        Ok(count)
    }
}



impl<const N: usize>  embedded_io::BufRead for CircularBuffer<N,u8>
{
    fn consume(&mut self, amt: usize) {
        let amt = core::cmp::min(amt, self.len());
        self.drain(..amt);
    }

    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        let (front, back) = self.as_slices();
        if !front.is_empty() {
            Ok(front)
        } else {
            Ok(back)
        }
    }
}




impl<const N: usize> embedded_io_async::Write for CircularBuffer<N,u8>{
    async fn flush(&mut self) ->Result<(), Self::Error> {
        Ok(())
    }

    async fn write(&mut self, src: &[u8]) -> Result<usize, Self::Error> {
        self.extend_from_slice(src);
        Ok(src.len())
    }
}


impl<const N: usize> embedded_io_async::Read for CircularBuffer<N,u8>{
    async fn read(&mut self, dst: &mut [u8]) -> Result<usize, Self::Error> {
        let (mut front, mut back) = self.as_slices();
        let mut count = front.read(dst).await?;
        count += back.read(&mut dst[count..]).await?;
        self.truncate_front(self.len() - count);
        Ok(count)
    }
}



impl<const N: usize> embedded_io_async::BufRead for CircularBuffer<N,u8>{
    fn consume(&mut self, amt: usize) {
        let amt = core::cmp::min(amt, self.len());
        self.drain(..amt);
    }

   async fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        let (front, back) = self.as_slices();
        if !front.is_empty() {
            Ok(front)
        } else {
            Ok(back)
        }
    }
}


