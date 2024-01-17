use core::fmt;

impl<const N: usize, T> Debug for CircularBuffer<N, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}
