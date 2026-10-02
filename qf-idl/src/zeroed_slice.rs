use crate::algebra::Zero;

pub(crate) struct ZeroedSlice<'a, T>(&'a mut [T]);

impl<'a, T> ZeroedSlice<'a, T> {
    fn new(slice: &'a mut [T]) -> Self
    where
        T: Zero + Clone,
    {
        slice.fill(T::ZERO);
        Self(slice)
    }

    pub(crate) fn into_mut(self) -> &'a mut [T] {
        self.0
    }
}
