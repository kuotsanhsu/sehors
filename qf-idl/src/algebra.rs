pub(crate) trait Zero {
    const ZERO: Self;
}

pub(crate) trait Monoid:
    std::cmp::PartialEq + Sized + std::ops::Add<Output = Self> + Zero
{
}

pub(crate) trait Group: Monoid + std::ops::Neg<Output = Self> {}
