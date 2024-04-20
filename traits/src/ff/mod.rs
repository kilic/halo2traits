pub mod arithmetic;
pub mod repr;

pub mod utils;

use rand_core::RngCore;

/// This trait represents an element of a field.
pub trait Field:
    crate::ff::repr::FieldReprRaw
    + Eq
    + Copy
    + Clone
    + Default
    + Send
    + Sync
    + core::fmt::Debug
    + 'static
    + subtle::ConditionallySelectable
    + subtle::ConstantTimeEq
    + core::ops::Neg<Output = Self>
    + core::ops::Add<Output = Self>
    + core::ops::Sub<Output = Self>
    + core::ops::Mul<Output = Self>
    + core::iter::Sum
    + core::iter::Product
    + for<'a> core::ops::Add<&'a Self, Output = Self>
    + for<'a> core::ops::Sub<&'a Self, Output = Self>
    + for<'a> core::ops::Mul<&'a Self, Output = Self>
    + for<'a> core::iter::Sum<&'a Self>
    + for<'a> core::iter::Product<&'a Self>
    + core::ops::AddAssign
    + core::ops::SubAssign
    + core::ops::MulAssign
    + for<'a> core::ops::AddAssign<&'a Self>
    + for<'a> core::ops::SubAssign<&'a Self>
    + for<'a> core::ops::MulAssign<&'a Self>
    + From<u64>
{
    /// The zero element of the field, the additive identity.
    const ZERO: Self;

    /// The one element of the field, the multiplicative identity.
    const ONE: Self;

    /// Returns an element chosen uniformly at random using a user-provided RNG.
    fn random(rng: impl RngCore) -> Self;

    /// Returns true iff this element is zero.
    fn is_zero(&self) -> subtle::Choice {
        self.ct_eq(&Self::ZERO)
    }

    /// Interpret a string of decimal digits as a (congruent) field element.
    fn from_decimal_str(s: &str) -> Option<Self> {
        crate::ff::utils::from_str(s, 10)
    }

    /// Interpret a string of hex digits as a (congruent) field element.
    fn from_hex_str(s: &str) -> Option<Self> {
        crate::ff::utils::from_str(s, 16)
    }

    /// Squares this element.
    #[must_use]
    fn square(&self) -> Self {
        *self * self
    }

    /// Doubles this element.
    #[must_use]
    fn double(&self) -> Self {
        *self + self
    }

    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self) -> subtle::CtOption<Self>;

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> subtle::CtOption<Self>;

    /// Exponentiates `self` by `exp`, where `exp` is a little-endian order integer
    /// exponent.
    ///
    /// # Guarantees
    ///
    /// This operation is constant time with respect to `self`, for all exponents with the
    /// same number of digits (`exp.as_ref().len()`). It is variable time with respect to
    /// the number of digits in the exponent.
    fn pow<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        crate::ff::arithmetic::pow(self, exp)
    }

    /// Exponentiates `self` by `exp`, where `exp` is a little-endian order integer
    /// exponent.
    ///
    /// # Guarantees
    ///
    /// **This operation is variable time with respect to `self`, for all exponent.** If
    /// the exponent is fixed, this operation is effectively constant time. However, for
    /// stronger constant-time guarantees, [`Field::pow`] should be used.
    fn pow_vartime<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        crate::ff::arithmetic::pow_vartime(self, exp)
    }

    /// Returns a field element that is congruent to the provided little endian unsigned
    /// byte representation of an integer.
    fn from_uniform_bytes(bytes: &[u8]) -> Self;
}

pub trait PrimeField: Field {
    /// Returns true iff this element is odd.
    fn is_odd(&self) -> subtle::Choice {
        subtle::Choice::from(self.to_repr::<crate::ff::repr::LE>().as_ref()[0] & 1)
    }

    /// Returns true iff this element is even.
    #[inline(always)]
    fn is_even(&self) -> subtle::Choice {
        !self.is_odd()
    }

    /// How many bits are needed to represent an element of this field.
    const NUM_BITS: u32;

    /// Inverse of $2$ in the field.
    const TWO_INV: Self;

    /// A fixed multiplicative generator of `modulus - 1` order. This element must also be
    /// a quadratic nonresidue.
    ///
    /// It can be calculated using [SageMath] as `GF(modulus).primitive_element()`.
    ///
    /// Implementations of this trait MUST ensure that this is the generator used to
    /// derive `Self::ROOT_OF_UNITY`.
    ///
    /// [SageMath]: https://www.sagemath.org/
    const MULTIPLICATIVE_GENERATOR: Self;

    /// An integer `s` satisfying the equation `2^s * t = modulus - 1` with `t` odd.
    ///
    /// This is the number of leading zero bits in the little-endian bit representation of
    /// `modulus - 1`.
    const S: u32;

    /// The `2^s` root of unity.
    ///
    /// It can be calculated by exponentiating `Self::MULTIPLICATIVE_GENERATOR` by `t`,
    /// where `t = (modulus - 1) >> Self::S`.
    const ROOT_OF_UNITY: Self;

    /// Inverse of [`Self::ROOT_OF_UNITY`].
    const ROOT_OF_UNITY_INV: Self;

    /// Generator of the `t-order` multiplicative subgroup.
    ///
    /// It can be calculated by exponentiating [`Self::MULTIPLICATIVE_GENERATOR`] by `2^s`,
    /// where `s` is [`Self::S`].
    const DELTA: Self;

    /// A field element of small multiplicative order $N$.
    ///
    /// The presense of this element allows you to perform (certain types of)
    /// endomorphisms on some elliptic curves.
    ///
    /// It can be calculated using [SageMath] as
    /// `GF(modulus).primitive_element() ^ ((modulus - 1) // N)`.
    /// Choosing the element of order $N$ that is smallest, when considered
    /// as an integer, may help to ensure consistency.
    ///
    /// [SageMath]: https://www.sagemath.org/
    const ZETA: Self;
}

pub trait Legendre {
    fn legendre(&self) -> i64;

    #[inline(always)]
    fn ct_quadratic_non_residue(&self) -> subtle::Choice {
        use subtle::ConstantTimeEq;
        self.legendre().ct_eq(&-1)
    }

    #[inline(always)]
    fn ct_quadratic_residue(&self) -> subtle::Choice {
        // The legendre symbol returns 0 for 0
        // and 1 for quadratic residues,
        // we consider 0 a square hence quadratic residue.
        use subtle::ConstantTimeEq;
        self.legendre().ct_ne(&-1)
    }
}
