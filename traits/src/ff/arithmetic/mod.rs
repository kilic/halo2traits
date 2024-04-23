pub mod inverse;
pub mod jacobi;
pub mod sqrt;
pub mod u64;

/// Exponentiates `self` by `exp`, where `exp` is a little-endian order integer
/// exponent.
///
/// # Guarantees
///
/// This operation is constant time with respect to `self`, for all exponents with the
/// same number of digits (`exp.as_ref().len()`). It is variable time with respect to
/// the number of digits in the exponent.
pub fn pow<F: crate::ff::Field, S: AsRef<[u64]>>(u: &F, exp: S) -> F {
    let mut res = F::ONE;
    for e in exp.as_ref().iter().rev() {
        for i in (0..64).rev() {
            res = res.square();
            let mut tmp = res;
            tmp *= u;
            res.conditional_assign(&tmp, (((*e >> i) & 1) as u8).into());
        }
    }
    res
}

/// Exponentiates `self` by `exp`, where `exp` is a little-endian order integer
/// exponent.
///
/// # Guarantees
///
/// **This operation is variable time with respect to `self`, for all exponent.** If
/// the exponent is fixed, this operation is effectively constant time. However, for
/// stronger constant-time guarantees, [`Field::pow`] should be used.
pub fn pow_vartime<F: crate::ff::Field, S: AsRef<[u64]>>(u: &F, exp: S) -> F {
    let mut res = F::ONE;
    for e in exp.as_ref().iter().rev() {
        for i in (0..64).rev() {
            res = res.square();

            if ((*e >> i) & 1) == 1 {
                res.mul_assign(u);
            }
        }
    }

    res
}
