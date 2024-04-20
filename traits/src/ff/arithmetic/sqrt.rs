use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Constant-time implementation of Tonelli–Shanks' square-root algorithm for
/// `p mod 16 = 1`.
///
/// `tm1d2` should be set to `(t - 1) // 2`, where `t = (modulus - 1) >> F::S`.
///
/// ## Implementing [`Field::sqrt`]
///
/// This function can be used to implement [`Field::sqrt`] for fields that both implement
/// [`PrimeField`] and satisfy `p mod 16 = 1`.
///
/// [`Field::sqrt`]: crate::Field::sqrt
pub fn sqrt_tonelli_shanks<F: crate::ff::PrimeField, S: AsRef<[u64]>>(
    f: &F,
    tm1d2: S,
) -> CtOption<F> {
    // This is a constant-time version of https://eprint.iacr.org/2012/685.pdf (page 12,
    // algorithm 5). Steps 2-5 of the algorithm are omitted because they are only needed
    // to detect non-square input; it is more efficient to do that by checking at the end
    // whether the square of the result is the input.

    // w = self^((t - 1) // 2)
    let w = f.pow_vartime(tm1d2);

    let mut v = F::S;
    let mut x = w * f;
    let mut b = x * w;

    // Initialize z as the 2^S root of unity.
    let mut z = F::ROOT_OF_UNITY;

    for max_v in (1..=F::S).rev() {
        let mut k = 1;
        let mut b2k = b.square();
        let mut j_less_than_v: Choice = 1.into();

        // This loop has three phases based on the value of k for algorithm 5:
        // - for j <= k, we square b2k in order to calculate b^{2^k}.
        // - for k < j <= v, we square z in order to calculate ω.
        // - for j > v, we do nothing.
        for j in 2..max_v {
            let b2k_is_one = b2k.ct_eq(&F::ONE);
            let squared = F::conditional_select(&b2k, &z, b2k_is_one).square();
            b2k = F::conditional_select(&squared, &b2k, b2k_is_one);
            let new_z = F::conditional_select(&z, &squared, b2k_is_one);
            j_less_than_v &= !j.ct_eq(&v);
            k = u32::conditional_select(&j, &k, b2k_is_one);
            z = F::conditional_select(&z, &new_z, j_less_than_v);
        }

        let result = x * z;
        x = F::conditional_select(&result, &x, b.ct_eq(&F::ONE));
        z = z.square();
        b *= z;
        v = k;
    }

    CtOption::new(
        x,
        (x * x).ct_eq(f), // Only return Some if it's the square root.
    )
}
