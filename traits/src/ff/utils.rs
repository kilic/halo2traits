pub(crate) fn from_str<F: crate::ff::Field>(s: &str, radix: u32) -> Option<F> {
    if radix != 10 && radix != 16 {
        panic!("only radix 10 and 16 are supported")
    }

    if s.is_empty() {
        return None;
    }
    if s == "0" {
        return Some(F::ZERO);
    }
    if s == "-1" {
        return Some(-F::ONE);
    }
    let mut res = F::ZERO;

    for c in s.chars() {
        match c.to_digit(radix) {
            Some(c) => {
                res.mul_assign(&(radix as u64).into());
                res.add_assign(&(c as u64).into());
            }
            None => {
                return None;
            }
        }
    }
    Some(res)
}

#[cfg(feature = "big")]
pub mod biguint {

    pub trait BigUintExt: crate::ff::Field {
        fn modulus() -> num_bigint::BigUint {
            Self::to_big(&-Self::ONE) + 1usize
        }

        fn from_big(e: &num_bigint::BigUint) -> Self {
            let bytes = e.to_bytes_le();
            let mut repr = Self::Repr::default();
            repr.as_mut()[..bytes.len()].copy_from_slice(&bytes[..]);
            Self::from_repr::<crate::ff::repr::LE>(&repr).unwrap()
        }

        fn to_big(&self) -> num_bigint::BigUint {
            num_bigint::BigUint::from_bytes_le(self.to_repr::<crate::ff::repr::LE>().as_ref())
        }
    }

    impl<T: crate::ff::Field> BigUintExt for T {}
}
