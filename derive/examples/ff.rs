use halo2derive::impl_field;
use halo2traits::ff::utils::biguint::BigUintExt;
use halo2traits::ff::{Field, Legendre, PrimeField};
use rand_core::OsRng;

impl_field!(
    Fr,
    modulus = "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
    mul_gen = "7",
    roots_of_unity = "03ddb9f5166d18b798865ea93dd31f743215cf6dd39329c8d34f1ed960c37c9c",
    zeta = "30644e72e131a029048b6e193fd84104cc37a73fec2bc5e9b8ca0b2d36636f23"
);

impl_field!(
    Fq,
    modulus = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab",
    mul_gen = "2",
    roots_of_unity = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa",
    zeta = "1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac"
);

fn main() {
    test::<Fq>();
    test::<Fr>();
}

fn test<F: PrimeField + Legendre>() {
    let n = 10000;
    let rng = OsRng;
    multiplication_tests::<F, _>(rng, n);
    addition_tests::<F, _>(rng, n);
    subtraction_tests::<F, _>(rng, n);
    negation_tests::<F, _>(rng, n);
    doubling_tests::<F, _>(rng, n);
    squaring_tests::<F, _>(rng, n);
    inversion_tests::<F, _>(rng, n);
    expansion_tests::<F, _>(rng, n);
    zero_tests::<F, _>(rng);
    one_tests::<F, _>(rng);
    sqrt_tests::<F, _>(rng);
    repr_tests::<F, _>(rng, n);
    constants_tests::<F>();
    from_uniform_bytes_tests::<F, _>(rng);
}

fn multiplication_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    for _ in 0..n {
        let a = F::random(&mut rng);
        let b = F::random(&mut rng);
        let c = F::random(&mut rng);

        let mut t0 = a; // (a * b) * c
        t0.mul_assign(&b);
        t0.mul_assign(&c);
        let mut t1 = a; // (a * c) * b
        t1.mul_assign(&c);
        t1.mul_assign(&b);
        let mut t2 = b; // (b * c) * a
        t2.mul_assign(&c);
        t2.mul_assign(&a);
        assert_eq!(t0, t1);
        assert_eq!(t0, t2);

        {
            let a = a.to_big();
            let b = b.to_big();
            let c = c.to_big();
            let t3 = (&a * &b * &c) % F::modulus();
            let t3 = F::from_big(&t3);
            assert_eq!(t0, t3);
        }
    }
}

fn addition_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    for _ in 0..n {
        let a = F::random(&mut rng);
        let b = F::random(&mut rng);
        let c = F::random(&mut rng);
        let mut t0 = a; // (a + b) + c
        t0.add_assign(&b);
        t0.add_assign(&c);
        let mut t1 = a; // (a + c) + b
        t1.add_assign(&c);
        t1.add_assign(&b);
        let mut t2 = b; // (b + c) + a
        t2.add_assign(&c);
        t2.add_assign(&a);
        assert_eq!(t0, t1);
        assert_eq!(t0, t2);

        {
            let a = a.to_big();
            let b = b.to_big();
            let c = c.to_big();
            let t3 = (&a + &b + &c) % F::modulus();
            let t3 = F::from_big(&t3);
            assert_eq!(t0, t3);
        }
    }
}

fn subtraction_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    for _ in 0..n {
        let a = F::random(&mut rng);
        let b = F::random(&mut rng);
        let mut t0 = a; // (a - b)
        t0.sub_assign(&b);

        {
            let a = a.to_big();
            let b = b.to_big();
            let t1 = (&a + F::modulus() - &b) % F::modulus();
            let t1 = F::from_big(&t1);
            assert_eq!(t0, t1);
        }

        let mut t1 = b; // (b - a)
        t1.sub_assign(&a);
        let mut t2 = t0; // (a - b) + (b - a) = 0
        t2.add_assign(&t1);
        assert_eq!(t2.is_zero().unwrap_u8(), 1);
    }
}

fn negation_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    for _ in 0..n {
        let a = F::random(&mut rng);
        let mut b = a;
        b = b.neg();
        b.add_assign(&a);
        assert_eq!(b.is_zero().unwrap_u8(), 1);
    }
}

fn doubling_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    for _ in 0..n {
        let mut a = F::random(&mut rng);
        let mut b = a;
        a.add_assign(&b);
        b = b.double();
        assert_eq!(a, b);
    }
}

fn squaring_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    for _ in 0..n {
        let mut a = F::random(&mut rng);
        let mut b = a;
        a.mul_assign(&b);
        b = b.square();
        assert_eq!(a, b);
    }
}

fn inversion_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    assert!(bool::from(F::ZERO.invert().is_none()));
    for _ in 0..n {
        let mut a = F::random(&mut rng);
        let b = a.invert().unwrap(); // probabilistically nonzero
        a.mul_assign(&b);
        assert_eq!(a, F::ONE);
    }
}

fn expansion_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    for _ in 0..n {
        // (a + b)(c + d) == (a*c + b*c + a*d + b*d)

        let a = F::random(&mut rng);
        let b = F::random(&mut rng);
        let c = F::random(&mut rng);
        let d = F::random(&mut rng);
        let mut t0 = a;
        t0.add_assign(&b);
        let mut t1 = c;
        t1.add_assign(&d);
        t0.mul_assign(&t1);
        let mut t2 = a;
        t2.mul_assign(&c);
        let mut t3 = b;
        t3.mul_assign(&c);
        let mut t4 = a;
        t4.mul_assign(&d);
        let mut t5 = b;
        t5.mul_assign(&d);
        t2.add_assign(&t3);
        t2.add_assign(&t4);
        t2.add_assign(&t5);

        assert_eq!(t0, t2);
    }
}

fn zero_tests<F: Field, R: rand_core::RngCore>(mut rng: R) {
    assert_eq!(F::ZERO.is_zero().unwrap_u8(), 1);
    {
        let mut z = F::ZERO;
        z = z.neg();
        assert_eq!(z.is_zero().unwrap_u8(), 1);
    }
    assert!(bool::from(F::ZERO.invert().is_none()));
    {
        let mut a = F::random(&mut rng);
        a.mul_assign(&F::ZERO);
        assert_eq!(a.is_zero().unwrap_u8(), 1);
    }
    {
        let mut a = F::random(&mut rng);
        let copy = a;
        a.add_assign(&F::ZERO);
        assert_eq!(a, copy);
    }
}

fn one_tests<F: Field, R: rand_core::RngCore>(mut rng: R) {
    assert!(bool::from(F::ONE.invert().is_some()));
    {
        let mut a = F::random(&mut rng);
        let copy = a;
        a.mul_assign(&F::ONE);
        assert_eq!(a, copy);
    }
    {
        let mut a = F::random(&mut rng);
        let copy = a;
        a.add_assign(&F::ONE);
        assert_eq!(a, copy + F::ONE);
    }
}

fn sqrt_tests<F: PrimeField + Legendre, R: rand_core::RngCore>(mut _rng: R) {
    let v = (F::TWO_INV).square().sqrt().unwrap();
    assert!(v == F::TWO_INV || (-v) == F::TWO_INV);

    for _ in 0..1000 {
        let a = F::random(OsRng);
        if a.legendre() == -1 {
            assert!(bool::from(a.sqrt().is_none()));
        }
    }

    for _ in 0..1000 {
        let a = F::random(OsRng);
        let mut b = a;
        b = b.square();
        assert_eq!(b.legendre(), 1);

        let b = b.sqrt().unwrap();
        let mut negb = b;
        negb = negb.neg();

        assert!(a == b || a == negb);
    }

    let mut c = F::ONE;
    for _ in 0..1000 {
        let mut b = c;
        b = b.square();
        assert_eq!(b.legendre(), 1);

        b = b.sqrt().unwrap();

        if b != c {
            b = b.neg();
        }

        assert_eq!(b, c);

        c += &F::ONE;
    }
}

fn repr_tests<F: Field, R: rand_core::RngCore>(mut rng: R, n: usize) {
    use halo2traits::ff::repr::{BE, LE};
    use num_bigint::BigUint;
    use num_bigint::RandBigInt;
    use num_traits::Zero;

    for _ in 0..n {
        let a = F::random(&mut rng);

        {
            let a_big = a.to_big();
            let b = F::from_big(&a_big);
            assert_eq!(a, b);
        }

        let bytes = a.to_repr::<LE>();
        let b = F::from_repr::<LE>(&bytes).unwrap();
        assert_eq!(a, b);
        let bytes = a.to_raw_repr::<LE>();
        let b = F::from_raw_repr::<LE>(&bytes).unwrap();
        assert_eq!(a, b);

        let bytes = a.to_repr::<BE>();
        let b = F::from_repr::<BE>(&bytes).unwrap();
        assert_eq!(a, b);
        let bytes = a.to_raw_repr::<BE>();
        let b = F::from_raw_repr::<BE>(&bytes).unwrap();
        assert_eq!(a, b);

        {
            let a_big_0 = OsRng.gen_biguint_range(&BigUint::zero(), &F::modulus());
            let a = F::from_big(&a_big_0);
            let a_big_1 = a.to_big();
            assert_eq!(a_big_0, a_big_1);

            let decimal_str = a_big_0.to_str_radix(10);
            let b = F::from_decimal_str(&decimal_str).unwrap();
            assert_eq!(a, b);
            let hex_str = a_big_0.to_str_radix(16);
            let b = F::from_hex_str(&hex_str).unwrap();
            assert_eq!(a, b);
        }
    }
}

fn constants_tests<F: PrimeField>() {
    assert_eq!(F::ROOT_OF_UNITY_INV, F::ROOT_OF_UNITY.invert().unwrap());
    assert_eq!(F::from(2) * F::TWO_INV, F::ONE);
    if F::S != 0 {
        assert_eq!(F::ROOT_OF_UNITY.pow([1 << F::S]), F::ONE);
        assert_eq!(F::DELTA, F::MULTIPLICATIVE_GENERATOR.pow([1u64 << F::S]));
    }
    assert_ne!(F::ZETA * F::ZETA, F::ONE);
    assert_eq!(F::ZETA * F::ZETA * F::ZETA, F::ONE);
}

fn from_uniform_bytes_tests<F: PrimeField, R: rand_core::RngCore>(mut rng: R) {
    use num_bigint::BigUint;

    for size in 1..=F::SIZE * 2 {
        for _ in 0..1 {
            let mut uniform_bytes = vec![0u8; size];
            rng.fill_bytes(&mut uniform_bytes[..]);
            let e0 = BigUint::from_bytes_le(&uniform_bytes) % F::modulus();

            let bytes = e0.to_bytes_le();

            let mut e0 = <F as halo2traits::ff::repr::FieldRepr>::Repr::default();
            e0.as_mut()[..bytes.len()].copy_from_slice(&bytes);
            let e0 = F::from_repr::<halo2traits::ff::repr::LE>(&e0).unwrap();

            let e1 = F::from_uniform_bytes(&uniform_bytes);
            assert_eq!(e0, e1);
        }
    }
}
