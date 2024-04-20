

This is rework of [`zkcrypto`](https://github.com/zkcrypto/) traits that are used in [`pse/halo2`](https://github.com/privacy-scaling-explorations/halo2) and [`pse/halo2curves`](https://github.com/privacy-scaling-explorations/halo2curves) in order to reduce trait complexity with some new added features:

* Raw and unchecked serilization supported at trait level
* Optional endianness support
* `BigUint` conversion support
* Unrolled rust arithmetic derivation
* Simplified derivation of field traits. For example implementing arithmetic and deriving `::Field` and `::Primefield` for base field of BLS12-381 is just straightforward as below:

```
impl_field!(
    Fq,
    modulus = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab",
    mul_gen = "2",
    roots_of_unity = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa",
    zeta = "1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac"
);
```

Curve traits and derivation is about to be added. These traits should cover `::CurveExt` ine `pasta-curves` and `::Curve` and `::CurveAffine` in `zkcrypto` side at once.