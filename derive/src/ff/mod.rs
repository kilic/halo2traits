use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Num, One};
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use std::collections::HashMap;
use syn::Token;

mod arith;
mod repr;

struct FieldConfig {
    field: syn::Ident,
    modulus: BigUint,
    mul_gen: BigUint,
    zeta: BigUint,
}

impl syn::parse::Parse for FieldConfig {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let field: syn::Ident = input.parse()?;
        input.parse::<syn::Token![,]>()?;

        let mut map: HashMap<String, String> = HashMap::new();

        fn get_big(map: &HashMap<String, String>, key: &str) -> syn::Result<BigUint> {
            let hex_repr = map
                .get(key)
                .ok_or(syn::Error::new(Span::call_site(), "missing modulus"))?;
            let big = BigUint::from_str_radix(hex_repr, 16)
                .map_err(|err| syn::Error::new(Span::call_site(), err.to_string()))?;
            Ok(big)
        }

        while !input.is_empty() {
            let key: syn::Ident = input.parse()?;
            input.parse::<Token![=]>()?;
            let value: syn::LitStr = input.parse()?;
            if map.insert(key.to_string(), value.value()).is_some() {
                return Err(syn::Error::new(
                    field.span(),
                    format!("duplicate key {}", key),
                ));
            }

            if !input.is_empty() {
                input.parse::<Token![,]>()?;
            }
        }

        let modulus = get_big(&map, "modulus")?;
        let mul_gen = get_big(&map, "mul_gen")?;
        let zeta = get_big(&map, "zeta")?;

        Ok(FieldConfig {
            field,
            modulus,
            mul_gen,
            zeta,
        })
    }
}

pub(crate) fn impl_field(input: TokenStream) -> TokenStream {
    use crate::utils::{big_to_token, mod_inv};
    let FieldConfig {
        field,
        modulus,
        mul_gen,
        zeta,
    } = syn::parse_macro_input!(input as FieldConfig);

    let num_bits = modulus.bits() as u32;
    let limb_size = 64;
    let num_limbs = ((num_bits - 1) / limb_size + 1) as usize;
    let modulus_limbs = crate::utils::big_to_limbs(&modulus, num_limbs);
    let modulus_limbs_ident = quote! {[#(#modulus_limbs,)*]};
    let to_token = |e: &BigUint| big_to_token(e, num_limbs);

    // binary modulus
    let t = BigUint::from(1u64) << (num_limbs * limb_size as usize);
    // r1 = mont(1)
    let r1: BigUint = &t % &modulus;
    let mont = |v: &BigUint| (v * &r1) % &modulus;
    // r2 = mont(r)
    let r2: BigUint = (&r1 * &r1) % &modulus;
    // r3 = mont(r^2)
    let r3: BigUint = (&r1 * &r1 * &r1) % &modulus;

    let r1 = to_token(&r1);
    let r2 = to_token(&r2);
    let r3 = to_token(&r3);

    // inv = -(r^{-1} mod 2^64) mod 2^64
    let mut inv64 = 1u64;
    for _ in 0..63 {
        inv64 = inv64.wrapping_mul(inv64);
        inv64 = inv64.wrapping_mul(modulus_limbs[0]);
    }
    inv64 = inv64.wrapping_neg();

    let mut by_inverter_constant: usize = 2;
    loop {
        let t = BigUint::from(1u64) << (62 * by_inverter_constant - 64);
        if t > modulus {
            break;
        }
        by_inverter_constant += 1;
    }

    let mut jacobi_constant: usize = 1;
    loop {
        let t = BigUint::from(1u64) << (64 * jacobi_constant - 31);
        if t > modulus {
            break;
        }
        jacobi_constant += 1;
    }

    let mut s: u32 = 0;
    let mut t = &modulus - BigUint::one();
    while t.is_even() {
        t >>= 1;
        s += 1;
    }

    let two_inv = mod_inv(&BigUint::from(2usize), &modulus);

    let sqrt_impl = {
        if &modulus % 16u64 == BigUint::from(1u64) {
            let tm1o2 = ((&t - 1usize) * &two_inv) % &modulus;
            let tm1o2 = big_to_token(&tm1o2, num_limbs);
            quote! {
                fn sqrt(&self) -> subtle::CtOption<Self> {
                    halo2traits::ff::arithmetic::sqrt::sqrt_tonelli_shanks(self, #tm1o2)
                }
            }
        } else if &modulus % 4u64 == BigUint::from(3u64) {
            let exp = (&modulus + 1usize) >> 2;
            let exp = big_to_token(&exp, num_limbs);
            quote! {
                fn sqrt(&self) -> subtle::CtOption<Self> {
                    use subtle::ConstantTimeEq;
                    let t = self.pow(#exp);
                    subtle::CtOption::new(t, t.square().ct_eq(self))
                }
            }
        } else {
            panic!("unsupported modulus")
        }
    };

    let root_of_unity = mul_gen.modpow(&t, &modulus);
    let root_of_unity_inv = mod_inv(&root_of_unity, &modulus);
    let delta = mul_gen.modpow(&(BigUint::one() << s), &modulus);

    let root_of_unity = to_token(&mont(&root_of_unity));
    let root_of_unity_inv = to_token(&mont(&root_of_unity_inv));
    let two_inv = to_token(&mont(&two_inv));
    let mul_gen = to_token(&mont(&mul_gen));
    let delta = to_token(&mont(&delta));
    let zeta = to_token(&mont(&zeta));

    let mut gen = quote! {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
        struct #field([u64; #num_limbs]);
    };

    gen.extend(repr::impl_serde(&field, num_limbs));
    gen.extend(crate::binops::impl_binops_additive(&field, &field, &field));
    gen.extend(crate::binops::impl_binops_additive_assigned(&field, &field));
    gen.extend(crate::binops::impl_binops_multiplicative(
        &field, &field, &field,
    ));
    gen.extend(crate::binops::impl_binops_multiplicative_assigned(
        &field, &field,
    ));

    let impl_arith = arith::impl_arith(&field, num_limbs, &modulus_limbs, inv64);
    gen.extend(quote! {
        impl #field {
            #impl_arith
        }
    });

    gen.extend(quote! {
        impl From<u64> for #field {
            fn from(val: u64) -> #field {
                let limbs = std::iter::once(val)
                    .chain(std::iter::repeat(0))
                    .take(#num_limbs)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                #field(limbs) * #field::R2
            }
        }


        impl core::fmt::Debug for #field {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                use halo2traits::ff::repr::{FieldRepr, LE};
                let tmp = self.to_repr::<LE>();
                write!(f, "0x")?;
                for &b in tmp.as_ref().iter().rev() {
                    write!(f, "{:02x}", b)?;
                }
                Ok(())
            }
        }

        impl subtle::ConstantTimeEq for #field {
            fn ct_eq(&self, other: &Self) -> subtle::Choice {
                subtle::Choice::from(
                    self.0
                        .iter()
                        .zip(other.0)
                        .all(|(a, b)| bool::from(a.ct_eq(&b))) as u8,
                )
            }
        }

        impl subtle::ConditionallySelectable for #field {
            fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
                let limbs = (0..#field::NUM_LIMBS)
                    .map(|i| u64::conditional_select(&a.0[i], &b.0[i], choice))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                #field(limbs)
            }
        }

        impl core::cmp::PartialOrd for #field {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl core::cmp::Ord for #field {
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                use halo2traits::ff::repr::FieldRepr;
                let left = self.to_repr::<halo2traits::ff::repr::LE>();
                let right = other.to_repr::<halo2traits::ff::repr::LE>();
                left.as_ref().iter()
                    .zip(right.as_ref().iter())
                    .rev()
                    .find_map(|(left_byte, right_byte)| match left_byte.cmp(right_byte) {
                        core::cmp::Ordering::Equal => None,
                        res => Some(res),
                    })
                    .unwrap_or(core::cmp::Ordering::Equal)
            }
        }


        impl #field {
            const NUM_LIMBS: usize = #num_limbs;
            const MODULUS: [u64; Self::NUM_LIMBS] = #modulus_limbs_ident;
            const R: Self = Self(#r1);
            const R2: Self = Self(#r2);
            const R3: Self = Self(#r3);

            /// Returns zero, the additive identity.
            #[inline]
            pub const fn zero() -> #field {
                #field([0; Self::NUM_LIMBS])
            }

            /// Returns one, the multiplicative identity.
            #[inline]
            pub const fn one() -> #field {
                Self::R
            }


            // Returns the Jacobi symbol, where the numerator and denominator
            // are the element and the characteristic of the field, respectively.
            // The Jacobi symbol is applicable to odd moduli
            // while the Legendre symbol is applicable to prime moduli.
            // They are equivalent for prime moduli.
            #[inline(always)]
            fn jacobi(&self) -> i64 {
                halo2traits::ff::arithmetic::jacobi::jacobi::<#jacobi_constant>(&self.0, &#modulus_limbs_ident)
            }

            // Returns the multiplicative inverse of the element. If it is zero, the method fails.
            #[inline(always)]
            fn invert(&self) -> subtle::CtOption<Self> {
                const BYINVERTOR: halo2traits::ff::arithmetic::inverse::BYInverter<#by_inverter_constant> =
                    halo2traits::ff::arithmetic::inverse::BYInverter::<#by_inverter_constant>::new(&#modulus_limbs_ident, &#r2);

                if let Some(inverse) = BYINVERTOR.invert::<{ Self::NUM_LIMBS }>(&self.0) {
                    subtle::CtOption::new(Self(inverse), subtle::Choice::from(1))
                } else {
                    subtle::CtOption::new(Self::zero(), subtle::Choice::from(0))
                }
            }
        }
    });

    let impl_ff_field = quote::quote! {


        impl<T: ::core::borrow::Borrow<#field>> ::core::iter::Sum<T> for #field {
            fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
                use halo2traits::ff::Field;
                iter.fold(Self::ZERO, |acc, item| acc + item.borrow())
            }
        }

        impl<T: ::core::borrow::Borrow<#field>> ::core::iter::Product<T> for #field {
            fn product<I: Iterator<Item = T>>(iter: I) -> Self {
                use halo2traits::ff::Field;
                iter.fold(Self::ONE, |acc, item| acc * item.borrow())
            }
        }

        impl halo2traits::ff::Field for #field {

            const ZERO : Self = Self::zero();
            const ONE : Self = Self::one();

            fn random(mut rng: impl rand_core::RngCore) -> Self {
                use halo2traits::ff::repr::FieldRepr;
                let mut wide = [0u8; Self::SIZE * 2];
                rng.fill_bytes(&mut wide);
                Self::from_uniform_bytes(&wide)
            }

            fn square(&self) -> Self {
                self.square()
            }

            fn invert(&self) -> subtle::CtOption<Self> {
                self.invert()
            }

            #sqrt_impl

            fn from_uniform_bytes(bytes: &[u8]) -> Self {
                use halo2traits::ff::repr::FieldRepr;

                assert!(bytes.len() <= Self::SIZE * 2, "Allow at most 2 elements");
                assert!(!bytes.is_empty());

                let mut wide = [0u8; Self::SIZE * 2];
                wide[..bytes.len()].copy_from_slice(bytes);
                let (a0, a1) = wide.split_at(Self::SIZE);

                let a0: [u64; Self::NUM_LIMBS] = (0..Self::NUM_LIMBS)
                    .map(|off| u64::from_le_bytes(a0[off * 8..(off + 1) * 8].try_into().unwrap()))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let a0 = #field(a0);

                let a1: [u64; Self::NUM_LIMBS] = (0..Self::NUM_LIMBS)
                    .map(|off| u64::from_le_bytes(a1[off * 8..(off + 1) * 8].try_into().unwrap()))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let a1 = #field(a1);

                a0 * Self::R2 + a1 * Self::R3
            }
        }
    };
    gen.extend(impl_ff_field);

    let impl_ff_prime_field = quote::quote! {

        impl halo2traits::ff::PrimeField for #field {
            const NUM_BITS: u32 = #num_bits;
            const TWO_INV :Self = Self(#two_inv);
            const MULTIPLICATIVE_GENERATOR: Self = Self(#mul_gen);
            const S: u32 = #s;
            const ROOT_OF_UNITY: Self = Self(#root_of_unity);
            const ROOT_OF_UNITY_INV: Self = Self(#root_of_unity_inv);
            const DELTA: Self = Self(#delta);
            const ZETA: Self = Self(#zeta);
        }
    };

    gen.extend(impl_ff_prime_field);

    let impl_ff_legendre = quote::quote! {
            impl halo2traits::ff::Legendre for #field {
                #[inline(always)]
                fn legendre(&self) -> i64 {
                    self.jacobi()
                }
            }
    };

    gen.extend(impl_ff_legendre);

    TokenStream::from(gen)
}
