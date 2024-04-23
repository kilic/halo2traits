use proc_macro2::TokenStream;

pub(crate) fn impl_serde(field: &syn::Ident, num_limbs: usize) -> TokenStream {
    let field_repr = quote::format_ident!("Repr{}", field);

    let size = num_limbs * 8;

    let impl_struct = quote::quote! {
        #[derive(Clone, Copy, Debug)]
        pub struct #field_repr([u8; #size]);

        impl Default for #field_repr {
            fn default() -> Self {
                Self([0u8; #size])
            }
        }

        impl From<[u8; #size]> for #field_repr {
            fn from(repr: [u8; #size]) -> Self {
                Self(repr)
            }
        }

        impl From<#field_repr> for [u8; #size] {
            fn from(repr: #field_repr) -> Self {
                repr.0
            }
        }

        impl AsMut<[u8]> for #field_repr {
            fn as_mut(&mut self) -> &mut [u8] {
                &mut self.0
            }
        }

        impl AsRef<[u8]> for #field_repr {
            fn as_ref(&self) -> &[u8] {
                &self.0
            }
        }

        impl core::ops::Index<usize> for #field_repr {
            type Output = u8;

            fn index(&self, index: usize) -> &Self::Output {
                &self.0[index]
            }
        }

        impl core::ops::Index<core::ops::Range<usize>> for #field_repr {
            type Output = [u8];

            fn index(&self, index: core::ops::Range<usize>) -> &Self::Output {
                &self.0[index]
            }
        }


    };

    let limbs: Vec<_> = (0..num_limbs)
        .map(|i| quote::quote! { self.0[#i] })
        .collect();
    let zeros: Vec<_> = std::iter::repeat(quote::quote! { 0 })
        .take(num_limbs)
        .collect();
    let padded = quote::quote! { &[#(#limbs),*, #(#zeros),*] };

    let impl_repr = quote::quote! {

        impl #field {
            #[inline(always)]
            fn is_less_than_modulus(e: &#field) -> bool {
                let borrow = e.0.iter().enumerate().fold(0, |borrow, (i, limb)| {
                    halo2traits::ff::arithmetic::u64::sbb(*limb, Self::MODULUS[i], borrow).1
                });
                (borrow as u8) & 1 == 1
            }
        }

        impl halo2traits::ff::repr::FieldRepr for #field {
            const SIZE: usize = #field::NUM_LIMBS * 8;

            type Repr = #field_repr;

            fn from_repr<E: halo2traits::ff::repr::Endian>(repr: &Self::Repr) -> subtle::CtOption<Self> {
                let mut el = #field::default();
                E::from_bytes(repr.as_ref(), &mut el.0);
                subtle::CtOption::new(el * Self::R2, subtle::Choice::from(Self::is_less_than_modulus(&el) as u8))
            }

            fn to_repr<E: halo2traits::ff::repr::Endian>(&self) -> Self::Repr {
                use halo2traits::ff::repr::FieldRepr;
                let el = #field::montgomery_reduce(#padded);
                let mut res = [0; Self::SIZE];
                E::to_bytes(&mut res, &el.0);
                res.into()
            }
        }
    };

    let impl_repr_raw = quote::quote! {
        impl halo2traits::ff::repr::FieldReprRaw for #field {

            fn from_raw_repr_unchecked<E: halo2traits::ff::repr::Endian>(repr: &Self::Repr) -> subtle::CtOption<Self> {
                let mut el = #field::default();
                E::from_bytes(repr.as_ref(), &mut el.0);
                subtle::CtOption::new(el, subtle::Choice::from(1 as u8))
            }

            fn from_raw_repr<E: halo2traits::ff::repr::Endian>(repr: &Self::Repr) -> subtle::CtOption<Self> {

                let mut el = #field::default();
                E::from_bytes(repr.as_ref(), &mut el.0);
                subtle::CtOption::new(el, subtle::Choice::from(Self::is_less_than_modulus(&el) as u8))
            }

            fn to_raw_repr<E: halo2traits::ff::repr::Endian>(&self) -> Self::Repr {
                use halo2traits::ff::repr::FieldRepr;
                let mut res = [0; Self::SIZE];
                E::to_bytes(&mut res, &self.0);
                res.into()
            }
        }
    };

    quote::quote! {
        #impl_struct
        #impl_repr
        #impl_repr_raw
    }
}
