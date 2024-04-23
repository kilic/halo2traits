use proc_macro2::TokenStream;
use quote::format_ident as fmtid;
use quote::quote;

fn select(cond: bool, this: TokenStream, other: TokenStream) -> TokenStream {
    if cond {
        this
    } else {
        other
    }
}

pub(crate) fn impl_arith(
    field: &syn::Ident,
    num_limbs: usize,
    modulus_limbs: &[u64],
    inv: u64,
) -> TokenStream {
    let impl_add = impl_add(field, num_limbs, modulus_limbs);
    let impl_sub = impl_sub(field, num_limbs, modulus_limbs);
    let impl_neg = impl_neg(field, num_limbs, modulus_limbs);
    let impl_mont = impl_mont(field, num_limbs, modulus_limbs, inv);
    let impl_mul = impl_mul(field, num_limbs);
    let impl_square = impl_square(field, num_limbs);
    let wide_num_limbs = num_limbs * 2;
    quote::quote! {
        #[inline(always)]
        pub const fn add(&self, rhs: &Self) -> Self {
            #impl_add
        }

        #[inline(always)]
        pub const fn sub(&self, rhs: &Self) -> Self {
            #impl_sub
        }

        #[inline(always)]
        pub const fn neg(&self) -> Self {
            #impl_neg
        }

        pub const fn mul(&self, rhs: &Self) -> Self{
            #impl_mul
        }

        pub const fn square(&self) -> Self{
            #impl_square
        }

        #[inline(always)]
        pub(crate) const fn montgomery_reduce(r: &[u64; #wide_num_limbs]) -> Self {
            #impl_mont
        }
    }
}

fn impl_mul(field: &syn::Ident, num_limbs: usize) -> TokenStream {
    let mut gen = quote! { use halo2traits::ff::arithmetic::u64::{adc, sbb, mac}; };
    for i in 0..num_limbs {
        for j in 0..num_limbs {
            let r_out = fmtid!("r_{}", i + j);
            let r_next = fmtid!("r_{}", i + j + 1);
            let r_in = select(i == 0, quote! {0}, quote! {#r_out});
            let carry_in = select(j == 0, quote! {0}, quote! {carry});
            let carry_out = select(j == num_limbs - 1, quote! {#r_next}, quote! {carry});
            gen.extend(
                quote! { let (#r_out, #carry_out) = mac(#r_in, self.0[#i], rhs.0[#j], #carry_in); },
            );
        }
    }

    let r: Vec<_> = (0..num_limbs * 2).map(|i| fmtid!("r_{}", i)).collect();
    quote! {
        #gen
        #field::montgomery_reduce(&[#(#r),*])
    }
}

fn impl_square(field: &syn::Ident, num_limbs: usize) -> TokenStream {
    let mut gen = quote! { use halo2traits::ff::arithmetic::u64::{adc, sbb, mac}; };
    for i in 0..num_limbs - 1 {
        let start_index = i * 2 + 1;
        for j in 0..num_limbs - i - 1 {
            let r_out = fmtid!("r_{}", start_index + j);
            let r_in = select(i == 0, quote! {0}, quote! {#r_out});
            let r_next = fmtid!("r_{}", start_index + j + 1);
            let carry_in = select(j == 0, quote! {0}, quote! {carry});
            let carry_out = select(j == num_limbs - i - 2, quote! {#r_next}, quote! {carry});
            let j = i + j + 1;
            gen.extend(quote! { let (#r_out, #carry_out) = mac(#r_in, self.0[#i], self.0[#j], #carry_in); });
        }
    }

    for i in (1..num_limbs * 2).rev() {
        let (r_cur, r_next) = (fmtid!("r_{}", i), fmtid!("r_{}", i - 1));
        if i == num_limbs * 2 - 1 {
            gen.extend(quote! { let #r_cur = #r_next >> 63; });
        } else if i == 1 {
            gen.extend(quote! { let #r_cur = (#r_cur << 1); });
        } else {
            gen.extend(quote! { let #r_cur = (#r_cur << 1) | (#r_next >> 63); });
        }
    }

    for i in 0..num_limbs {
        let index = i * 2;
        let r_cur = fmtid!("r_{}", index);
        let r_next = fmtid!("r_{}", index + 1);
        let r_cur_in = select(i == 0, quote! {0}, quote! {#r_cur});
        let carry_in = select(i == 0, quote! {0}, quote! {carry});
        let carry_out = select(i == num_limbs - 1, quote! {_}, quote! {carry});
        gen.extend(quote! {
            let (#r_cur, carry) = mac(#r_cur_in, self.0[#i], self.0[#i], #carry_in);
            let (#r_next, #carry_out) = adc(0, #r_next, carry);
        });
    }

    let r: Vec<_> = (0..num_limbs * 2).map(|i| fmtid!("r_{}", i)).collect();
    quote! {
        #gen
        #field::montgomery_reduce(&[#(#r),*])
    }
}

fn impl_add(field: &syn::Ident, num_limbs: usize, modulus_limbs: &[u64]) -> TokenStream {
    let mut gen = quote! { use halo2traits::ff::arithmetic::u64::{adc, sbb}; };

    (0..num_limbs).for_each(|i| {
        let carry = select(i == 0, quote! {0}, quote! {carry});
        let d_i = fmtid!("d_{}", i);
        gen.extend(quote! { let ( #d_i, carry) = adc(self.0[#i], rhs.0[#i], #carry); });
    });

    (0..num_limbs).for_each(|i| {
        let borrow = select(i == 0, quote! {0}, quote! {borrow});
        let d_i = fmtid!("d_{}", i);
        let modulus_limb = modulus_limbs[i];
        gen.extend(quote! { let (#d_i, borrow) = sbb(#d_i, #modulus_limb, #borrow); });
    });
    gen.extend(quote! {let (_, borrow) = sbb(carry, 0, borrow);});

    (0..num_limbs).for_each(|i| {
        let carry_in = select(i == 0, quote! {0}, quote! {carry});
        let carry_out = select(i == num_limbs - 1, quote! {_}, quote! {carry});
        let d_i = fmtid!("d_{}", i);
        let modulus_limb = modulus_limbs[i];
        gen.extend(
            quote! { let (#d_i, #carry_out) = adc(#d_i, #modulus_limb & borrow, #carry_in); },
        );
    });

    let ret: Vec<_> = (0..num_limbs).map(|i| fmtid!("d_{}", i)).collect();

    quote! {
        #gen
        #field([#(#ret),*])
    }
}

fn impl_sub(field: &syn::Ident, num_limbs: usize, modulus_limbs: &[u64]) -> TokenStream {
    let mut gen = quote! { use halo2traits::ff::arithmetic::u64::{adc, sbb}; };

    (0..num_limbs).for_each(|i| {
        let borrow = select(i == 0, quote! {0}, quote! {borrow});
        let d_i = fmtid!("d_{}", i);
        gen.extend(quote! { let (#d_i, borrow) = sbb(self.0[#i], rhs.0[#i], #borrow); });
    });

    (0..num_limbs).for_each(|i| {
        let carry_in = select(i == 0, quote! {0}, quote! {carry});
        let carry_out = select(i == num_limbs - 1, quote! {_}, quote! {carry});
        let d_i = fmtid!("d_{}", i);
        let modulus_limb = modulus_limbs[i];
        gen.extend(
            quote! { let (#d_i, #carry_out) = adc(#d_i, #modulus_limb & borrow, #carry_in); },
        );
    });

    let ret: Vec<_> = (0..num_limbs).map(|i| fmtid!("d_{}", i)).collect();

    quote! {
        #gen
        #field([#(#ret),*])
    }
}

fn impl_neg(field: &syn::Ident, num_limbs: usize, modulus_limbs: &[u64]) -> TokenStream {
    let mut gen = quote! { use halo2traits::ff::arithmetic::u64::{adc, sbb}; };

    (0..num_limbs).for_each(|i| {
        let borrow_in = select(i == 0, quote! {0}, quote! {borrow});
        let borrow_out = select(i == num_limbs - 1, quote! {_}, quote! {borrow});
        let d_i = fmtid!("d_{}", i);
        let modulus_limb = modulus_limbs[i];
        gen.extend(quote! { let (#d_i, #borrow_out) = sbb(#modulus_limb, self.0[#i], #borrow_in); })
    });

    let mask_limbs: Vec<_> = (0..num_limbs)
        .map(|i| quote::quote! { self.0[#i] })
        .collect();
    gen.extend(quote! { let mask = (((#(#mask_limbs)|*) == 0) as u64).wrapping_sub(1); });

    let ret: Vec<_> = (0..num_limbs)
        .map(|i| {
            let d_i = fmtid!("d_{}", i);
            quote! { #d_i & mask }
        })
        .collect();

    quote! {
        #gen
        #field([#(#ret),*])
    }
}

fn impl_mont(field: &syn::Ident, num_limbs: usize, modulus_limbs: &[u64], inv: u64) -> TokenStream {
    let mut gen = quote! { use halo2traits::ff::arithmetic::u64::{adc, sbb, mac}; };

    for i in 0..num_limbs {
        if i == 0 {
            gen.extend(quote! { let k = r[0].wrapping_mul(#inv); });

            for (j, m) in modulus_limbs.iter().enumerate() {
                let r_out = fmtid!("r_{}", j);
                let r_out = select(j == 0, quote! {_}, quote! {#r_out});
                let carry_in = select(j == 0, quote! {0}, quote! {carry});
                gen.extend(quote! { let (#r_out, carry) = mac(r[#j], k, #m, #carry_in); });
            }
            let r_out = fmtid!("r_{}", num_limbs);
            gen.extend(quote! { let (#r_out, carry2) = adc(r[#num_limbs], 0, carry); });
        } else {
            let r_i = fmtid!("r_{}", i);
            gen.extend(quote! { let k = #r_i.wrapping_mul(#inv); });

            for (j, m) in modulus_limbs.iter().enumerate() {
                let r_in = fmtid!("r_{}", j + i);
                let r_out = select(j == 0, quote! {_}, quote! {#r_in});
                let carry_in = select(j == 0, quote! {0}, quote! {carry});
                gen.extend(quote! { let (#r_out, carry) = mac(#r_in, k, #m, #carry_in); });
            }
            let idx = num_limbs + i;
            let r_out = fmtid!("r_{}", idx);
            let carry_out = select(i == num_limbs - 1, quote! {_}, quote! {carry2});
            gen.extend(quote! { let (#r_out, #carry_out) = adc(r[#idx], carry2, carry); });
        }
    }

    let r: Vec<_> = (num_limbs..num_limbs * 2)
        .map(|i| fmtid!("r_{}", i))
        .collect();
    let r = quote! { #field([#(#r),*]) };
    let modulus = quote! {#field([#(#modulus_limbs,)*])};

    quote! {
        #gen
        #r.sub(&#modulus)
    }
}
