use proc_macro2::TokenStream;

pub(crate) fn impl_binops_additive(
    lhs: &syn::Ident,
    rhs: &syn::Ident,
    out: &syn::Ident,
) -> TokenStream {
    quote::quote! {
        impl core::ops::Add<#rhs> for #lhs {
            type Output = #out;

            #[inline]
            fn add(self, rhs: #rhs) -> #out {
                &self + &rhs
            }
        }

        impl<'a> core::ops::Add<#rhs> for &'a #lhs {
            type Output = #out;

            #[inline]
            fn add(self, rhs: #rhs) -> #out {
                self + &rhs
            }
        }

        impl<'b> core::ops::Add<&'b #rhs> for #lhs {
            type Output = #out;

            #[inline]
            fn add(self, rhs: &'b #rhs) -> #out {
                &self + rhs
            }
        }

        impl<'a, 'b> core::ops::Add<&'b #rhs> for &'a #lhs {
            type Output = #out;

            #[inline]
            fn add(self, rhs: &'b #rhs) -> #lhs {
                self.add(rhs)
            }
        }

        impl core::ops::Sub<#rhs> for #lhs {
            type Output = #out;

            #[inline]
            fn sub(self, rhs: #rhs) -> #out {
                &self - &rhs
            }
        }

        impl<'a> core::ops::Sub<#rhs> for &'a #lhs {
            type Output = #out;

            #[inline]
            fn sub(self, rhs: #rhs) -> #out {
                self - &rhs
            }
        }

        impl<'b> core::ops::Sub<&'b #rhs> for #lhs {
            type Output = #out;

            #[inline]
            fn sub(self, rhs: &'b #rhs) -> #out {
                &self - rhs
            }
        }

        impl<'a, 'b> core::ops::Sub<&'b #rhs> for &'a #lhs {
            type Output = #out;

            #[inline]
            fn sub(self, rhs: &'b #rhs) -> #out {
                self.sub(rhs)
            }
        }

        impl<'a> core::ops::Neg for &'a #lhs {
            type Output = #out;

            #[inline]
            fn neg(self) -> #lhs {
                self.neg()
            }
        }

        impl core::ops::Neg for #lhs {
            type Output = #out;

            #[inline]
            fn neg(self) -> #out {
                -&self
            }
        }
    }
}

pub(crate) fn impl_binops_additive_assigned(lhs: &syn::Ident, rhs: &syn::Ident) -> TokenStream {
    quote::quote! {
        impl core::ops::SubAssign<#rhs> for #lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: #rhs) {
                *self = &*self - &rhs;
            }
        }

        impl core::ops::AddAssign<#rhs> for #lhs {
            #[inline]
            fn add_assign(&mut self, rhs: #rhs) {
                *self = &*self + &rhs;
            }
        }

        impl<'b> core::ops::SubAssign<&'b #rhs> for #lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: &'b #rhs) {
                *self = &*self - rhs;
            }
        }

        impl<'b> core::ops::AddAssign<&'b #rhs> for #lhs {
            #[inline]
            fn add_assign(&mut self, rhs: &'b #rhs) {
                *self = &*self + rhs;
            }
        }
    }
}

pub(crate) fn impl_binops_multiplicative(
    lhs: &syn::Ident,
    rhs: &syn::Ident,
    out: &syn::Ident,
) -> TokenStream {
    quote::quote! {

        impl core::ops::Mul<#rhs> for #lhs {
            type Output = #out;

            #[inline]
            fn mul(self, rhs: #rhs) -> #out {
                &self * &rhs
            }
        }

        impl<'a> core::ops::Mul<#rhs> for &'a #lhs {
            type Output = #out;

            #[inline]
            fn mul(self, rhs: #rhs) -> #out {
                self * &rhs
            }
        }

        impl<'b> core::ops::Mul<&'b #rhs> for #lhs {
            type Output = #out;

            #[inline]
            fn mul(self, rhs: &'b #rhs) -> #out {
                &self * rhs
            }
        }

        impl<'a, 'b> core::ops::Mul<&'b #rhs> for &'a #lhs {
            type Output = #out;

            #[inline]
            fn mul(self, rhs: &'b #rhs) -> #out {
                self.mul(rhs)
            }
        }
    }
}

pub(crate) fn impl_binops_multiplicative_assigned(
    lhs: &syn::Ident,
    rhs: &syn::Ident,
) -> TokenStream {
    quote::quote! {
        impl core::ops::MulAssign<#rhs> for #lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: #rhs) {
                *self = &*self * &rhs;
            }
        }

        impl<'b> core::ops::MulAssign<&'b #rhs> for #lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: &'b #rhs) {
                *self = &*self * rhs;
            }
        }
    }
}
