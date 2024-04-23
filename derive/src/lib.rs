mod binops;
mod ff;
mod utils;

#[proc_macro]
pub fn impl_field(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    ff::impl_field(input)
}
