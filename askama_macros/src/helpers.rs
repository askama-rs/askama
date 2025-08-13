use proc_macro2::Span;
use syn::{Ident, Lifetime, Type};

/// Recursively check if a type contains one of the given Idents
pub(crate) fn type_contains_ident(ty: &Type, ident: &Ident) -> Option<Span> {
    match ty {
        Type::Path(type_path) => {
            for segment in &type_path.path.segments {
                // Check if the segment ident matches
                if &segment.ident == ident {
                    return Some(segment.ident.span());
                }

                // Check generic arguments recursively
                if let syn::PathArguments::AngleBracketed(ref args) = segment.arguments {
                    for arg in &args.args {
                        match arg {
                            syn::GenericArgument::Type(inner_ty) => {
                                if let Some(span) = type_contains_ident(inner_ty, ident) {
                                    return Some(span);
                                }
                            }
                            syn::GenericArgument::AssocType(assoc) => {
                                if let Some(span) = type_contains_ident(&assoc.ty, ident) {
                                    return Some(span);
                                }
                            }
                            _ => {} // Not types -> skip
                        }
                    }
                }
            }
            None
        }
        Type::Reference(type_ref) => type_contains_ident(&type_ref.elem, ident),
        Type::Slice(type_slice) => type_contains_ident(&type_slice.elem, ident),
        Type::Array(type_array) => type_contains_ident(&type_array.elem, ident),
        Type::Tuple(type_tuple) => type_tuple
            .elems
            .iter()
            .filter_map(|elem_ty| type_contains_ident(elem_ty, ident))
            .next(),
        Type::Paren(type_paren) => type_contains_ident(&type_paren.elem, ident),
        Type::Group(type_group) => type_contains_ident(&type_group.elem, ident),
        _ => None, // covers everything else
    }
}

pub(crate) fn patch_ref_with_lifetime(ty: &Type, lifetime: &Ident) -> Type {
    match ty {
        Type::Reference(type_ref) => {
            let mut new_type_ref = type_ref.clone();

            // Inject the lifetime if it's missing
            if new_type_ref.lifetime.is_none() {
                new_type_ref.lifetime = Some(Lifetime {
                    apostrophe: Span::call_site(),
                    ident: lifetime.clone(),
                });
            }

            Type::Reference(new_type_ref)
        }
        _ => ty.clone(), // Only patch reference types; others remain unchanged
    }
}
