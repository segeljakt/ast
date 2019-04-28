//! Machinery in charge of deriving `FromPest` for a type.
//!
//! Documentation in this module and submodules describes the requirement placed on _child_
//! functions. This is important as manipulation is done over untyped `TokenStream`.

use {
    itertools::Itertools,
    proc_macro2::TokenStream,
    std::{iter, path::PathBuf as FilePath},
    syn::{
        parse::Error, parse::Result, spanned::Spanned, Data, DataEnum, DataStruct, DeriveInput,
        Field, Fields, Ident, Path, Variant,
    },
};

use attributes::{DeriveAttribute, FieldAttribute, OperatorAttribute};

mod field;

/// Creates implementation of `FromPest` for given derive input.
///
/// For child functions, sets up an environment with:
///
/// ```text
/// type Self::Rule;
/// type Self::FatalError = Void;
/// let pest: &mut Pairs;
/// ```
///
/// Child function is required to produce a number of statements that implement the semantics of
/// `FromPest::from_pest`; that is: `Ok(Self)` => success, `pest` updated past the node;
/// `Err(NoMatch)` => failure, `pest` is unchanged; `Err(Malformed)` impossible, panic instead.
/// `?` and `return` may be used for early exit of failed matches.
pub(crate) fn derive(
    DeriveInput {
        attrs,
        ident: name,
        generics,
        data,
        ..
    }: DeriveInput,
) -> Result<TokenStream> {
    let attrs = DeriveAttribute::from_attributes(attrs)?;

    let grammar = {
        let mut grammar_attrs = attrs.iter().filter_map(|attr| match attr {
            DeriveAttribute::Grammar(attr) => Some(attr),
            _ => None,
        });
        match (grammar_attrs.next(), grammar_attrs.next()) {
            (Some(_), Some(attr)) => Err(Error::new(
                attr.span(),
                "duplicate #[pest_ast(grammar)] not allowed",
            ))?,
            (None, None) => None,
            (Some(attr), None) => Some(FilePath::from(attr.lit.value())),
            _ => unreachable!(),
        }
    };

    let (rule_enum, rule_variant) = {
        let mut rule_attrs = attrs.iter().filter_map(|attr| match attr {
            DeriveAttribute::Rule(attr) => Some(attr),
            _ => None,
        });
        match (rule_attrs.next(), rule_attrs.next()) {
            (Some(_), Some(attr)) => Err(Error::new(
                attr.span(),
                "duplicate #[pest_ast(rule)] not allowed",
            ))?,
            (None, None) => (parse_quote!(Rule), parse_quote!(#name)),
            (Some(attr), None) => (attr.path.clone(), attr.variant.clone()),
            _ => unreachable!(),
        }
    };

    let (from_pest_lifetime, did_synthesize_lifetime) = generics
        .lifetimes()
        .next()
        .map(|def| (def.lifetime.clone(), false))
        .unwrap_or_else(|| (parse_quote!('unique_lifetime_name), true));

    let mut generics_ = generics.clone();
    let (_, ty_generics, where_clause) = generics.split_for_impl();
    if did_synthesize_lifetime {
        let lt = from_pest_lifetime.clone();
        generics_.params.push(parse_quote!(#lt));
    }
    let (impl_generics, _, _) = generics_.split_for_impl();

    let from_pest_template = |body: TokenStream| {
        quote! {
            impl #impl_generics ::from_pest::FromPest<#from_pest_lifetime> for #name #ty_generics #where_clause {
                type Rule = #rule_enum;
                type FatalError = ::from_pest::Void;

                fn from_pest(
                    pest: &mut ::from_pest::pest::iterators::Pairs<#from_pest_lifetime, #rule_enum>
                ) -> ::std::result::Result<Self, ::from_pest::ConversionError<::from_pest::Void>> {
                    #body
                }
            }
        }
    };
    let pratt_template = |primary_body: TokenStream,
                          infix_body: TokenStream,
                          prefix_body: TokenStream,
                          postfix_body: TokenStream| {
        quote! {
            impl #impl_generics ::from_pest::pratt_parser::PrattParser<#from_pest_lifetime, #rule_enum> for #name #ty_generics #where_clause {
                fn primary(primary: ::pest::iterators::Pair<#from_pest_lifetime, #rule_enum>)
                    -> ::std::result::Result<Self, ::from_pest::ConversionError<::from_pest::Void>>
                {
                    let pairs = &mut ::from_pest::pest::iterators::Pairs::single(primary);
                    Ok(#primary_body)
                }

                fn infix(lhs: Self, op: ::pest::iterators::Pair<#from_pest_lifetime, #rule_enum>, rhs: Self)
                    -> ::std::result::Result<Self, ::from_pest::ConversionError<::from_pest::Void>>
                {
                    let pairs = &mut ::from_pest::pest::iterators::Pairs::single(op);
                    Ok(#infix_body)
                }

                fn prefix(op: ::pest::iterators::Pair<#from_pest_lifetime, #rule_enum>, rhs: Self)
                    -> ::std::result::Result<Self, ::from_pest::ConversionError<::from_pest::Void>>
                {
                    let pairs = &mut ::from_pest::pest::iterators::Pairs::single(op);
                    Ok(#prefix_body)
                }

                fn postfix(lhs: Self, op: ::pest::iterators::Pair<#from_pest_lifetime, #rule_enum>)
                    -> ::std::result::Result<Self, ::from_pest::ConversionError<::from_pest::Void>>
                {
                    let pairs = &mut ::from_pest::pest::iterators::Pairs::single(op);
                    Ok(#postfix_body)
                }
            }
        }
    };
    let pratt_query_template = |body: TokenStream| {
        quote! {
            impl #impl_generics ::from_pest::pratt_parser::PrattParserQuery<Rule> for #name #ty_generics #where_clause {
                fn query_operator(rule: Rule) -> Option<::from_pest::pratt_parser::Affix> {
                    #body
                }
            }
        }
    };

    match data {
        Data::Union(data) => Err(Error::new(
            data.union_token.span(),
            "Cannot derive FromPest for union",
        )),
        Data::Struct(data) => derive_for_struct(
            grammar,
            &name,
            &rule_enum,
            &rule_variant,
            data,
            from_pest_template,
        ),
        Data::Enum(data) => {
            let mut pratt_attrs = attrs.into_iter().filter(|attr| match attr {
                DeriveAttribute::Expr(_)
                | DeriveAttribute::Infix(_)
                | DeriveAttribute::Prefix(_)
                | DeriveAttribute::Postfix(_) => true,
                _ => false,
            });
            match (pratt_attrs.next(), pratt_attrs.next()) {
                (Some(_), Some(attr)) => Err(Error::new(
                    attr.span(),
                    "at most one out of #[pest_ast(expr)] / #[pest_ast(infix)] / #[pest_ast(prefix)] / #[pest_ast(postfix)] can be present",
                ))?,
                (None, None) => derive_for_enum(grammar, &name, &rule_enum, &rule_variant, data, from_pest_template),
                (Some(DeriveAttribute::Expr(_)), None) => derive_pratt(&name, &rule_enum, &rule_variant, data, from_pest_template, pratt_query_template, pratt_template),
                (Some(affix), None) => {
                    let pratt_query_impl = derive_pratt_query(&rule_enum, data.clone(), &affix, pratt_query_template)?;
                    let from_pest_impl = derive_for_enum(grammar, &name, &rule_enum, &rule_variant, data, from_pest_template)?;
                    Ok(quote!(#pratt_query_impl #from_pest_impl))
                },
                _ => unreachable!()
            }
        }
    }
}

/// Implements `FromPest::from_pest` for some struct.
///
/// For child functions, sets up an environment with:
///
/// ```text
/// let span: Span;         // the span of this production
/// let inner: &mut Pairs;  // the contents of this production
/// ```
///
/// Child function is required to produce an _expression_ which constructs an instance of `Self`
/// from the `Pair`s in `inner` or early returns a `NoMatch`. `inner` and `span` are free working
/// space, but `inner` should represent the point past all consumed productions afterwards.
fn derive_for_struct<F>(
    grammar: Option<FilePath>,
    name: &Ident,
    rule_enum: &Path,
    rule_variant: &Ident,
    DataStruct { fields, .. }: DataStruct,
    from_pest_template: F,
) -> Result<TokenStream>
where
    F: FnOnce(TokenStream) -> TokenStream,
{
    if let Some(_path) = grammar {
        unimplemented!("Grammar introspection not implemented yet")
    }

    let construct = field::convert(&parse_quote!(#name), fields)?;

    let from_pest_body = quote! {
        let mut clone = pest.clone();
        let pair = clone.next().ok_or(::from_pest::ConversionError::NoMatch)?;
        if pair.as_rule() == #rule_enum::#rule_variant {
            let span = pair.as_span();
            let mut inner = pair.into_inner();
            let inner = &mut inner;
            let this = #construct;
            if inner.clone().next().is_some() {
                panic!(
                    concat!(
                        "when converting ",
                        stringify!(#name),
                        ", found extraneous {:?}",
                    ),
                    inner,
                )
            }
            *pest = clone;
            Ok(this)
        } else {
            Err(::from_pest::ConversionError::NoMatch)
        }
    };
    Ok(from_pest_template(from_pest_body))
}

#[allow(unused)]
#[allow(clippy::needless_pass_by_value)]
fn derive_for_enum<F>(
    grammar: Option<FilePath>,
    name: &Ident,
    rule_enum: &Path,
    rule_variant: &Ident,
    DataEnum { variants, .. }: DataEnum,
    from_pest_template: F,
) -> Result<TokenStream>
where
    F: FnOnce(TokenStream) -> TokenStream,
{
    if let Some(_path) = grammar {
        unimplemented!("Grammar introspection not implemented yet")
    }

    let variant_name = variants
        .iter()
        .map(|variant| variant.ident.clone())
        .collect_vec();

    let construct_variant: Vec<TokenStream> = variants
        .into_iter()
        .map(|variant| {
            let variant_name = variant.ident;
            if variant.fields == Fields::Unit {
                Ok(quote! {
                    inner.peek()
                        .and_then(|pair|
                            if pair.as_rule() == #rule_enum::#variant_name {
                                let _ = inner.next();
                                Some(#name::#variant_name)
                            } else {
                                None
                            }
                        )
                        .ok_or(::from_pest::ConversionError::NoMatch)?
                })
            } else {
                field::convert(&parse_quote!(#name::#variant_name), variant.fields)
            }
        })
        .collect::<Result<_>>()?;

    let name = iter::repeat(name.clone()).take(variant_name.len());

    let from_pest_body = quote! {
        let mut clone = pest.clone();
        let pair = clone.next().ok_or(::from_pest::ConversionError::NoMatch)?;
        if pair.as_rule() == #rule_enum::#rule_variant {
            let this = Err(::from_pest::ConversionError::NoMatch)
                #(.or_else(|_: ::from_pest::ConversionError<::from_pest::Void>| {
                    let span = pair.as_span();
                    let mut inner = pair.clone().into_inner();
                    let inner = &mut inner;
                    let this = #construct_variant;
                    if inner.clone().next().is_some() {
                        panic!(
                            concat!(
                                "when converting ",
                                stringify!(#name),
                                "::",
                                stringify!(#variant_name),
                                ", found extraneous {:?}",
                            ),
                            inner,
                        )
                    }
                    Ok(this)
                }))*?;
            *pest = clone;
            Ok(this)
        } else {
            Err(::from_pest::ConversionError::NoMatch)
        }
    };

    Ok(from_pest_template(from_pest_body))
}

fn derive_pratt_query<F>(
    rule_enum: &Path,
    data: DataEnum,
    affix: &DeriveAttribute,
    pratt_query_template: F,
) -> Result<TokenStream>
where
    F: FnOnce(TokenStream) -> TokenStream,
{
    let cases: Vec<TokenStream> = data
        .variants
        .into_iter()
        .map(|Variant { ident, attrs, .. }| {
            let attrs = FieldAttribute::from_attributes(attrs)?;
            if attrs.len() > 1 {
                Err(Error::new(
                    ident.span(),
                    "cannot have multiple inner derives for #[pest_ast(..)] here",
                ))?
            }
            Ok(match attrs.into_iter().next() {
                Some(FieldAttribute::Operator(OperatorAttribute {
                    precedence,
                    associativity,
                })) => {
                    let precedence = precedence.rhs.value();
                    match (affix, associativity) {
                        (DeriveAttribute::Infix(_), None) => Err(Error::new(
                            ident.span(),
                            "infix operators must have an associativity",
                        ))?,
                        (DeriveAttribute::Prefix(_), Some(_)) => Err(Error::new(
                            ident.span(),
                            "prefix operators must not have an associativity",
                        ))?,
                        (DeriveAttribute::Postfix(_), Some(_)) => Err(Error::new(
                            ident.span(),
                            "postfix operators must not have an associativity",
                        ))?,
                        (DeriveAttribute::Infix(_), Some(associativity)) => {
                            let associativity = associativity.rhs.value();
                            match associativity.as_ref() {
                                "left" => quote! {
                                    #rule_enum::#ident => Some(::from_pest::pratt_parser::Affix::Infix {
                                        precedence: #precedence * 10,
                                        associativity: ::from_pest::pratt_parser::Associativity::Left,
                                    })
                                },
                                "right" => quote! {
                                    #rule_enum::#ident => Some(::from_pest::pratt_parser::Affix::Infix {
                                        precedence: #precedence * 10,
                                        associativity: ::from_pest::pratt_parser::Associativity::Right,
                                    })
                                },
                                _ => Err(Error::new(
                                    ident.span(),
                                    "associativity must either be \"left\" or \"right\" ",
                                ))?,
                            }
                        }
                        (DeriveAttribute::Prefix(_), None) => quote! {
                            #rule_enum::#ident => Some(::from_pest::pratt_parser::Affix::Prefix {
                                precedence: #precedence * 10,
                            })
                        },
                        (DeriveAttribute::Postfix(_), None) => quote! {
                            #rule_enum::#ident => Some(::from_pest::pratt_parser::Affix::Postfix {
                                precedence: #precedence * 10,
                            })
                        },
                        _ => unreachable!(),
                    }
                }
                Some(_) => Err(Error::new(ident.span(), "unexpected pest_ast attribute"))?,
                None => match affix {
                    DeriveAttribute::Infix(_) => Err(Error::new(
                        ident.span(),
                        "expected #[pest_ast(precedence = ..., associativity = ...])",
                    ))?,
                    _ => Err(Error::new(
                        ident.span(),
                        "expected #[pest_ast(precedence = ...)]",
                    ))?,
                },
            })
        })
        .collect::<Result<Vec<_>>>()?;

    let pratt_query_body = quote! {
        match rule {
            #(#cases,)*
            _ => None,
        }
    };
    let pratt_query_impl = pratt_query_template(pratt_query_body);
    Ok(quote!(#pratt_query_impl))
}

fn derive_pratt<F, G, H>(
    name: &Ident,
    rule_enum: &Path,
    rule_variant: &Ident,
    data: DataEnum,
    from_pest_template: F,
    pratt_query_template: G,
    pratt_template: H,
) -> Result<TokenStream>
where
    F: FnOnce(TokenStream) -> TokenStream,
    G: FnOnce(TokenStream) -> TokenStream,
    H: FnOnce(TokenStream, TokenStream, TokenStream, TokenStream) -> TokenStream,
{
    let mut primary: Option<TokenStream> = None;
    let mut infix: Option<(TokenStream, TokenStream)> = None;
    let mut prefix: Option<(TokenStream, TokenStream)> = None;
    let mut postfix: Option<(TokenStream, TokenStream)> = None;
    for Variant {
        ident: variant_ident,
        fields,
        attrs,
        ..
    } in data.variants
    {
        match fields {
            Fields::Unnamed(fields) => {
                let mut f = fields.unnamed.into_iter();
                let attrs = FieldAttribute::from_attributes(attrs)?;
                let ref attr = if attrs.len() > 1 {
                    Err(Error::new(
                        name.span(),
                        "variants with multiple inner derives #[pest_ast(..)] derives is disallowed for #[pest_ast(expr)] enums",
                    ))?
                } else {
                    &attrs[0]
                };
                use attributes::FieldAttribute::{Infix, Postfix, Prefix, Primary};
                match (attr, f.next(), f.next(), f.next(), f.next()) {
                    (Primary(_), Some(_), None, None, None) => {
                        if primary.is_some() {
                            Err(Error::new(
                                name.span(),
                                "duplicate primary expression variants not allowed",
                            ))?
                        }
                        primary = Some(
                            quote!(#name::#variant_ident(::from_pest::FromPest::from_pest(pairs)?)),
                        )
                    }
                    (Infix(_), Some(_), Some(Field { ty, .. }), Some(_), None) => {
                        if infix.is_some() {
                            Err(Error::new(
                                name.span(),
                                "duplicate infix expression variants not allowed",
                            ))?
                        }
                        infix = Some((
                            quote!(#name::#variant_ident(Box::new(lhs), ::from_pest::FromPest::from_pest(pairs)?, Box::new(rhs))),
                            quote!(<#ty as ::from_pest::pratt_parser::PrattParserQuery<Rule>>::query_operator(rule)),
                        ))
                    }
                    (Prefix(_), Some(Field { ty, .. }), Some(_), None, None) => {
                        if prefix.is_some() {
                            Err(Error::new(
                                name.span(),
                                "duplicate prefix expression variants not allowed",
                            ))?
                        }
                        prefix = Some((
                            quote!(#name::#variant_ident(::from_pest::FromPest::from_pest(pairs)?, Box::new(rhs))),
                            quote!(<#ty as ::from_pest::pratt_parser::PrattParserQuery<Rule>>::query_operator(rule)),
                        ))
                    }
                    (Postfix(_), Some(_), Some(Field { ty, .. }), None, None) => {
                        if postfix.is_some() {
                            Err(Error::new(
                                name.span(),
                                "multiple postfix expression variants not allowed",
                            ))?
                        }
                        postfix = Some((
                            quote!(#name::#variant_ident(Box::new(lhs), ::from_pest::FromPest::from_pest(pairs)?)),
                            quote!(<#ty as ::from_pest::pratt_parser::PrattParserQuery<Rule>>::query_operator(rule)),
                        ))
                    }
                    _ => Err(Error::new(
                        name.span(),
                        "operators can only be binary/unary",
                    ))?,
                }
            }
            _ => {
                Err(Error::new(
                    name.span(),
                    "#[pest_ast(expr)] can currently only be derived for enums with unnamed variants.",
                ))?;
            }
        }
    }
    if primary.is_none() {
        Err(Error::new(
            name.span(),
            "#[pest_ast(primary)] seems to be missing for #[pest_ast(expr)].",
        ))?;
    }
    let primary = primary.unwrap();
    let (infix_impl, infix_query) = infix.unwrap_or((quote!(unreachable!()), quote!(None)));
    let (prefix_impl, prefix_query) = prefix.unwrap_or((quote!(unreachable!()), quote!(None)));
    let (postfix_impl, postfix_query) = postfix.unwrap_or((quote!(unreachable!()), quote!(None)));

    let from_pest_body = quote! {
        let mut clone = pest.clone();
        let pair = clone.next().ok_or(::from_pest::ConversionError::NoMatch)?;
        if pair.as_rule() == #rule_enum::#rule_variant {
            let span = pair.as_span();
            let mut inner = pair.into_inner();
            let inner = &mut inner;
            use ::from_pest::pratt_parser::PrattParser;
            let this = Self::pratt_parse(inner)?;
            if inner.clone().next().is_some() {
                panic!(
                    concat!(
                        "when converting ",
                        stringify!(#name),
                        ", found extraneous {:?}",
                    ),
                    inner,
                )
            }
            *pest = clone;
            Ok(this)
        } else {
            Err(::from_pest::ConversionError::NoMatch)
        }
    };
    let query_op_body = quote! {
        #infix_query.or_else(|| #prefix_query.or_else(|| #postfix_query))
    };
    let from_pest_impl = from_pest_template(from_pest_body);
    let pratt_query_impl = pratt_query_template(query_op_body);
    let pratt_impl = pratt_template(primary, infix_impl, prefix_impl, postfix_impl);
    Ok(quote!(#from_pest_impl #pratt_query_impl #pratt_impl))
}
