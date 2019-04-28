#![allow(clippy::eval_order_dependence)] // syn patterns

use {
    itertools::Itertools,
    proc_macro2::TokenStream,
    quote::ToTokens,
    syn::{
        parse::{Error, Parse, ParseStream, Parser, Result},
        punctuated::Punctuated,
        spanned::Spanned,
        token::Paren,
        Attribute, Ident, LitStr, LitInt, Path,
    },
};

mod kw {
    custom_keyword!(grammar);
    custom_keyword!(outer);
    custom_keyword!(inner);
    custom_keyword!(with);
    custom_keyword!(rule);
    custom_keyword!(expr);
    custom_keyword!(primary);
    custom_keyword!(infix);
    custom_keyword!(prefix);
    custom_keyword!(postfix);
    custom_keyword!(associativity);
    custom_keyword!(precedence);
}

/// `#[pest_ast(..)]` for the outer `#[derive(FromPest)]`
pub(crate) enum DeriveAttribute {
    /// `grammar = "grammar.rs"`
    Grammar(GrammarAttribute),
    /// `rule(path::to)`
    Rule(RuleAttribute),
    /// `expr`
    Expr(ExprAttribute),
    /// `infix`
    Infix(InfixAttribute),
    /// `prefix`
    Prefix(PrefixAttribute),
    /// `postfix`
    Postfix(PostfixAttribute),
}

/// `#[pest_ast(..)]` for fields in `#[derive(FromPest)]`
pub(crate) enum FieldAttribute {
    /// `outer(with(path::to),*)`
    Outer(OuterAttribute),
    /// `inner(rule(path::to), with(path::to),*)`
    Inner(InnerAttribute),
    /// `primary`
    Primary(PrimaryAttribute),
    /// `infix`
    Infix(InfixAttribute),
    /// `prefix`
    Prefix(PrefixAttribute),
    /// `postfix`
    Postfix(PostfixAttribute),
    /// `precedence = 1`
    /// or
    /// `precedence = 1, associativity = "left"`
    Operator(OperatorAttribute),
}

pub(crate) struct GrammarAttribute {
    pub(crate) grammar: kw::grammar,
    pub(crate) eq: Token![=],
    pub(crate) lit: LitStr,
}

pub(crate) struct OuterAttribute {
    pub(crate) outer: kw::outer,
    pub(crate) paren: Paren,
    pub(crate) with: Punctuated<WithAttribute, Token![,]>,
}

pub(crate) struct InnerAttribute {
    pub(crate) inner: kw::inner,
    pub(crate) paren: Paren,
    pub(crate) rule: Option<RuleAttribute>,
    pub(crate) comma: Option<Token![,]>,
    pub(crate) with: Punctuated<WithAttribute, Token![,]>,
}

pub(crate) struct WithAttribute {
    pub(crate) with: kw::with,
    pub(crate) paren: Paren,
    pub(crate) path: Path,
}

pub(crate) struct RuleAttribute {
    pub(crate) rule: kw::rule,
    pub(crate) paren: Paren,
    pub(crate) path: Path,
    pub(crate) sep: Token![::],
    pub(crate) variant: Ident,
}

pub(crate) struct ExprAttribute {
    pub(crate) expr: kw::expr,
}

pub(crate) struct PrimaryAttribute {
    pub(crate) primary: kw::primary,
}

pub(crate) struct InfixAttribute {
    pub(crate) infix: kw::infix,
}

pub(crate) struct PrefixAttribute {
    pub(crate) prefix: kw::prefix,
}

pub(crate) struct PostfixAttribute {
    pub(crate) postfix: kw::postfix,
}

pub(crate) struct OperatorAttribute {
    pub(crate) precedence: Precedence,
    pub(crate) associativity: Option<Associativity>,
}

pub struct Precedence {
    pub lhs: kw::precedence,
    pub eq: Token![=],
    pub rhs: LitInt,
}

pub struct Associativity {
    pub comma: Token![,],
    pub lhs: kw::associativity,
    pub eq: Token![=],
    pub rhs: LitStr,
}

impl DeriveAttribute {
    pub(crate) fn from_attributes(attrs: impl IntoIterator<Item = Attribute>) -> Result<Vec<Self>> {
        attrs
            .into_iter()
            .map(DeriveAttribute::from_attribute)
            .fold_results(vec![], |mut acc, t| {
                acc.extend(t);
                acc
            })
    }

    pub(crate) fn from_attribute(attr: Attribute) -> Result<Vec<Self>> {
        if attr.path != parse_quote!(pest_ast) {
            return Ok(vec![]);
        }

        Parser::parse2(
            |input: ParseStream| {
                let content;
                parenthesized!(content in input);
                let punctuated: Punctuated<_, Token![,]> =
                    content.parse_terminated(Parse::parse)?;
                Ok(punctuated.into_iter().collect_vec())
            },
            attr.tts,
        )
    }
}

impl FieldAttribute {
    pub(crate) fn from_attributes(attrs: impl IntoIterator<Item = Attribute>) -> Result<Vec<Self>> {
        attrs
            .into_iter()
            .map(FieldAttribute::from_attribute)
            .fold_results(vec![], |mut acc, t| {
                acc.extend(t);
                acc
            })
    }

    pub(crate) fn from_attribute(attr: Attribute) -> Result<Vec<Self>> {
        if attr.path != parse_quote!(pest_ast) {
            return Ok(vec![]);
        }

        Parser::parse2(
            |input: ParseStream| {
                let content;
                parenthesized!(content in input);
                let punctuated: Punctuated<_, Token![,]> =
                    content.parse_terminated(Parse::parse)?;
                Ok(punctuated.into_iter().collect_vec())
            },
            attr.tts,
        )
    }
}

impl Parse for DeriveAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(kw::grammar) {
            GrammarAttribute::parse(input).map(DeriveAttribute::Grammar)
        } else if lookahead.peek(kw::rule) {
            RuleAttribute::parse(input).map(DeriveAttribute::Rule)
        } else if lookahead.peek(kw::expr) {
            ExprAttribute::parse(input).map(DeriveAttribute::Expr)
        } else if lookahead.peek(kw::infix) {
            InfixAttribute::parse(input).map(DeriveAttribute::Infix)
        } else if lookahead.peek(kw::prefix) {
            PrefixAttribute::parse(input).map(DeriveAttribute::Prefix)
        } else if lookahead.peek(kw::postfix) {
            PostfixAttribute::parse(input).map(DeriveAttribute::Postfix)
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for FieldAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(kw::outer) {
            OuterAttribute::parse(input).map(FieldAttribute::Outer)
        } else if lookahead.peek(kw::inner) {
            InnerAttribute::parse(input).map(FieldAttribute::Inner)
        } else if lookahead.peek(kw::primary) {
            PrimaryAttribute::parse(input).map(FieldAttribute::Primary)
        } else if lookahead.peek(kw::infix) {
            InfixAttribute::parse(input).map(FieldAttribute::Infix)
        } else if lookahead.peek(kw::prefix) {
            PrefixAttribute::parse(input).map(FieldAttribute::Prefix)
        } else if lookahead.peek(kw::postfix) {
            PostfixAttribute::parse(input).map(FieldAttribute::Postfix)
        } else if lookahead.peek(kw::precedence) {
            OperatorAttribute::parse(input).map(FieldAttribute::Operator)
        } else {
            Err(lookahead.error())
        }
    }
}

impl ToTokens for DeriveAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            DeriveAttribute::Grammar(attr) => attr.to_tokens(tokens),
            DeriveAttribute::Rule(attr) => attr.to_tokens(tokens),
            DeriveAttribute::Expr(attr) => attr.to_tokens(tokens),
            DeriveAttribute::Infix(attr) => attr.to_tokens(tokens),
            DeriveAttribute::Prefix(attr) => attr.to_tokens(tokens),
            DeriveAttribute::Postfix(attr) => attr.to_tokens(tokens),
        }
    }
}

impl ToTokens for FieldAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            FieldAttribute::Outer(attr) => attr.to_tokens(tokens),
            FieldAttribute::Inner(attr) => attr.to_tokens(tokens),
            FieldAttribute::Primary(attr) => attr.to_tokens(tokens),
            FieldAttribute::Infix(attr) => attr.to_tokens(tokens),
            FieldAttribute::Prefix(attr) => attr.to_tokens(tokens),
            FieldAttribute::Postfix(attr) => attr.to_tokens(tokens),
            FieldAttribute::Operator(attr) => attr.to_tokens(tokens),
        }
    }
}

impl Parse for GrammarAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(GrammarAttribute {
            grammar: input.parse()?,
            eq: input.parse()?,
            lit: input.parse()?,
        })
    }
}

impl ToTokens for GrammarAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.grammar.to_tokens(tokens);
        self.eq.to_tokens(tokens);
        self.lit.to_tokens(tokens);
    }
}

impl Parse for OuterAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(OuterAttribute {
            outer: input.parse()?,
            paren: parenthesized!(content in input),
            with: content.parse_terminated(WithAttribute::parse)?,
        })
    }
}

impl ToTokens for OuterAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.outer.to_tokens(tokens);
        self.paren.surround(tokens, |tokens| {
            self.with.to_tokens(tokens);
        })
    }
}

impl Parse for InnerAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let inner = input.parse()?;
        let paren = parenthesized!(content in input);
        let (rule, comma) = if content.peek(kw::rule) {
            (Some(content.parse()?), content.parse().ok().and_then(Some))
        } else {
            (None, None)
        };
        let with = content.parse_terminated(WithAttribute::parse)?;
        Ok(InnerAttribute {
            inner,
            paren,
            rule,
            comma,
            with,
        })
    }
}

impl ToTokens for InnerAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.inner.to_tokens(tokens);
        self.paren.surround(tokens, |tokens| {
            if let Some(rule) = &self.rule {
                rule.to_tokens(tokens);
            }
            if let Some(comma) = &self.comma {
                comma.to_tokens(tokens);
            }
            self.with.to_tokens(tokens);
        })
    }
}

impl Parse for WithAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(WithAttribute {
            with: input.parse()?,
            paren: parenthesized!(content in input),
            path: content.parse()?,
        })
    }
}

impl ToTokens for WithAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.with.to_tokens(tokens);
        self.paren
            .surround(tokens, |tokens| self.path.to_tokens(tokens));
    }
}

impl Parse for RuleAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let rule = input.parse()?;
        let paren = parenthesized!(content in input);
        let mut path: Path = content.parse()?;
        let (variant, _) = path.segments.pop().unwrap().into_tuple();
        let sep = if path.segments.trailing_punct() {
            // fix trailing punct
            let (head, sep) = path.segments.pop().unwrap().into_tuple();
            path.segments.push(head);
            sep.unwrap()
        } else {
            Err(Error::new(
                path.span(),
                "must be a path to enum variant (both enum and variant)",
            ))?
        };
        if variant.arguments.is_empty() {
            Ok(RuleAttribute {
                rule,
                paren,
                path,
                sep,
                variant: variant.ident,
            })
        } else {
            Err(Error::new(path.span(), "must be a path to enum variant"))
        }
    }
}

impl ToTokens for RuleAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.rule.to_tokens(tokens);
        self.paren.surround(tokens, |tokens| {
            self.path.to_tokens(tokens);
            self.sep.to_tokens(tokens);
            self.variant.to_tokens(tokens);
        });
    }
}

impl Parse for ExprAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(ExprAttribute {
            expr: input.parse()?,
        })
    }
}

impl ToTokens for ExprAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.expr.to_tokens(tokens);
    }
}

impl Parse for InfixAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(InfixAttribute {
            infix: input.parse()?,
        })
    }
}

impl ToTokens for InfixAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.infix.to_tokens(tokens);
    }
}

impl Parse for PrefixAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(PrefixAttribute {
            prefix: input.parse()?,
        })
    }
}

impl ToTokens for PrefixAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.prefix.to_tokens(tokens);
    }
}

impl Parse for PostfixAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(PostfixAttribute {
            postfix: input.parse()?,
        })
    }
}

impl ToTokens for PostfixAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.postfix.to_tokens(tokens);
    }
}

impl Parse for PrimaryAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(PrimaryAttribute {
            primary: input.parse()?,
        })
    }
}

impl ToTokens for PrimaryAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.primary.to_tokens(tokens);
    }
}

impl Parse for OperatorAttribute {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(OperatorAttribute {
            precedence: Precedence {
                lhs: input.parse()?,
                eq: input.parse()?,
                rhs: input.parse()?,
            },
            associativity: if input.is_empty() {
                None
            } else {
                Some(Associativity {
                    comma: input.parse()?,
                    lhs: input.parse()?,
                    eq: input.parse()?,
                    rhs: input.parse()?,
                })
            },
        })
    }
}

impl ToTokens for OperatorAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.precedence.lhs.to_tokens(tokens);
        self.precedence.eq.to_tokens(tokens);
        self.precedence.rhs.to_tokens(tokens);
        if let Some(ref associativity) = self.associativity {
            associativity.comma.to_tokens(tokens);
            associativity.lhs.to_tokens(tokens);
            associativity.eq.to_tokens(tokens);
            associativity.rhs.to_tokens(tokens);
        }
    }
}
