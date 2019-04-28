use {
    pest::{
        iterators::{Pair, Pairs},
        RuleType,
    },
    ConversionError as Error, Void,
};

#[derive(Debug)]
pub enum Associativity {
    Left,
    Right,
}

pub type Precedence = u64;

#[derive(Debug)]
pub enum Affix {
    Infix {
        precedence: Precedence,
        associativity: Associativity,
    },
    Prefix {
        precedence: Precedence,
    },
    Postfix {
        precedence: Precedence,
    },
}

pub trait PrattParserQuery<R> {
    fn query_operator(rule: R) -> Option<Affix>;
}

pub trait PrattParser<'i, R>
where
    R: RuleType,
    Self: Sized + PrattParserQuery<R>,
{
    fn primary(pair: Pair<'i, R>) -> Result<Self, Error<Void>>;

    fn infix(lhs: Self, op: Pair<'i, R>, rhs: Self) -> Result<Self, Error<Void>>;

    fn prefix(op: Pair<'i, R>, rhs: Self) -> Result<Self, Error<Void>>;

    fn postfix(lhs: Self, op: Pair<'i, R>) -> Result<Self, Error<Void>>;

    fn pratt_parse(pairs: &mut Pairs<'i, R>) -> Result<Self, Error<Void>> {
        Self::parse_expr(pairs, 0)
    }

    fn parse_expr(pairs: &mut Pairs<'i, R>, rbp: Precedence) -> Result<Self, Error<Void>> {
        let mut lhs = Self::nud(pairs);
        while rbp < Self::lbp(pairs) {
            lhs = Self::led(pairs, lhs?);
        }
        lhs
    }

    fn nud(pairs: &mut Pairs<'i, R>) -> Result<Self, Error<Void>> {
        let pair = pairs.next().expect("Pratt parsing expects non-empty Pairs");
        match Self::peek_affix(&pair) {
            Some(Affix::Prefix { precedence }) => {
                let rhs = Self::parse_expr(pairs, precedence - 1);
                Self::prefix(pair, rhs?)
            }
            None => Self::primary(pair),
            _ => panic!(
                "Expected unary-prefix or primary expression, found {}",
                pair
            ),
        }
    }

    fn led(pairs: &mut Pairs<'i, R>, lhs: Self) -> Result<Self, Error<Void>> {
        let pair = pairs.next().expect("Pratt parsing expects non-empty Pairs");
        match Self::peek_affix(&pair) {
            Some(Affix::Infix {
                associativity,
                precedence,
            }) => {
                let rhs = match associativity {
                    Associativity::Left => Self::parse_expr(pairs, precedence),
                    Associativity::Right => Self::parse_expr(pairs, precedence - 1),
                };
                Self::infix(lhs, pair, rhs?)
            }
            Some(Affix::Postfix { .. }) => Self::postfix(lhs, pair),
            _ => panic!(
                "Expected unary-postfix or binary-infix expression, found {}",
                pair
            ),
        }
    }

    fn lbp(pairs: &mut Pairs<'i, R>) -> Precedence {
        match pairs.peek() {
            Some(pair) => match Self::peek_affix(&pair) {
                Some(Affix::Infix { precedence, .. })
                | Some(Affix::Prefix { precedence })
                | Some(Affix::Postfix { precedence }) => precedence,
                None => panic!("Expected operator, found {}", pair),
            },
            None => 0,
        }
    }

    fn peek_affix(pair: &Pair<'i, R>) -> Option<Affix> {
        pair.clone()
            .into_inner()
            .peek()
            .and_then(|pair| Self::query_operator(pair.as_rule()))
    }
}
