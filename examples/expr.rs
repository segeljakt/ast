#![allow(bad_style)]
#![feature(box_syntax)]

// Unfortunately, you currently have to import all four of these.
// We're considering what it would look like to make this redundant,
// and then you'd only need pest and pest-ast.

#[macro_use]
extern crate pest_derive;
extern crate from_pest;
extern crate pest;
extern crate void;
#[macro_use]
extern crate lazy_static;
extern crate either;

mod parser {
  #[derive(Parser)]
  #[grammar = "../examples/expr.pest"]
  pub struct Parser;
}

mod ast {
  use super::parser::Rule;
  use pest::{iterators::{Pair, Pairs}, prec_climber::PrecClimber};
  use from_pest::{FromPest, ConversionError};
  use void::Void;
  use either::Either;
  use pest::RuleType;

  type PestError = ConversionError<Void>;

  #[derive(Debug)]
  pub struct Program<'p> {
    pub expr: Expr<'p>,
  }

  #[derive(Debug)]
  pub enum Expr<'p> {
    UnaryOp(UnaryOp<'p>),
    BinaryOp(BinaryOp<'p>),
    Term(Term<'p>),
  }

  #[derive(Debug)]
  pub struct UnaryOp<'p> {
    pub op: Either<Prefix,Suffix<'p>>,
    pub expr: Box<Expr<'p>>
  }

  #[derive(Debug)]
  pub struct BinaryOp<'p> {
    pub lhs: Box<Expr<'p>>,
    pub op: Infix,
    pub rhs: Box<Expr<'p>>,
  }

  #[derive(Debug)]
  pub enum Prefix {
    Not,
    Neg,
  }

  #[derive(Debug)]
  pub enum Infix {
    Add,
    Mul,
  }

  #[derive(Debug)]
  pub enum Suffix<'p> {
    Try,
    Call(Call<'p>),
  }

  #[derive(Debug)]
  pub struct Call<'p> {
    pub id: Ident<'p>,
    pub args: Vec<Expr<'p>>
  }

  #[derive(Debug)]
  pub struct Ident<'p> {
    pub id: &'p str,
  }

  #[derive(Debug)]
  pub struct Term<'p> {
    pub id: Ident<'p>,
  }

  impl<'p> FromPest<'p> for Program<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Program<'p>, PestError> {
      Ok(Program {
        expr: Expr::from_pest(&mut pest.next().unwrap().into_inner())?
      })
    }
  }

  lazy_static! {
    static ref PREC_CLIMBER: PrecClimber<Rule> = {
      use pest::prec_climber::Assoc::*;
      use pest::prec_climber::Operator;

      PrecClimber::new(vec![
        Operator::new(Rule::add, Left),
        Operator::new(Rule::mul, Left),
      ])
    };
  }

  impl<'p> FromPest<'p> for Expr<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Expr<'p>, PestError> {
      PREC_CLIMBER.climb_arity(Rule::prefix, pest,
        |pair: Pair<Rule>| match pair.as_rule() {
          Rule::expr => Ok(Expr::from_pest(&mut pair.into_inner())?),
          Rule::term => Ok(Expr::Term(Term::from_pest(&mut Pairs::single(pair))?)),
          x          => { println!("{:?}", x); unreachable!() },
        },
        |prefix: Pair<Rule>, rhs: Result<Expr<'p>, PestError>| Ok(Expr::UnaryOp(UnaryOp{
          op: Either::Left(Prefix::from_pest(&mut Pairs::single(prefix))?),
          expr: box rhs?,
        })),
        |lhs: Result<Expr<'p>, PestError>, suffix: Pair<Rule>| Ok(Expr::UnaryOp(UnaryOp{
          op: Either::Right(Suffix::from_pest(&mut Pairs::single(suffix))?),
          expr: box lhs?,
        })),
        |lhs: Result<Expr<'p>, PestError>, infix: Pair<Rule>, rhs: Result<Expr<'p>, PestError>|
          Ok(Expr::BinaryOp(BinaryOp {
            lhs: box lhs?,
            op: Infix::from_pest(&mut Pairs::single(infix))?,
            rhs: box rhs?
        })),
      )
    }
  }

  trait ArityPrecClimber<R: RuleType> {
    fn climb_arity<'i, P, F, G, H, I, T>(
      &self,
      unary_rule: R,
      pairs: &mut P,
      primary: F,
      prefix: G,
      suffix: H,
      infix: I,
    ) -> T
    where P: Iterator<Item = Pair<'i, R>>,
          F: Fn(Pair<'i, R>) -> T,
          G: Fn(Pair<'i, R>, T) -> T,
          H: Fn(T, Pair<'i, R>) -> T,
          I: Fn(T, Pair<'i, R>, T) -> T;

    fn climb_prefix<'i, P, F, G, T>(
      unary_rule: R,
      pairs: &mut P,
      primary: &F,
      prefix: &G,
    ) -> T
    where P: Iterator<Item = Pair<'i, R>>,
          F: Fn(Pair<'i, R>) -> T,
          G: Fn(Pair<'i, R>, T) -> T,
    {
      let pair = pairs.next().unwrap();
      println!("{:?}", unary_rule);
      println!("{:?}", pair);
      if pair.as_rule() == unary_rule {
        let expr = Self::climb_prefix(unary_rule, pairs, primary, prefix);
        prefix(pair, expr)
      } else {
        primary(pair)
      }
    }

  }

  impl<R: RuleType> ArityPrecClimber<R> for PrecClimber<R> {
    fn climb_arity<'i, P, F, G, H, I, T>(
      &self,
      unary_rule: R,
      pairs: &mut P,
      primary: F,
      prefix: G,
      suffix: H,
      infix: I,
    ) -> T
    where P: Iterator<Item = Pair<'i, R>>,
          F: Fn(Pair<'i, R>) -> T,
          G: Fn(Pair<'i, R>, T) -> T,
          H: Fn(T, Pair<'i, R>) -> T,
          I: Fn(T, Pair<'i, R>, T) -> T,
    {
      let unary = |pair: Pair<'i,R>| {
        let mut inner = pair.into_inner();
        println!("{:}", inner);
        let expr = Self::climb_prefix(unary_rule, &mut inner, &primary, &prefix);
        inner.fold(expr, |acc, pair| suffix(acc, pair))
      };
      self.climb(pairs, unary, infix)
    }
  }

  impl<'p> FromPest<'p> for Call<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Call<'p>, PestError> {
      Ok(Call {
        id: Ident::from_pest(&mut Pairs::single(pest.next().unwrap()))?,
        args: pest.map(|pair| Expr::from_pest(&mut Pairs::single(pair)))
          .collect::<Result<Vec<Expr>, _>>()?,
      })
    }
  }

  impl<'p> FromPest<'p> for Term<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Term<'p>, PestError> {
      Ok(Term {
        id: Ident::from_pest(&mut Pairs::single(pest.next().unwrap()))?,
      })
    }
  }

  impl<'p> FromPest<'p> for Ident<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Ident<'p>, PestError> {
      Ok(Ident {
        id: pest.next().unwrap().as_str()
      })
    }
  }

  impl<'p> FromPest<'p> for Infix {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Infix, PestError> {
      match pest.next().unwrap().as_rule() {
        Rule::add => Ok(Infix::Add),
        Rule::mul => Ok(Infix::Mul),
        _         => Err(ConversionError::NoMatch),
      }
    }
  }
  impl<'p> FromPest<'p> for Prefix {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Prefix, PestError> {
      match pest.next().unwrap().as_rule() {
        Rule::not => Ok(Prefix::Not),
        Rule::neg => Ok(Prefix::Neg),
        _         => Err(ConversionError::NoMatch),
      }
    }
  }
  impl<'p> FromPest<'p> for Suffix<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Suffix<'p>, PestError> {
      let pair = pest.next().unwrap();
      match pair.as_rule() {
        Rule::try  => Ok(Suffix::Try),
        Rule::call => Ok(Suffix::Call(Call::from_pest(&mut Pairs::single(pair))?)),
        _          => Err(ConversionError::NoMatch),
      }
    }
  }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
  use ast::Program;
  use from_pest::FromPest;
  use pest::Parser;
  use std::fs;

  let source = String::from_utf8(fs::read("./examples/expr.txt")?)?;
  let mut parse_tree = parser::Parser::parse(parser::Rule::program, &source)?;
  println!("parse tree = {:#?}", parse_tree);
  let syntax_tree = Program::from_pest(&mut parse_tree).expect("infallible");
  println!("syntax tree = {:#?}", syntax_tree);

  Ok(())
}

#[test]
fn expr_example_runs() {
  main().unwrap()
}

