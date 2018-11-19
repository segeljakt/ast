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
  use pest::{
    iterators::{Pair, Pairs},
    prec_climber::{PrecClimber, Assoc::*, Operator},
    RuleType
  };
  use from_pest::{FromPest, ConversionError};
  use void::Void;
  use either::Either;
  use std::collections::HashMap;

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
    pub expr: Box<Expr<'p>>,
    pub op: Either<Prefix,Suffix<'p>>,
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

  #[derive(Clone)]
  enum Position {
    Suffix,
    Prefix,
  }

  lazy_static! {
    static ref PREC_CLIMBER: PrecClimber<Rule> =
      PrecClimber::new(vec![
        Operator::new(Rule::add, Left),
        Operator::new(Rule::mul, Left),
      ]);
  }

  lazy_static! {
    static ref UNARY_OPS: HashMap<Rule, Position> = [
      (Rule::not, Position::Prefix),
      (Rule::neg, Position::Prefix),
      (Rule::try, Position::Suffix),
      (Rule::call, Position::Suffix)
    ].iter().cloned().collect();
  }

  impl<'p> FromPest<'p> for Expr<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Expr<'p>, PestError> {
      PREC_CLIMBER.climb_arity(&*UNARY_OPS, pest,
        |pair: Pair<Rule>| match pair.as_rule() {
          Rule::expr => Ok(Expr::from_pest(&mut pair.into_inner())?),
          Rule::term => Ok(Expr::Term(Term::from_pest(&mut Pairs::single(pair))?)),
          _          => unreachable!(),
        },
        |prefix: Pair<Rule>, rhs: Result<Expr<'p>, PestError>|
          Ok(Expr::UnaryOp(UnaryOp{
            op: Either::Left(Prefix::from_pest(&mut Pairs::single(prefix))?),
            expr: box rhs?,
        })),
        |lhs: Result<Expr<'p>, PestError>, suffix: Pair<Rule>|
          Ok(Expr::UnaryOp(UnaryOp{
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
      unary_ops: &HashMap<R, Position>,
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

    fn prefix_rec<'i, P, F, G, T>(
      unary_ops: &HashMap<R, Position>,
      pairs: &mut P,
      primary: &F,
      prefix: &G,
    ) -> T
    where P: Iterator<Item = Pair<'i, R>>,
          F: Fn(Pair<'i, R>) -> T,
          G: Fn(Pair<'i, R>, T) -> T,
    {
      let pair = pairs.next().unwrap();
      match unary_ops.get(&pair.as_rule()) {
        Some(Position::Prefix) => {
          let expr = Self::prefix_rec(unary_ops, pairs, primary, prefix);
          prefix(pair, expr)
        },
        _ => primary(pair),
      }
    }

  }

  impl<R: RuleType> ArityPrecClimber<R> for PrecClimber<R> {
    fn climb_arity<'i, P, F, G, H, I, T>(
      &self,
      unary_ops: &HashMap<R, Position>,
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
        let expr = Self::prefix_rec(&unary_ops, &mut inner, &primary, &prefix);
        inner.fold(expr, |acc, pair| suffix(acc, pair))
      };
      self.climb(&mut pairs.next().unwrap().into_inner(), unary, infix)
    }
  }

  impl<'p> FromPest<'p> for Call<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Call<'p>, PestError> {
      Ok(Call {
        id: Ident::from_pest(pest)?,
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
      println!("{}", pair);
      match pair.as_rule() {
        Rule::try  => Ok(Suffix::Try),
        Rule::call => Ok(Suffix::Call(Call::from_pest(&mut pair.into_inner())?)),
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

