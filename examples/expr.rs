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
      PREC_CLIMBER.climb(pest,
        |pair: Pair<Rule>|
        match pair.as_rule() {
          Rule::expr => Ok(Expr::from_pest(&mut pair.into_inner())?),
          Rule::term => Ok(Expr::Term(Term::from_pest(&mut Pairs::single(pair))?)),
          Rule::unop => climb_unop(&mut pair.into_inner()),
          _          => Err(ConversionError::NoMatch),
        },
        |lhs: Result<Expr<'p>, PestError>, pair: Pair<Rule>, rhs: Result<Expr<'p>, PestError>|
        Ok(Expr::BinaryOp(BinaryOp {
          lhs: box lhs?,
          op: Infix::from_pest(&mut Pairs::single(pair))?,
          rhs: box rhs?
        }))
      )
    }
  }

  fn climb_unop<'p>(pairs: &mut Pairs<'p,Rule>) -> Result<Expr<'p>, PestError> {
    let prefix = climb_prefix(pairs)?;
    let suffix = climb_suffix(pairs, prefix);
    suffix
  }

  fn climb_prefix<'p>(pairs: &mut Pairs<'p, Rule>) -> Result<Expr<'p>, PestError> {
    let pair = pairs.next().unwrap();
    Ok(match pair.as_rule() {
      Rule::not | Rule::neg => Expr::UnaryOp(UnaryOp {
        op: Either::Left(Prefix::from_pest(&mut Pairs::single(pair))?),
        expr: box climb_prefix(pairs)?,
      }),
      _ => Expr::from_pest(&mut Pairs::single(pair))?,
    })
  }

  fn climb_suffix<'p>(pairs: &mut Pairs<'p, Rule>, prefix: Expr<'p>) -> Result<Expr<'p>, PestError> {
    pairs.map(|pair| Suffix::from_pest(&mut Pairs::single(pair)))
      .try_fold(prefix, |acc, op|
        op.and_then(|op| Ok(Expr::UnaryOp(UnaryOp {
            op: Either::Right(op),
            expr: box acc,
          }))))
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
  //println!("parse tree = {:#?}", parse_tree);
  let syntax_tree = Program::from_pest(&mut parse_tree).expect("infallible");
  println!("syntax tree = {:#?}", syntax_tree);

  Ok(())
}

#[test]
fn expr_example_runs() {
  main().unwrap()
}

