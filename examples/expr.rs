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

  type PestError = ConversionError<Void>;

  #[derive(Debug)]
  pub struct Program<'p> {
    pub expr: Expr<'p>,
  }

  #[derive(Debug)]
  pub enum Expr<'p> {
    UnaryPrefix(UnaryPrefix<'p>),
    BinaryInfix(BinaryInfix<'p>),
    UnarySuffix(UnarySuffix<'p>),
    Term(Term<'p>),
  }

  #[derive(Debug)]
  pub struct UnaryPrefix<'p> {
    pub op: UnaryPrefixOp,
    pub expr: Box<Expr<'p>>
  }

  #[derive(Debug)]
  pub enum UnaryPrefixOp {
    Not,
    Neg,
  }

  #[derive(Debug)]
  pub struct UnarySuffix<'p> {
    pub expr: Box<Expr<'p>>,
    pub op: UnarySuffixOp,
  }

  #[derive(Debug)]
  pub enum UnarySuffixOp {
    Try,
  }

  #[derive(Debug)]
  pub struct BinaryInfix<'p> {
    pub lhs: Box<Expr<'p>>,
    pub op: BinaryInfixOp,
    pub rhs: Box<Expr<'p>>,
  }

  #[derive(Debug)]
  pub enum BinaryInfixOp {
    Add,
    Mul,
  }

  #[derive(Debug)]
  pub struct Term<'p> {
    pub term: &'p str,
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
          Rule::expr         => Ok(Expr::from_pest(&mut pair.into_inner())?),
          Rule::term         => Ok(Expr::Term(Term::from_pest(&mut Pairs::single(pair))?)),
          Rule::unary_prefix => Ok(Expr::UnaryPrefix(UnaryPrefix::from_pest(&mut Pairs::single(pair))?)),
          Rule::unary_suffix => {
            let mut inner = pair.into_inner();
            let expr = Expr::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
            inner.try_fold(expr, |acc, pair|
              match UnarySuffixOp::from_pest(&mut Pairs::single(pair)) {
                Ok(op) => Ok(Expr::UnarySuffix(UnarySuffix {
                  expr: box acc,
                  op: op,
                })),
                Err(e) => Err(e)
              })
          },
          _ => Err(ConversionError::NoMatch),
        },
        |lhs: Result<Expr<'p>, PestError>, pair: Pair<Rule>, rhs: Result<Expr<'p>, PestError>|
        Ok(Expr::BinaryInfix(BinaryInfix {
          lhs: box lhs?,
          op: BinaryInfixOp::from_pest(&mut Pairs::single(pair))?,
          rhs: box rhs?
        }))
      )
    }
  }

  impl<'p> FromPest<'p> for UnaryPrefix<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<UnaryPrefix<'p>, PestError> {
      let mut inner = pest.next().unwrap().into_inner();
      Ok(UnaryPrefix {
        op: UnaryPrefixOp::from_pest(&mut inner)?,
        expr: box Expr::from_pest(&mut inner)?,
      })
    }
  }

  impl<'p> FromPest<'p> for Term<'p> {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<Term<'p>, PestError> {
      Ok(Term {
        term: pest.next().unwrap().as_str()
      })
    }
  }

  impl<'p> FromPest<'p> for BinaryInfixOp {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<BinaryInfixOp, PestError> {
      Ok(match pest.next().unwrap().as_rule() {
        Rule::add => BinaryInfixOp::Add,
        Rule::mul => BinaryInfixOp::Mul,
        _         => unreachable!(),
      })
    }
  }
  impl<'p> FromPest<'p> for UnaryPrefixOp {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<UnaryPrefixOp, PestError> {
      Ok(match pest.next().unwrap().as_rule() {
        Rule::not => UnaryPrefixOp::Not,
        Rule::neg => UnaryPrefixOp::Neg,
        _         => unreachable!(),
      })
    }
  }
  impl<'p> FromPest<'p> for UnarySuffixOp {
    type Rule = Rule;
    type FatalError = Void;
    fn from_pest(pest: &mut Pairs<'p, Rule>) -> Result<UnarySuffixOp, PestError> {
      Ok(match pest.next().unwrap().as_rule() {
        Rule::try => UnarySuffixOp::Try,
        _         => unreachable!(),
      })
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

