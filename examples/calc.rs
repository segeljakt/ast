#![allow(bad_style)]

#[macro_use]
extern crate pest_derive;
extern crate pest;

mod parser {
  #[derive(Parser)]
  #[grammar = "../examples/calc.pest"]
  pub struct Parser;
}

use pest::{
  iterators::Pairs,
  prec_climber::{
    PrecClimber,
    Assoc::*,
    Op,
  },
};
use pest::Parser;
use std::fs;
use parser::Rule;

fn parse_expr(pairs: Pairs<Rule>, climber: &PrecClimber<Rule>) -> i32 {
  climber
      .map_primary(|primary| match primary.as_rule() {
          Rule::int  => primary.as_str().parse().unwrap(),
          Rule::expr => parse_expr(primary.into_inner(), climber),
          _          => unreachable!(),
      })
      .map_prefix(|op, rhs| match op.as_rule() {
          Rule::neg  => -rhs,
          _          => unreachable!(),
      })
      .map_postfix(|lhs, op| match op.as_rule() {
          Rule::fac  => (1..=lhs).product(),
          _          => unreachable!(),
      })
      .map_infix(|lhs, op, rhs| match op.as_rule() {
          Rule::add  => lhs + rhs,
          Rule::sub  => lhs - rhs,
          Rule::mul  => lhs * rhs,
          Rule::div  => lhs / rhs,
          Rule::pow  => (1..=rhs).map(|_| lhs).product(),
          _          => unreachable!(),
      })
      .climb(pairs)
      .unwrap()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {

  let climber = PrecClimber::new()
      .op(Op::infix(Rule::add, Left) | Op::infix(Rule::sub, Left))
      .op(Op::infix(Rule::mul, Left) | Op::infix(Rule::div, Left))
      .op(Op::infix(Rule::pow, Right))
      .op(Op::postfix(Rule::fac))
      .op(Op::prefix(Rule::neg));

  let source = String::from_utf8(fs::read("./examples/calc.txt")?)?;
  let mut parse_tree = parser::Parser::parse(Rule::program, &source)?;
  println!("parse tree = {:#?}", parse_tree);

  let pairs = parse_tree
    .next().unwrap().into_inner()  // inner of program
    .next().unwrap().into_inner(); // inner of expr
  let result = parse_expr(pairs, &climber);
  println!("result = {:#?}", result);

  Ok(())
}

