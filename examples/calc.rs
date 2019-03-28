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
  Parser,
  iterators::Pairs,
  prec_climber::{
    PrecClimber,
    Assoc::*,
    Op,
  },
};
use std::io::{stdin, stdout, Write};
use parser::Rule;

fn interpret_str(pairs: Pairs<Rule>, climber: &PrecClimber<Rule>) -> String {
  climber
      .map_primary(|primary| match primary.as_rule() {
          Rule::int  => primary.as_str().to_owned(),
          Rule::expr => interpret_str(primary.into_inner(), climber),
          _          => unreachable!(),
      })
      .map_prefix(|op, rhs| match op.as_rule() {
          Rule::neg  => format!("(-{})", rhs),
          _          => unreachable!(),
      })
      .map_postfix(|lhs, op| match op.as_rule() {
          Rule::fac  => format!("({}!)", lhs),
          _          => unreachable!(),
      })
      .map_infix(|lhs, op, rhs| match op.as_rule() {
          Rule::add  => format!("({}+{})", lhs, rhs),
          Rule::sub  => format!("({}-{})", lhs, rhs),
          Rule::mul  => format!("({}*{})", lhs, rhs),
          Rule::div  => format!("({}/{})", lhs, rhs),
          Rule::pow  => format!("({}^{})", lhs, rhs),
          _          => unreachable!(),
      })
      .climb(pairs)
      .unwrap()
}

fn interpret_i32(pairs: Pairs<Rule>, climber: &PrecClimber<Rule>) -> i128 {
  climber
      .map_primary(|primary| match primary.as_rule() {
          Rule::int  => primary.as_str().parse().unwrap(),
          Rule::expr => interpret_i32(primary.into_inner(), climber),
          _          => unreachable!(),
      })
      .map_prefix(|op, rhs| match op.as_rule() {
          Rule::neg  => -rhs,
          _          => unreachable!(),
      })
      .map_postfix(|lhs, op| match op.as_rule() {
          Rule::fac  => (1..lhs+1).product(),
          _          => unreachable!(),
      })
      .map_infix(|lhs, op, rhs| match op.as_rule() {
          Rule::add  => lhs + rhs,
          Rule::sub  => lhs - rhs,
          Rule::mul  => lhs * rhs,
          Rule::div  => lhs / rhs,
          Rule::pow  => (1..rhs+1).map(|_| lhs).product(),
          _          => unreachable!(),
      })
      .climb(pairs)
      .unwrap()
}

fn main() {

    let climber = PrecClimber::new()
      .op(Op::infix(Rule::add, Left) | Op::infix(Rule::sub, Left))
      .op(Op::infix(Rule::mul, Left) | Op::infix(Rule::div, Left))
      .op(Op::infix(Rule::pow, Right))
      .op(Op::postfix(Rule::fac))
      .op(Op::prefix(Rule::neg));

    let stdin = stdin();
    let mut stdout = stdout();

    loop {
      let source = {
        print!("> ");
        let _ = stdout.flush();
        let mut input = String::new();
        stdin.read_line(&mut input).unwrap();
        input.trim().to_string()
      };

      let pairs = match parser::Parser::parse(Rule::program, &source) {
        Ok(mut parse_tree) => {
          parse_tree
            .next().unwrap().into_inner() // inner of program
            .next().unwrap().into_inner() // inner of expr
        },
        Err(err) => {
          println!("Failed parsing input: {:}", err);
          continue;
        }
      };

      let result = interpret_i32(pairs.clone(), &climber);
      let pretty = interpret_str(pairs.clone(), &climber);

      println!("{} => {} => {}", source, pretty, result);
    }
}

