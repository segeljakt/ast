#![allow(bad_style)]
#![feature(box_syntax)]

// Unfortunately, you currently have to import all four of these.
// We're considering what it would look like to make this redundant,
// and then you'd only need pest and pest-ast.

#[macro_use]
extern crate pest_derive;
extern crate from_pest;
#[macro_use]
extern crate pest_ast;
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
    use from_pest::{ConversionError, FromPest};
    use pest::{
        iterators::Pairs,
        pratt_parser::{Assoc::*, Op, PrattParser},
        Span,
    };
    use void::Void;

    type PestError = ConversionError<Void>;

    #[derive(Debug, FromPest)]
    #[pest_ast(rule(Rule::Program))]
    pub struct ParseTree<'i> {
        pub prog: Program<'i>,
        pub eoi: EOI,
    }

    #[derive(Debug, FromPest)]
    #[pest_ast(rule(Rule::EOI))]
    pub struct EOI;

    #[derive(Debug, FromPest)]
    #[pest_ast(rule(Rule::Program))]
    pub struct Program<'i> {
        pub expr: Expr<'i>,
    }

    #[derive(Debug)]
    pub enum Expr<'i> {
        Unary {
            expr: Box<Expr<'i>>,
            op: UnaryOp<'i>,
        },
        Binary {
            lhs: Box<Expr<'i>>,
            op: BinaryOp,
            rhs: Box<Expr<'i>>,
        },
        Term {
            id: Ident<'i>,
        },
    }

    #[derive(Debug)]
    //     #[pest_ast(rule(Rule::Prefix))]
    pub enum UnaryOp<'i> {
        Not,
        Neg,
        Try,
        Call(Call<'i>),
    }

    #[derive(Debug)]
    pub enum BinaryOp {
        Add,
        Sub,
        Mul,
        Div,
    }

    #[derive(Debug, FromPest)]
    #[pest_ast(rule(Rule::Call))]
    pub struct Call<'i> {
        pub id: Ident<'i>,
        pub args: Vec<Expr<'i>>,
    }

    fn span_into_str(span: Span) -> &str {
        span.as_str()
    }

    #[derive(Debug, FromPest)]
    #[pest_ast(rule(Rule::Ident))]
    pub struct Ident<'i> {
        #[pest_ast(outer(with(span_into_str)))]
        pub id: &'i str,
    }

    lazy_static! {
        static ref PRATT_PARSER: PrattParser<Rule> = PrattParser::new()
            .op(Op::infix(Rule::Add, Left) | Op::infix(Rule::Sub, Left))
            .op(Op::infix(Rule::Mul, Left) | Op::infix(Rule::Div, Left))
            .op(Op::postfix(Rule::Try) | Op::postfix(Rule::Call))
            .op(Op::prefix(Rule::Not) | Op::prefix(Rule::Neg));
    }

    impl<'i> FromPest<'i> for Expr<'i> {
        type Rule = Rule;
        type FatalError = Void;
        fn from_pest(pest: &mut Pairs<'i, Rule>) -> Result<Expr<'i>, PestError> {
            println!("[[FROM PEST]] {}", pest);
            PRATT_PARSER
                .map_primary(|pair| {
                    println!("Primary: {}", pair);
                    match pair.as_rule() {
                        Rule::Expr => Ok(Expr::from_pest(&mut pair.into_inner())?),
                        Rule::Term => Ok(Expr::Term {
                            id: Ident::from_pest(&mut Pairs::single(pair))?,
                        }),
                        _ => unreachable!(),
                    }
                })
                .map_prefix(|op, r| {
                    Ok(Expr::Unary {
                        op: match op.as_rule() {
                            Rule::Not => Ok(UnaryOp::Not),
                            Rule::Neg => Ok(UnaryOp::Neg),
                            _ => Err(ConversionError::NoMatch),
                        }?,
                        expr: box r?,
                    })
                })
                .map_postfix(|l, op| {
                    println!("Postfix: {}", op);
                    Ok(Expr::Unary {
                        op: match op.as_rule() {
                            Rule::Try => Ok(UnaryOp::Try),
                            Rule::Call => {
                                Ok(UnaryOp::Call(Call::from_pest(&mut Pairs::single(op))?))
                            }
                            _ => Err(ConversionError::NoMatch),
                        }?,
                        expr: box l?,
                    })
                })
                .map_infix(|l, op, r| {
                    Ok(Expr::Binary {
                        lhs: box l?,
                        op: match op.as_rule() {
                            Rule::Add => Ok(BinaryOp::Add),
                            Rule::Sub => Ok(BinaryOp::Sub),
                            Rule::Mul => Ok(BinaryOp::Mul),
                            Rule::Div => Ok(BinaryOp::Div),
                            _ => Err(ConversionError::NoMatch),
                        }?,
                        rhs: box r?,
                    })
                })
                .parse(pest)
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    use ast::ParseTree;
    use from_pest::FromPest;
    use pest::Parser;
    use std::fs;

    let source = String::from_utf8(fs::read("./examples/expr.txt")?)?;
    println!("source = {}", source);
    let mut token_tree = parser::Parser::parse(parser::Rule::TokenTree, &source)?;
    println!("token tree = {:#?}", token_tree);
    let parse_tree = ParseTree::from_pest(&mut token_tree).expect("infallible");
    println!("syntax tree = {:#?}", parse_tree);

    Ok(())
}

#[test]
fn expr_example_runs() {
    main().unwrap()
}
