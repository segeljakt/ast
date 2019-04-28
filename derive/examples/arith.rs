use pest_derive;
use pest_derive::Parser;
use from_pest;
use pest_ast;
use pest;

use pest::Parser;

#[derive(Parser)]
#[grammar = "../examples/from-pair.pest"]
pub struct TokenTreeParser;

#[derive(Debug, FromPest)]
struct Program<'i>(Expr<'i>);

#[derive(Debug, FromPest)]
#[pest(expr)]
enum Expr<'i> {
    #[pest(primary)]
    Primary(Primary<'i>),

    #[pest(infix)]
    Infix(Box<Expr<'i>>, InfixOp, Box<Expr<'i>>),

    #[pest(prefix)]
    Prefix(PrefixOp, Box<Expr<'i>>),

    #[pest(postfix)]
    Postfix(Box<Expr<'i>>, PostfixOp),
}

#[derive(Debug, FromPest)]
enum Primary<'i> {
    Term(Term<'i>),
}

#[derive(Debug, FromPest)]
struct Term<'i> {
    #[pest(text)]
    val: &'i str,
}

#[derive(Debug, FromPest)]
#[pest(infix)]
enum InfixOp {
    #[pest(precedence = 1, associativity = "left")]
    Add,
    #[pest(precedence = 2, associativity = "left")]
    Mul,
}

#[derive(Debug, FromPest)]
#[pest(prefix)]
enum PrefixOp {
    #[pest(precedence = 3)]
    Not,
    #[pest(precedence = 3)]
    Neg,
}

#[derive(Debug, FromPest)]
#[pest(postfix)]
enum PostfixOp {
    #[pest(precedence = 4)]
    Try,
}

fn main() {
    let source = "!a?+!b?";

    let mut token_tree = TokenTreeParser::parse(Rule::Program, source).expect("parse success");
    println!("parse tree = {:#?}", token_tree);

    let parse_tree = Program::from_pairs(token_tree);
    println!("syntax tree = {:#?}", parse_tree);
}

