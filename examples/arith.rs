#[macro_use]
extern crate pest_derive;
extern crate from_pest;
#[macro_use]
extern crate pest_ast;
extern crate pest;

use pest::Parser;

#[derive(Parser)]
#[grammar = "../examples/arith.pest"]
pub struct TokenTree;

#[derive(Debug, FromPest)]
pub struct SyntaxTree<'i>(Expr<'i>, EOI);

#[derive(Debug, FromPest)]
pub struct EOI;

fn span_into_str(span: pest::Span) -> &str {
    span.as_str()
}

#[derive(Debug, FromPest)]
#[pest_ast(expr)]
pub enum Expr<'i> {
    #[pest_ast(primary)]
    Primary(Primary<'i>),

    #[pest_ast(infix)]
    Infix(Box<Expr<'i>>, InfixOp, Box<Expr<'i>>),

    #[pest_ast(prefix)]
    Prefix(PrefixOp, Box<Expr<'i>>),

    #[pest_ast(postfix)]
    Postfix(Box<Expr<'i>>, PostfixOp),
}

#[derive(Debug, FromPest)]
pub enum Primary<'i> {
    Term(Term<'i>),
}

#[derive(Debug, FromPest)]
pub struct Term<'i> {
    #[pest_ast(outer(with(span_into_str)))]
    val: &'i str,
}

#[derive(Debug, FromPest)]
#[pest_ast(infix)]
pub enum InfixOp {
    #[pest_ast(precedence = 1, associativity = "left")]
    Add,
    #[pest_ast(precedence = 2, associativity = "left")]
    Mul,
}

#[derive(Debug, FromPest)]
#[pest_ast(prefix)]
pub enum PrefixOp {
    #[pest_ast(precedence = 3)]
    Not,
    #[pest_ast(precedence = 3)]
    Neg,
}

#[derive(Debug, FromPest)]
#[pest_ast(postfix)]
pub enum PostfixOp {
    #[pest_ast(precedence = 4)]
    Try,
}

fn main() {
    use from_pest::FromPest;
    use pest::Parser;

    let source = "!a?+!b?";

    let mut token_tree = TokenTree::parse(Rule::SyntaxTree, source).expect("parse success");
    println!("token tree = {:#?}", token_tree);

    let syntax_tree = SyntaxTree::from_pest(&mut token_tree);
    println!("syntax tree = {:#?}", syntax_tree);
}


