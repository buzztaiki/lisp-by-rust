use std::io::stdin;

mod env;
mod eval;
mod lisp;
mod reader;
mod repl;

fn main() -> lisp::Result<()> {
    repl::repl(env::Env::new(), stdin())
}
