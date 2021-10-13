use std::io::stdin;

mod eval;
mod lisp;
mod reader;
mod repl;
mod env;

fn main() -> lisp::Result<()> {
    repl::repl(env::Env::new(), stdin())
}
