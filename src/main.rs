use std::io::stdin;

mod eval;
mod lisp;
mod reader;
mod repl;

fn main() -> lisp::Result<()> {
    repl::repl(lisp::Env::new(), stdin())
}
