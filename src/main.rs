use std::env::args;
use std::fs::File;
use std::io::stdin;

mod env;
mod eval;
mod lisp;
mod reader;
mod repl;

fn main() -> lisp::Result<()> {
    if let Some(fname) = args().skip(1).next() {
        let f = File::open(fname).map_err(|e| lisp::Error(e.to_string()))?;
        repl::repl(env::Env::new(), f)
    } else {
        repl::repl(env::Env::new(), stdin())
    }
}
