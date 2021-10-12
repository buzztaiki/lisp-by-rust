use std::io::stdin;

mod lisp;

fn main() -> lisp::Result<()> {
    lisp::repl(lisp::Env::new(), stdin())
}
