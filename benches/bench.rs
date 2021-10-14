#![feature(test)]

// how to execute: cargo +nightly bench

extern crate test;
use lib::env::Env;
use lib::eval;
use lib::lisp::Expr;
use lib::reader::Reader;
use std::rc::Rc;
use test::black_box;

fn read(x: &str) -> Rc<Expr> {
    Reader::new(x.bytes()).read().unwrap().unwrap()
}

fn define_fib(env: &mut Env) {
    let defun = r"
(defun fib (n)
  (cond ((< n 2) n)
        (t (+ (fib (- n 1)) (fib (- n 2))))))
";
    eval::eval(env, &read(defun)).unwrap();
}

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

#[bench]
fn bench_lisp_fib10(b: &mut test::Bencher) {
    let mut env = eval::global_env();
    define_fib(&mut env);

    let expr = read("(fib 10)");
    b.iter(|| eval::eval(&mut env, &expr).unwrap());
}

#[bench]
fn bench_lisp_fib20(b: &mut test::Bencher) {
    let mut env = eval::global_env();
    define_fib(&mut env);

    let expr = read("(fib 20)");
    b.iter(|| eval::eval(&mut env, &expr).unwrap())
}

#[bench]
fn bench_rust_fib10(b: &mut test::Bencher) {
    b.iter(|| fibonacci(black_box(10)));
}

#[bench]
fn bench_rust_fib20(b: &mut test::Bencher) {
    b.iter(|| fibonacci(black_box(20)));
}
