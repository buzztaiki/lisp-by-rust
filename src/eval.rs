use std::rc::Rc;

use crate::env::Env;
use crate::lisp::*;

pub fn eval(env: &mut Env, x: &Expr) -> Result<Rc<Expr>> {
    match x {
        Expr::Cons(car, cdr) => apply(env, car, cdr),
        Expr::Symbol(_) => env
            .get(x)
            .ok_or_else(|| Error(format!("symbol not found: {}", x))),
        Expr::Number(v) => Ok(number(*v)),
        Expr::Function(f) => Ok(function(f.clone())),
    }
}

pub fn evlis(env: &mut Env, xs: &Expr) -> Result<Rc<Expr>> {
    if xs.is_nil() {
        Ok(nil())
    } else {
        Ok(cons(eval(env, &*xs.car()?)?, evlis(env, &*xs.cdr()?)?))
    }
}

fn evcon(env: &mut Env, xs: &Expr) -> Result<Rc<Expr>> {
    // (cond ((eq x y) 'ok) (t 'ng))
    if xs.is_nil() {
        Ok(nil())
    } else {
        let x = xs.car()?;
        if !eval(env, &*x.car()?)?.is_nil() {
            eval(env, &*x.cadr()?)
        } else {
            evcon(env, &*xs.cdr()?)
        }
    }
}

fn evlet(env: &mut Env, xs: &Expr) -> Result<Rc<Expr>> {
    // (let ((x 1) (y 2)) (cons x y))
    let mut new_env = env.new_scope();
    for x in xs.car()?.iter() {
        let x = x?;
        new_env.insert(x.car()?, eval(env, &*x.cadr()?)?);
    }
    eval(&mut new_env, &*xs.cadr()?)
}

fn evlambda(env: &Env, xs: &Expr) -> Result<Rc<Expr>> {
    // (lambda (x y) (cons x y))
    let f = function(FunctionExpr::function(
        env.new_scope(),
        xs.car()?,
        xs.cdr()?,
    ));
    Ok(f)
}

fn evdefun(env: &mut Env, xs: &Expr) -> Result<Rc<Expr>> {
    // (defun f (x y) (cons x y))
    let name = xs.car()?;
    let f = evlambda(env, &*xs.cdr()?)?;
    env.insert(name, f.clone());
    Ok(f)
}

fn map_number(xs: Rc<Expr>) -> impl Iterator<Item = Result<i64>> {
    xs.iter().map(|x| {
        x.and_then(|x| match &*x {
            Expr::Number(x) => Ok(*x),
            _ => Err(Error(format!("invalid number: {}", x))),
        })
    })
}

fn ev_number_op(
    env: &mut Env,
    f: impl Fn(i64, i64) -> i64,
    init: i64,
    xs: &Expr,
) -> Result<Rc<Expr>> {
    let xs = map_number(evlis(env, xs)?);
    let res = xs.reduce(|a, b| a.and_then(|a| b.map(|b| f(a, b))));
    res.unwrap_or(Ok(init)).map(number)
}

fn ev_number_cmp(env: &mut Env, f: impl Fn(i64, i64) -> bool, xs: &Expr) -> Result<Rc<Expr>> {
    let mut xs = map_number(evlis(env, xs)?);
    let x = xs
        .next()
        .unwrap_or_else(|| Err(Error("wrong number of argument".to_string())));
    let res = xs.try_fold(x, |a, b| {
        a.and_then(|a| b.map(|b| f(a, b).then(|| b))).transpose()
    });
    res.transpose().map(|x| Expr::from_bool(x.is_some()))
}

pub fn apply(env: &mut Env, func: &Expr, args: &Expr) -> Result<Rc<Expr>> {
    match func {
        Expr::Symbol(fname) => {
            let res = match fname.as_str() {
                "cons" => cons(eval(env, &*args.car()?)?, eval(env, &*args.cadr()?)?),
                "car" => eval(env, &*args.car()?)?.car()?,
                "cdr" => eval(env, &*args.car()?)?.cdr()?,
                "quote" => args.car()?,
                "atom" => Expr::from_bool(args.car()?.is_atom()),
                "eq" => {
                    Expr::from_bool(eval(env, &*args.car()?)?.lisp_eq(&*eval(env, &*args.cadr()?)?))
                }
                "cond" => evcon(env, args)?,
                "let" => evlet(env, args)?,
                "lambda" => evlambda(env, args)?,
                "defun" => evdefun(env, args)?,
                "+" => ev_number_op(env, |a, b| a + b, 0, args)?,
                "-" => ev_number_op(env, |a, b| a - b, 0, args)?,
                "*" => ev_number_op(env, |a, b| a * b, 1, args)?,
                "/" => ev_number_op(env, |a, b| a / b, 0, args)?,
                "<" => ev_number_cmp(env, |a, b| a < b, args)?,
                ">" => ev_number_cmp(env, |a, b| a > b, args)?,
                "<=" => ev_number_cmp(env, |a, b| a <= b, args)?,
                ">=" => ev_number_cmp(env, |a, b| a >= b, args)?,
                _ => {
                    let args = evlis(env, args)?;
                    let func = eval(env, func)?;
                    apply(env, &func, &args)?
                }
            };
            Ok(res)
        }
        Expr::Cons(_, _) => {
            let func = eval(env, func)?;
            apply(env, &func, args)
        }
        Expr::Function(function) => function.apply(env, args),
        _ => Err(Error(format!("invalid function: {}", func))),
    }
}

pub fn global_env() -> Env {
    let mut env = Env::new();
    env.insert(nil(), nil());
    env.insert(t(), t());
    env
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader;

    fn assert_eval_with_env(mut env: Env, sexpr: &str, expr: Rc<Expr>) {
        let mut r = reader::Reader::new(sexpr.bytes());
        let mut output = nil();
        while let Some(x) = r.read().unwrap() {
            output = eval(&mut env, &x).unwrap();
        }
        assert_eq!(output, expr);
    }

    fn assert_eval(sexpr: &str, expr: Rc<Expr>) {
        assert_eval_with_env(global_env(), sexpr, expr);
    }

    #[test]
    fn test_eval_number() {
        assert_eval("10", number(10));
    }

    #[test]
    fn test_eval_nil() {
        assert_eval("nil", nil());
    }

    #[test]
    fn test_eval_t() {
        assert_eval("t", t());
    }

    #[test]
    fn test_eval_cons() {
        assert_eval("(cons 1 2)", cons(number(1), number(2)));
    }

    #[test]
    fn test_eval_eq() {
        assert_eval("(eq 10 10)", t());

        let mut env = global_env();
        env.insert(symbol("x"), number(10));
        assert_eval_with_env(env, "(eq x 10)", t());
    }

    #[test]
    fn test_eval_lambda() {
        assert_eval(
            "((lambda (a b) (cons a b)) 1 2)",
            cons(number(1), number(2)),
        );
        assert_eval("((lambda (a) ((lambda (b) b) a)) 'x)", symbol("x"));
    }

    #[test]
    fn test_eval_let() {
        assert_eval("(let ((a 1) (b 2)) (cons 1 2))", cons(number(1), number(2)));
    }

    #[test]
    fn test_eval_cond() {
        assert_eval(
            "(let ((x 10)) (cond ((eq x 1) 'ng) ((eq x 10) 'ok) (t nil)))",
            symbol("ok"),
        );
    }

    #[test]
    fn test_eval_closure() {
        assert_eval(
            "(let ((f (let ((x 1)) (lambda (y) (+ x y))))) (f 10))",
            number(11),
        );
        assert_eval("((let ((x 1)) (lambda (y) (+ x y))) 10)", number(11));
    }

    #[test]
    #[should_panic(expected = "symbol not found: y")]
    fn test_eval_closure_uncaptured() {
        assert_eval(
            "(let ((f (let ((x 1)) (lambda () (+ x y))))) (let ((y 10)) (f 10)))",
            number(11),
        );
    }

    #[test]
    fn test_eval_defun() {
        assert_eval(
            r"
(defun fib (n)
  (cond ((< n 2) n)
        (t (+ (fib (- n 1)) (fib (- n 2))))))
(fib 10)
",
            number(55),
        );
    }
}
