use std::rc::Rc;

use crate::lisp::*;

pub fn eval(env: &Env, x: Rc<Expr>) -> Result<Rc<Expr>> {
    match x.as_ref() {
        Expr::Cons(car, cdr) => apply(env, car.clone(), cdr.clone()),
        Expr::Symbol(_) if x == nil() || x == t() => Ok(x),
        Expr::Symbol(_) => env
            .get(&x)
            .cloned()
            .ok_or_else(|| Error(format!("symbol not found: {}", x))),
        Expr::Number(_) => Ok(x),
        Expr::Function(_) => Ok(x),
    }
}

pub fn evlis(env: &Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    if xs == nil() {
        Ok(xs)
    } else {
        Ok(cons(eval(env, car(xs.clone())?)?, evlis(env, cdr(xs)?)?))
    }
}

fn evcon(env: &Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    // (cond ((eq x y) 'ok) (t 'ng))
    if xs == nil() {
        Ok(xs)
    } else {
        let x = car(xs.clone())?;
        if eval(env, car(x.clone())?)? != nil() {
            eval(env, car(cdr(x)?)?)
        } else {
            evcon(env, cdr(xs)?)
        }
    }
}

fn evlet(env: &Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    // (let ((x 1) (y 2)) (cons x y))
    let mut new_env = env.clone();
    for x in iter(car(xs.clone())?) {
        let x = x?;
        new_env.insert(
            car(x.clone())?,
            eval(env, car(cdr(x)?)?)?,
        );
    }
    eval(&new_env, car(cdr(xs)?)?)
}

fn number_op(f: impl FnOnce(i64, i64) -> i64, args: Rc<Expr>) -> Result<Rc<Expr>> {
    match (car(args.clone())?.as_ref(), car(cdr(args)?)?.as_ref()) {
        (Expr::Number(x), Expr::Number(y)) => Ok(number(f(*x, *y))),
        (x, y) => Err(Error(format!("invalid number: {}, {}", x, y))),
    }
}

fn number_cmp(f: impl FnOnce(i64, i64) -> bool, args: Rc<Expr>) -> Result<Rc<Expr>> {
    match (car(args.clone())?.as_ref(), car(cdr(args)?)?.as_ref()) {
        (Expr::Number(x), Expr::Number(y)) => Ok(bool_to_expr(f(*x, *y))),
        (x, y) => Err(Error(format!("invalid number: {}, {}", x, y))),
    }
}

pub fn apply(env: &Env, func: Rc<Expr>, args: Rc<Expr>) -> Result<Rc<Expr>> {
    match func.as_ref() {
        Expr::Symbol(fname) => {
            let res = match fname.as_str() {
                "cons" => cons(eval(env, car(args.clone())?)?, eval(env, car(cdr(args)?)?)?),
                "car" => car(eval(env, car(args)?)?)?,
                "cdr" => cdr(eval(env, car(args)?)?)?,
                "quote" => car(args)?,
                "atom" => bool_to_expr(atom(car(args)?)),
                "eq" => bool_to_expr(eq(
                    eval(env, car(args.clone())?)?,
                    eval(env, car(cdr(args)?)?)?,
                )),
                "cond" => evcon(env, args)?,
                "let" => evlet(env, args)?,
                "lambda" => function(Function::new(env, car(args.clone())?, cdr(args.clone())?)),
                "+" => number_op(|x, y| x + y, evlis(env, args)?)?,
                "-" => number_op(|x, y| x - y, evlis(env, args)?)?,
                "*" => number_op(|x, y| x * y, evlis(env, args)?)?,
                "/" => number_op(|x, y| x / y, evlis(env, args)?)?,
                "<" => number_cmp(|x, y| x < y, evlis(env, args)?)?,
                "<=" => number_cmp(|x, y| x <= y, evlis(env, args)?)?,
                ">" => number_cmp(|x, y| x > y, evlis(env, args)?)?,
                ">=" => number_cmp(|x, y| x >= y, evlis(env, args)?)?,
                _ => apply(env, eval(env, func)?, evlis(env, args)?)?,
            };
            Ok(res)
        }
        Expr::Cons(_, _) => apply(env, eval(env, func)?, args),
        Expr::Function(function) => function.apply(env, args),
        _ => Err(Error(format!("invalid function: {}", func))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader;

    fn assert_eval(env: &Env, sexpr: &str, expr: Rc<Expr>) {
        let input = reader::Reader::new(sexpr.bytes()).read().unwrap().unwrap();
        dbg!(input.clone());
        assert_eq!(eval(env, input).unwrap(), expr);
    }

    #[test]
    fn test_eval_number() {
        assert_eval(&Env::new(), "10", number(10));
    }

    #[test]
    fn test_eval_nil() {
        assert_eval(&Env::new(), "nil", nil());
    }

    #[test]
    fn test_eval_t() {
        assert_eval(&Env::new(), "t", t());
    }

    #[test]
    fn test_eval_cons() {
        assert_eval(&Env::new(), "(cons 1 2)", cons(number(1), number(2)));
    }

    #[test]
    fn test_eval_eq() {
        assert_eval(&Env::new(), "(eq 10 10)", t());

        let mut env = Env::new();
        env.insert(symbol("x"), number(10));
        assert_eval(&env, "(eq x 10)", t());
    }

    #[test]
    fn test_eval_lambda() {
        assert_eval(
            &Env::new(),
            "((lambda (a b) (cons a b)) 1 2)",
            cons(number(1), number(2)),
        );
        assert_eval(
            &Env::new(),
            "((lambda (a) ((lambda (b) b) a)) 'x)",
            symbol("x"),
        );
    }

    #[test]
    fn test_eval_let() {
        assert_eval(
            &Env::new(),
            "(let ((a 1) (b 2)) (cons 1 2))",
            cons(number(1), number(2)),
        );
    }

    #[test]
    fn test_eval_cond() {
        assert_eval(
            &Env::new(),
            "(let ((x 10)) (cond ((eq x 1) 'ng) ((eq x 10) 'ok) (t nil)))",
            symbol("ok"),
        );
    }

    #[test]
    fn test_eval_closure() {
        assert_eval(
            &Env::new(),
            "(let ((f (let ((x 1)) (lambda (y) (+ x y))))) (f 10))",
            number(11),
        );
        assert_eval(
            &Env::new(),
            "((let ((x 1)) (lambda (y) (+ x y))) 10)",
            number(11),
        );
    }

    #[test]
    fn test_eval_fib() {
        assert_eval(
            &Env::new(),
            r"
(let ((fib (lambda (fib n)
             (cond ((< n 2) n)
                   (t (+ (fib fib (- n 1)) (fib fib (- n 2))))))))
  (fib fib 10))
",
            number(55),
        );
    }
}
