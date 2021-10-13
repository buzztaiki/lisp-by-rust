use std::rc::Rc;

use crate::lisp::*;

pub fn eval(env: &mut Env, x: Rc<Expr>) -> Result<Rc<Expr>> {
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

pub fn evlis(env: &mut Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    if xs == nil() {
        Ok(xs)
    } else {
        Ok(cons(eval(env, car(xs.clone())?)?, evlis(env, cdr(xs)?)?))
    }
}

fn evcon(env: &mut Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
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

fn evlet(env: &mut Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    // (let ((x 1) (y 2)) (cons x y))
    let mut new_env = env.clone();
    for x in iter(car(xs.clone())?) {
        let x = x?;
        new_env.insert(car(x.clone())?, eval(env, car(cdr(x)?)?)?);
    }
    eval(&mut new_env, car(cdr(xs)?)?)
}

fn evdefun(env: &mut Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    // (defun f (x y) (cons x y))
    let f = function(Function::new(
        env,
        car(cdr(xs.clone())?)?,
        cdr(cdr(xs.clone())?)?,
    ));
    let name = car(xs.clone())?;
    env.insert(name, f.clone());
    Ok(f)
}

fn map_number(x: Rc<Expr>) -> Result<i64> {
    match x.as_ref() {
        Expr::Number(x) => Ok(*x),
        _ => Err(Error(format!("invalid number: {}", x))),
    }
}

fn ev_number_op(
    env: &mut Env,
    f: impl Fn(i64, i64) -> i64,
    init: i64,
    xs: Rc<Expr>,
) -> Result<Rc<Expr>> {
    let xs = iter(evlis(env, xs)?)
        .map(|x| x.and_then(map_number))
        .collect::<Result<Vec<_>>>()?;
    Ok(number(xs.iter().copied().reduce(f).unwrap_or(init)))
}

fn ev_number_cmp(env: &mut Env, f: impl Fn(i64, i64) -> bool, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    let xs = iter(evlis(env, xs)?)
        .map(|x| x.and_then(map_number))
        .collect::<Result<Vec<_>>>()?;
    Ok(bool_to_expr(xs.windows(2).all(|x| f(x[0], x[1]))))
}

pub fn apply(env: &mut Env, func: Rc<Expr>, args: Rc<Expr>) -> Result<Rc<Expr>> {
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
                    apply(env, func, args)?
                }
            };
            Ok(res)
        }
        Expr::Cons(_, _) => {
            let func = eval(env, func)?;
            apply(env, func, args)
        }
        Expr::Function(function) => function.apply(env, args),
        _ => Err(Error(format!("invalid function: {}", func))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader;

    fn assert_eval_with_env(mut env: Env, sexpr: &str, expr: Rc<Expr>) {
        let mut r = reader::Reader::new(sexpr.bytes());
        let mut output = nil();
        while let Some(x) = r.read().unwrap() {
            output = eval(&mut env, x).unwrap();
        }
        assert_eq!(output, expr);
    }

    fn assert_eval(sexpr: &str, expr: Rc<Expr>) {
        assert_eval_with_env(Env::new(), sexpr, expr);
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

        let mut env = Env::new();
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
