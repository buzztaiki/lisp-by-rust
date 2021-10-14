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

pub fn apply(env: &mut Env, func: &Expr, args: &Expr) -> Result<Rc<Expr>> {
    match func {
        Expr::Symbol(_) => {
            let func = eval(env, func)?;
            apply(env, &func, args)
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
}
