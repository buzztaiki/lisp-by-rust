use std::rc::Rc;

use crate::env::Env;
use crate::lisp::*;

pub fn eval(env: &mut Env, x: &Expr) -> Result<Rc<Expr>> {
    match x {
        Expr::Cons(func, args) => match &*get_function(env, func)? {
            FunctionExpr::SpecialForm(x) => x.apply(env, args),
            FunctionExpr::Function(x) => {
                let evargs = evlis(env, args)?;
                x.apply(env, &evargs)
            }
            FunctionExpr::Macro(x) => {
                let body = x.apply(env, args)?;
                eval(env, &body)
            }
        },
        Expr::Symbol(_) => env
            .get(x)
            .ok_or_else(|| Error(format!("unbound variable: {}", x))),
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

pub fn bind_args(env: &mut Env, names: &Expr, values: &Expr) -> Result<()> {
    for (k, v) in names.iter().zip(values.iter()) {
        env.insert(k?, v?);
    }
    Ok(())
}

pub fn eval_body(env: &mut Env, body: &Expr) -> Result<Rc<Expr>> {
    body.iter()
        .try_fold(nil(), |_, x| x.and_then(|x| eval(env, &x)))
}

pub fn get_function(env: &mut Env, func: &Expr) -> Result<Rc<FunctionExpr>> {
    match func {
        Expr::Symbol(_) => match env.get_function(func) {
            Some(x) => get_function(env, &x),
            None => Err(Error(format!("unbound function: {}", func))),
        },
        Expr::Cons(x, args) if x.to_string() == "lambda" => {
            let f = lambda(env, args.car()?, args.cdr()?);
            get_function(env, &f)
        }
        Expr::Function(x) => Ok(x.clone()),
        _ => Err(Error(format!("invalid function: {}", func))),
    }
}

pub fn global_env() -> Env {
    let mut env = Env::new();
    env.insert_global(nil(), nil());
    env.insert_global(t(), t());
    env
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader;

    fn assert_eval_with_env(env: &mut Env, sexpr: &str, expr: Rc<Expr>) {
        let r = reader::Reader::new(sexpr.bytes());
        let output = r.fold(nil(), |_, x| eval(env, &x.unwrap()).unwrap());
        assert_eq!(output, expr);
    }

    fn assert_eval(sexpr: &str, expr: Rc<Expr>) {
        assert_eval_with_env(&mut global_env(), sexpr, expr);
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
    fn test_eval_body() {
        let env = &mut global_env();
        let body = list(&[number(1), number(2)]);
        assert_eq!(eval_body(env, &body).unwrap(), number(2));
    }
}
