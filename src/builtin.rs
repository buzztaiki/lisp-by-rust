use std::rc::Rc;

use crate::env::Env;
use crate::eval::{self, eval, eval_body, evlis};
use crate::lisp::{
    self, function, nil, number, symbol, BuiltinFn, Error, Expr, FunctionExpr, Result,
};

fn cons(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    Ok(lisp::cons(
        eval(env, &*args.car()?)?,
        eval(env, &*args.cadr()?)?,
    ))
}

fn list(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    eval::evlis(env, args)
}

fn car(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    eval(env, &*args.car()?)?.car()
}

fn cdr(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    eval(env, &*args.car()?)?.cdr()
}

fn quote(_env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    args.car()
}

fn atom(_env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    Ok(Expr::from_bool(args.car()?.is_atom()))
}

fn eq(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    Ok(Expr::from_bool(
        eval(env, &*args.car()?)?.lisp_eq(&*eval(env, &*args.cadr()?)?),
    ))
}

fn cond(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    // (cond ((eq x y) 'ok) (t 'ng))
    if args.is_nil() {
        Ok(nil())
    } else {
        let x = args.car()?;
        if !eval(env, &*x.car()?)?.is_nil() {
            eval_body(env, &*x.cdr()?)
        } else {
            cond(env, &*args.cdr()?)
        }
    }
}

fn lisp_let(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    // (let ((x 1) (y 2)) (cons x y))
    let mut vars = env.capture();
    for x in args.car()?.iter() {
        let (car, cdr) = x?.pair()?;
        vars.push((car, eval(env, &*cdr.car()?)?));
    }

    let scope = &mut env.enter_scope();
    scope.extend(vars.into_iter());
    eval_body(scope, &*args.cdr()?)
}

fn lambda(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    // (lambda (x y) (cons x y))
    let f = function(FunctionExpr::function(
        env,
        "lambda",
        args.car()?,
        args.cdr()?,
    ));
    Ok(f)
}

fn defun(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    // (defun f (x y) (cons x y))
    let name = args.car()?;
    let args = args.cdr()?;
    let f = function(FunctionExpr::function(
        env,
        &name.to_string(),
        args.car()?,
        args.cdr()?,
    ));
    env.insert_function(name, f.clone());
    Ok(f)
}

fn defmacro(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    // (defmacro f (x y) (cons x y))
    let name = args.car()?;
    let args = args.cdr()?;
    let f = function(FunctionExpr::macro_form(
        env,
        &name.to_string(),
        args.car()?,
        args.cdr()?,
    ));
    env.insert_function(name, f.clone());
    Ok(f)
}

fn map_number(args: &Expr) -> impl Iterator<Item = Result<i64>> + '_ {
    args.iter().map(|x| {
        x.and_then(|x| match &*x {
            Expr::Number(x) => Ok(*x),
            _ => Err(Error(format!("invalid number: {}", x))),
        })
    })
}

fn number_op(
    env: &mut Env,
    args: &Expr,
    f: impl Fn(i64, i64) -> i64,
    init: i64,
) -> Result<Rc<Expr>> {
    let evargs = evlis(env, args)?;
    let args = map_number(&evargs);
    let res = args.reduce(|a, b| a.and_then(|a| b.map(|b| f(a, b))));
    res.unwrap_or(Ok(init)).map(number)
}

fn number_cmp(env: &mut Env, args: &Expr, f: impl Fn(i64, i64) -> bool) -> Result<Rc<Expr>> {
    let evargs = evlis(env, args)?;
    let mut args = map_number(&evargs);
    let x = args
        .next()
        .unwrap_or_else(|| Err(Error("wrong number of argument".to_string())));
    let res = args.try_fold(x, |a, b| {
        a.and_then(|a| b.map(|b| f(a, b).then(|| b))).transpose()
    });
    res.transpose().map(|x| Expr::from_bool(x.is_some()))
}

macro_rules! def_number_op {
    ($func_name:ident, $op:tt, $init:expr) => {
        fn $func_name(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
            number_op(env, args, |a, b| a $op b, $init)
        }
    };
}

macro_rules! def_number_cmp {
    ($func_name:ident, $op:tt) => {
        fn $func_name(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
            number_cmp(env, args, |a, b| a $op b)
        }
    };
}

def_number_op!(add, +, 0);
def_number_op!(sub, -, 0);
def_number_op!(mul, *, 1);
def_number_op!(div, /, 1);

def_number_cmp!(lt, <);
def_number_cmp!(gt, >);
def_number_cmp!(le, <=);
def_number_cmp!(ge, >=);

fn prin1(env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
    let x = eval(env, &*args.car()?)?;
    print!("{}", x);
    Ok(x)
}

fn terpri(_env: &mut Env, _args: &Expr) -> Result<Rc<Expr>> {
    println!();
    Ok(lisp::t())
}

pub fn global_env() -> Env {
    let builtins: Vec<(&str, BuiltinFn)> = vec![
        ("cons", cons),
        ("list", list),
        ("car", car),
        ("cdr", cdr),
        ("quote", quote),
        ("atom", atom),
        ("eq", eq),
        ("cond", cond),
        ("let", lisp_let),
        ("lambda", lambda),
        ("defun", defun),
        ("defmacro", defmacro),
        ("+", add),
        ("-", sub),
        ("*", mul),
        ("/", div),
        ("<", lt),
        (">", gt),
        ("<=", le),
        (">=", ge),
        ("prin1", prin1),
        ("terpri", terpri),
    ];

    let mut env = eval::global_env();
    for (k, v) in builtins {
        env.insert_function(symbol(k), function(FunctionExpr::builtin(k, v)));
    }
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
    fn test_eval_cons() {
        assert_eval("(let ((x 2)) (cons 1 x))", lisp::cons(number(1), number(2)));
    }

    #[test]
    fn test_eval_list() {
        assert_eval(
            "(let ((x 2)) (list 1 x))",
            lisp::list(&[number(1), number(2)]),
        );
    }

    #[test]
    fn test_eval_eq() {
        assert_eval("(eq 10 10)", lisp::t());

        let env = &mut global_env();
        env.insert(symbol("x"), number(10));
        assert_eval_with_env(env, "(eq x 10)", lisp::t());
    }

    #[test]
    fn test_eval_lambda() {
        assert_eval(
            "((lambda (a b) (cons a b)) 1 2)",
            lisp::cons(number(1), number(2)),
        );
        assert_eval("((lambda (a) ((lambda (b) b) a)) 'x)", symbol("x"));
        assert_eval("((lambda (f x) (f x x)) + 1)", number(2));
    }

    #[test]
    fn test_eval_let() {
        assert_eval(
            "(let ((a 1) (b 2)) (cons 1 2))",
            lisp::cons(number(1), number(2)),
        );
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
    #[should_panic(expected = "unbound variable: y")]
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

    #[test]
    fn test_eval_defun_in_closure() {
        assert_eval(
            r"
(let ((x 1)) (defun f (y) (+ x y)))
(f 2)
",
            number(3),
        );
    }

    #[test]
    fn test_eval_defmacro() {
        let env = &mut global_env();
        assert_eval_with_env(
            env,
            "(defmacro myand (a b) (list 'cond (list a b))) t",
            lisp::t(),
        );
        assert_eval_with_env(env, "(myand 'moo 'woo)", symbol("woo"));
        assert_eval_with_env(env, "(myand nil 'woo)", nil());
        assert_eval_with_env(env, "(myand 'moo nil)", nil());
    }

    #[test]
    fn test_eval_defmacro_in_closure() {
        assert_eval(
            r"
(let ((x 1)) (defmacro m () (list '+ x 'x)))
(let ((x 2)) (m))
",
            number(3),
        );
    }
}
