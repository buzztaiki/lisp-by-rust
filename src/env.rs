use std::collections::HashMap;
use std::rc::Rc;

use crate::lisp::Expr;

#[derive(Debug)]
pub struct Env {
    global: Scope,
    stack: Vec<Scope>,
}

type Scope = HashMap<Rc<Expr>, Rc<Expr>>;

impl Env {
    pub fn new() -> Self {
        Self {
            global: Scope::new(),
            stack: Vec::new(),
        }
    }

    pub fn insert(&mut self, k: Rc<Expr>, v: Rc<Expr>) {
        if let Some(scope) = self.stack.last_mut() {
            scope.insert(k, v);
        } else {
            self.global.insert(k, v);
        }
    }

    pub fn extend(&mut self, iter: impl Iterator<Item = (Rc<Expr>, Rc<Expr>)>) {
        if let Some(scope) = self.stack.last_mut() {
            scope.extend(iter);
        } else {
            self.global.extend(iter);
        }
    }

    pub fn insert_global(&mut self, k: Rc<Expr>, v: Rc<Expr>) {
        self.global.insert(k, v);
    }

    pub fn get(&self, k: &Expr) -> Option<Rc<Expr>> {
        let x = self
            .stack
            .last()
            .and_then(|scope| scope.get(k))
            .or_else(|| self.global.get(k));
        x.cloned()
    }

    pub fn enter_scope(&mut self) {
        self.stack.push(Scope::new());
    }

    pub fn exit_scope(&mut self) {
        self.stack.pop();
    }

    pub fn capture(&self) -> Vec<(Rc<Expr>, Rc<Expr>)> {
        self.stack
            .last()
            .iter()
            .flat_map(|x| x.iter())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lisp::number;

    #[test]
    fn test() {
        let mut env = Env::new();
        env.insert(number(10), number(20));
        assert_eq!(env.get(&number(10)), Some(number(20)));

        env.enter_scope();
        assert_eq!(env.get(&number(10)), Some(number(20)));

        env.insert(number(10), number(30));
        env.insert(number(20), number(40));
        assert_eq!(env.get(&number(10)), Some(number(30)));
        assert_eq!(env.get(&number(20)), Some(number(40)));

        env.exit_scope();
        assert_eq!(env.get(&number(10)), Some(number(20)));
        assert_eq!(env.get(&number(20)), None);
    }
}
