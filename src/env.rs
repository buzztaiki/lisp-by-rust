use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use crate::lisp::Expr;

#[derive(Debug, Default)]
pub struct Env {
    global: Map,
    function: Map,
    stack: Vec<Map>,
}

type Map = HashMap<Rc<Expr>, Rc<Expr>>;

pub struct Scope<'a> {
    env: &'a mut Env,
}

impl<'a> Scope<'a> {
    pub fn env(&self) -> &Env {
        self.env
    }

    pub fn env_mut(&mut self) -> &mut Env {
        self.env
    }
}

impl<'a> Drop for Scope<'a> {
    fn drop(&mut self) {
        self.env.exit_scope();
    }
}

impl<'a> Deref for Scope<'a> {
    type Target = Env;

    fn deref(&self) -> &Self::Target {
        self.env
    }
}

impl<'a> DerefMut for Scope<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.env
    }
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, k: Rc<Expr>, v: Rc<Expr>) {
        let map = self.stack.last_mut().unwrap_or(&mut self.global);
        map.insert(k, v);
    }

    pub fn extend(&mut self, iter: impl Iterator<Item = (Rc<Expr>, Rc<Expr>)>) {
        let map = self.stack.last_mut().unwrap_or(&mut self.global);
        map.extend(iter);
    }

    pub fn insert_global(&mut self, k: Rc<Expr>, v: Rc<Expr>) {
        self.global.insert(k, v);
    }

    pub fn insert_function(&mut self, k: Rc<Expr>, v: Rc<Expr>) {
        self.function.insert(k, v);
    }

    pub fn get(&self, k: &Expr) -> Option<Rc<Expr>> {
        let value = self.stack.last().and_then(|map| map.get(k));
        value.or_else(|| self.global.get(k)).cloned()
    }

    pub fn get_function(&self, k: &Expr) -> Option<Rc<Expr>> {
        self.function.get(k).cloned()
    }

    pub fn enter_scope(&mut self) -> Scope {
        self.stack.push(Map::new());
        Scope { env: self }
    }

    fn exit_scope(&mut self) {
        self.stack.pop();
    }

    pub fn capture(&self) -> Vec<(Rc<Expr>, Rc<Expr>)> {
        match self.stack.last() {
            Some(map) => map.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
            None => Vec::new(),
        }
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

        {
            let mut scope = env.enter_scope();
            assert_eq!(scope.get(&number(10)), Some(number(20)));

            scope.insert(number(10), number(30));
            scope.insert(number(20), number(40));
            assert_eq!(scope.get(&number(10)), Some(number(30)));
            assert_eq!(scope.get(&number(20)), Some(number(40)));
        }

        assert_eq!(env.get(&number(10)), Some(number(20)));
        assert_eq!(env.get(&number(20)), None);
    }
}
