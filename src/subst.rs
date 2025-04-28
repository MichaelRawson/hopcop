use std::fmt;

use crate::syntax::{Application, Literal, Term};
use crate::util::Perfect;
use fnv::FnvHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Location(usize);

impl Location {
    pub(crate) fn new(index: usize) -> Self {
        Self(index)
    }
}

pub(crate) const ROOT: Location = Location(0);
pub(crate) const BANK1: Location = Location(1);
pub(crate) const BANK2: Location = Location(2);

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Located<T> {
    location: Location,
    item: T,
}

impl Location {
    pub(crate) fn locate<T>(self, item: T) -> Located<T> {
        Located {
            location: self,
            item,
        }
    }
}

impl<T: fmt::Display> fmt::Display for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.item, self.location)
    }
}

impl<T> Located<T> {
    fn transfer<S>(&self, item: S) -> Located<S> {
        Located {
            location: self.location,
            item,
        }
    }

    fn map<S, F: FnOnce(T) -> S>(self, f: F) -> Located<S> {
        Located {
            location: self.location,
            item: f(self.item),
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct Substitution {
    map: FnvHashMap<Located<usize>, Located<Term>>,
    trail: Vec<Located<usize>>,
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for x in &self.trail {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{} -> {}", x, self.map[x])?;
            first = false;
        }
        write!(f, "}}")
    }
}

impl Substitution {
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn len(&self) -> usize {
        self.trail.len()
    }

    pub(crate) fn clear(&mut self) {
        self.map.clear();
        self.trail.clear();
    }

    pub(crate) fn truncate(&mut self, to: usize) {
        assert!(to <= self.len());
        while to < self.len() {
            let next = self.trail.pop().unwrap();
            assert!(self.map.remove(&next).is_some());
        }
    }

    pub(crate) fn unify(&mut self, left: Located<Term>, right: Located<Term>) -> bool {
        let start = self.trail.len();
        let mut todo = vec![];
        let mut next = Some((left, right));
        while let Some((left, right)) = next {
            let left = self.lookup(left);
            let right = self.lookup(right);
            if left == right {
                next = todo.pop();
                continue;
            }
            match (left.item, right.item) {
                (Term::Var(x), Term::Var(_)) => {
                    let left = left.transfer(x);
                    self.map.insert(left, right);
                    self.trail.push(left);
                }
                (Term::Var(x), Term::App(app)) => {
                    if !self.bind(left.transfer(x), right.transfer(app)) {
                        self.truncate(start);
                        return false;
                    }
                }
                (Term::App(t), Term::Var(x)) => {
                    if !self.bind(right.transfer(x), left.transfer(t)) {
                        self.truncate(start);
                        return false;
                    }
                }
                (Term::App(lapp), Term::App(rapp)) => {
                    if lapp.symbol != rapp.symbol {
                        self.truncate(start);
                        return false;
                    }
                    todo.extend(Iterator::zip(
                        lapp.args.iter().map(|arg| left.transfer(*arg)),
                        rapp.args.iter().map(|arg| right.transfer(*arg)),
                    ));
                }
            }
            next = todo.pop();
        }
        true
    }

    pub(crate) fn unify_literal(&mut self, l: Located<Literal>, k: Located<Literal>) -> bool {
        assert_ne!(l.item.polarity, k.item.polarity);
        self.unify(l.map(|l| Term::App(l.atom)), k.map(|r| Term::App(r.atom)))
    }

    fn bind(&mut self, x: Located<usize>, t: Located<Perfect<Application>>) -> bool {
        let mut todo: Vec<_> = t.item.args.iter().map(|arg| t.transfer(*arg)).collect();
        while let Some(next) = todo.pop() {
            let next = self.lookup(next);
            match next.item {
                Term::Var(y) => {
                    if x == next.transfer(y) {
                        return false;
                    }
                }
                Term::App(app) => {
                    todo.extend(app.args.iter().map(|arg| next.transfer(*arg)));
                }
            }
        }
        self.map.insert(x, t.map(Term::App));
        self.trail.push(x);
        true
    }

    fn lookup(&self, mut term: Located<Term>) -> Located<Term> {
        while let Term::Var(x) = term.item {
            if let Some(bound) = self.map.get(&term.transfer(x)) {
                term = *bound;
            } else {
                break;
            }
        }
        term
    }
}
