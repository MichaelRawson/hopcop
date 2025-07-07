use fnv::{FnvBuildHasher, FnvHashMap};
use indexmap::IndexSet;
use std::fmt;
use std::hash::Hash;

use crate::subst::{Located, Location};
use crate::syntax::{Literal, Term};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Atom {
    Place(Location, Literal),
    Bind(Located<usize>, Located<Term>),
    CannotReduce(Location, Location),
    Disequation(Located<Term>, Located<Term>),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Place(location, literal) => write!(f, "{literal}@{location}"),
            Atom::Bind(x, t) => write!(f, "{x}->{t}"),
            Atom::CannotReduce(l, k) => write!(f, "{l}≁{k}"),
            Atom::Disequation(s, t) => write!(f, "{s}≠{t}"),
        }
    }
}

type Assignment = IndexSet<Atom, FnvBuildHasher>;

#[derive(Default)]
pub(crate) struct DB {
    watch: FnvHashMap<Atom, Vec<Box<[Atom]>>>,
}

fn watch(clause: &[Atom], assignment: &Assignment) -> Option<Atom> {
    clause.iter().find(|a| !assignment.contains(*a)).copied()
}

impl DB {
    pub(crate) fn clear(&mut self) {
        self.watch.clear();
    }

    pub(crate) fn insert(&mut self, clause: Box<[Atom]>, assignment: &Assignment) {
        let watched = watch(&clause, assignment).expect("inserted conflicting clause");
        self.watch.entry(watched).or_default().push(clause);
    }

    pub(crate) fn find_conflicts(
        &mut self,
        atom: Atom,
        assignment: &Assignment,
    ) -> Option<&Vec<Box<[Atom]>>> {
        let mut needs_move = self.watch.remove(&atom)?;
        let mut i = 0;
        while i < needs_move.len() {
            if let Some(watched) = watch(&needs_move[i], assignment) {
                self.watch
                    .entry(watched)
                    .or_default()
                    .push(needs_move.swap_remove(i));
            } else {
                i += 1;
            }
        }
        if needs_move.is_empty() {
            return None;
        }
        Some(self.watch.entry(atom).or_insert(needs_move))
    }
}
