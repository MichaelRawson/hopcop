use fnv::{FnvBuildHasher, FnvHashMap};
use indexmap::IndexSet;
use std::fmt;
use std::hash::Hash;

use crate::subst::Location;
use crate::syntax::Literal;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Atom {
    Place(Location, Literal),
    Connect(Location, Location),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Place(location, literal) => write!(f, "{}@{}", literal, location),
            Atom::Connect(l, k) => write!(f, "{}~{}", l, k),
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

    pub(crate) fn find_conflict(&mut self, atom: Atom, assignment: &Assignment) -> Option<&[Atom]> {
        let mut needs_move = self.watch.remove(&atom)?;
        while let Some(clause) = needs_move.pop() {
            if let Some(watched) = watch(&clause, assignment) {
                self.watch.entry(watched).or_default().push(clause);
            } else {
                // abort, conflict found
                let reinserted = self.watch.entry(atom).or_insert(needs_move);
                reinserted.push(clause);
                return reinserted.last().map(|b| &**b);
            }
        }
        None
    }
}
