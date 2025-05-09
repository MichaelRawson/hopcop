use fnv::{FnvBuildHasher, FnvHashSet};
use indexmap::IndexSet;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::db::{Atom, DB};
use crate::subst::{Located, Location, ROOT, Substitution};
use crate::syntax::{Clause, Extension, Literal, Matrix, Term};
use crate::tableau::Tableau;

#[derive(Debug, Default, Clone, Copy)]
struct Restore {
    tableau: usize,
    substitution: usize,
    atoms: usize,
    closed: usize,
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    rng: SmallRng,
    tableau: Tableau,
    substitution: Substitution,
    atoms: IndexSet<Atom, FnvBuildHasher>,
    closed: Vec<Location>,
    restore: Vec<Restore>,
    open: Vec<Location>,
    learn: FnvHashSet<Atom>,
    db: DB,
    depth: usize,
    scratch: Substitution,
}

impl<'matrix> Search<'matrix> {
    fn restore(&mut self, restore: Restore) {
        self.tableau.truncate(restore.tableau);
        self.substitution.truncate(restore.substitution);
        self.atoms.truncate(restore.atoms);
        self.open.extend(self.closed.drain(restore.closed..));
        self.open.retain(|open| self.tableau.contains(*open));
    }

    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        Self {
            matrix,
            rng: SmallRng::seed_from_u64(0),
            tableau: Tableau::default(),
            substitution: Substitution::default(),
            atoms: IndexSet::default(),
            closed: vec![],
            restore: vec![],
            open: vec![],
            learn: FnvHashSet::default(),
            db: DB::default(),
            depth: 1,
            scratch: Substitution::default(),
        }
    }

    pub(crate) fn is_closed(&self) -> bool {
        !self.restore.is_empty() && self.open.is_empty()
    }

    pub(crate) fn graphviz(&self) {
        self.tableau.graphviz()
    }

    pub(crate) fn expand_or_backtrack(&mut self) {
        assert!(!self.is_closed());
        /*
        eprint!("atoms:");
        for atom in &self.atoms {
            eprint!(" {}", atom);
        }
        eprintln!();
        //eprintln!("substitution: {}", self.substitution);
        */

        self.learn.clear();
        self.restore.push(Restore {
            tableau: self.tableau.len(),
            substitution: self.substitution.len(),
            atoms: self.atoms.len(),
            closed: self.closed.len(),
        });

        if self.open.is_empty() {
            if self.try_start() {
                return;
            }
        } else {
            let index = self.rng.random_range(..self.open.len());
            let open = self.open.swap_remove(index);
            if self.try_close(open) {
                self.closed.push(open);
                return;
            }
            self.open.push(open);

            // add literal itself to learned clause
            self.learn
                .insert(Atom::Place(open, self.tableau[open].literal));
        }
        self.restore.pop();

        if self.learn.is_empty() {
            self.db.clear();
            self.depth += 1;
            dbg!(self.depth);
            return;
        }
        /*
        eprint!("learn:");
        for reason in &self.learn {
            eprint!(" {}", reason);
        }
        eprintln!();
        */

        let conflict_position = self
            .atoms
            .iter()
            .rposition(|atom| self.learn.contains(atom))
            .expect("live atoms do not contain learned clause");
        let restore_position = self
            .restore
            .iter()
            .rposition(|restore| restore.atoms <= conflict_position)
            .unwrap_or_default();

        let restore = self.restore[restore_position];
        self.restore.truncate(restore_position);
        self.restore(restore);
        self.db.insert(self.learn.drain().collect(), &self.atoms);
    }

    fn try_start(&mut self) -> bool {
        for start in &self.matrix.start {
            if self.start(start) {
                return true;
            }
        }
        false
    }

    fn start(&mut self, start: &'static Clause) -> bool {
        assert!(self.tableau.is_empty());
        assert!(self.substitution.is_empty());
        assert!(self.atoms.is_empty());
        assert!(self.closed.is_empty());
        assert!(self.open.is_empty());

        for (index, literal) in start.literals.iter().copied().enumerate() {
            let location = self.add_child(ROOT, literal, index, false);
            self.open.push(location);
        }
        self.atoms.extend(
            start
                .disequations
                .iter()
                .map(|d| Atom::Disequation(ROOT.locate(d.left), ROOT.locate(d.right))),
        );
        if !self.check_atoms_since(0) {
            self.tableau.clear();
            self.atoms.clear();
            self.open.clear();
            return false;
        }
        true
    }

    fn try_close(&mut self, open: Location) -> bool {
        let node = self.tableau[open];
        let mut ancestor = node.parent;
        while ancestor != ROOT {
            let member = self.tableau[ancestor];
            if self.reduce(ancestor, open) {
                return true;
            }
            ancestor = member.parent;
        }

        // regularity
        let restore_atoms = self.atoms.len();
        let mut ancestor = node.parent;
        let k = node.parent.locate(Term::App(node.literal.atom));
        while ancestor != ROOT {
            let member = self.tableau[ancestor];
            let l = member.parent.locate(Term::App(member.literal.atom));
            if member.literal.polarity == node.literal.polarity {
                self.scratch.clear();
                if self.scratch.unify(l, k) {
                    self.atoms.insert(Atom::Disequation(l, k));
                }
            }
            ancestor = member.parent;
        }
        // TODO check regularity ahead of time?

        let Literal { polarity, atom } = node.literal;
        if node.depth == self.depth {
            // TODO try to avoid learning depth limit here?
        } else if let Some(extensions) = self.matrix.index.get(&(!polarity, atom.symbol)) {
            for extension in extensions {
                if self.extend(open, *extension) {
                    return true;
                }
            }
        }

        // remove regularity disequations from learned clause on failure
        for atom in self.atoms.drain(restore_atoms..) {
            self.learn.remove(&atom);
        }

        false
    }

    fn reduce(&mut self, parent: Location, open: Location) -> bool {
        let parent_node = self.tableau[parent];
        let open_node = self.tableau[open];
        let l = parent_node.parent.locate(parent_node.literal);
        let k = open_node.parent.locate(open_node.literal);
        if !self.could_unify(l, k) {
            self.learn.insert(Atom::CannotReduce(parent, open));
            return false;
        }

        let restore_subst = self.substitution.len();
        if !self.substitution.connect(l, k) {
            self.learn.insert(Atom::Place(parent, parent_node.literal));
            self.explain_connection_failure(l, k);
            return false;
        }
        let restore_atoms = self.atoms.len();
        self.atoms
            .extend(self.scratch.bindings().map(|(x, t)| Atom::Bind(*x, *t)));
        if !self.check_atoms_since(restore_atoms) {
            self.substitution.truncate(restore_subst);
            for atom in self.atoms.drain(restore_atoms..) {
                self.learn.remove(&atom);
            }
            return false;
        }
        true
    }

    fn extend(&mut self, open: Location, extension: Extension) -> bool {
        let open_node = self.tableau[open];
        let el = extension.clause.literals[extension.index];
        let l = open_node.parent.locate(open_node.literal);
        let k = open.locate(el);
        if !self.could_unify(l, k) {
            return false;
        }

        let restore_subst = self.substitution.len();
        if !self.substitution.connect(l, k) {
            self.explain_connection_failure(l, k);
            return false;
        }

        let restore_tableau = self.tableau.len();
        let restore_atoms = self.atoms.len();
        let restore_open = self.open.len();
        self.atoms
            .extend(self.scratch.bindings().map(|(x, t)| Atom::Bind(*x, *t)));
        for (index, literal) in extension.clause.literals.iter().copied().enumerate() {
            let location = self.add_child(open, literal, index, index != extension.index);
            if index != extension.index {
                self.open.push(location);
            }
        }
        self.atoms.extend(
            extension
                .clause
                .disequations
                .iter()
                .map(|d| Atom::Disequation(open.locate(d.left), open.locate(d.right))),
        );
        if !self.check_atoms_since(restore_atoms) {
            self.substitution.truncate(restore_subst);
            self.tableau.truncate(restore_tableau);
            for atom in self.atoms.drain(restore_atoms..) {
                self.learn.remove(&atom);
            }
            self.open.truncate(restore_open);
            return false;
        }
        true
    }

    // TODO better name
    fn check_atoms_since(&mut self, after: usize) -> bool {
        let atoms = &self.atoms[after..];
        for atom in atoms {
            if let Some(conflict) = self.db.find_conflict(*atom, &self.atoms) {
                self.learn
                    .extend(conflict.iter().filter(|x| !atoms.iter().any(|a| a == *x)));
                return false;
            }
        }
        for atom in &self.atoms {
            let (left, right) = if let Atom::Disequation(left, right) = atom {
                (*left, *right)
            } else {
                continue;
            };
            if self.substitution.equal(left, right) {
                self.explain_equal(left, right);
                return false;
            }
        }
        true
    }

    fn could_unify(&mut self, l: Located<Literal>, k: Located<Literal>) -> bool {
        self.scratch.clear();
        l.item.polarity != k.item.polarity && self.scratch.connect(l, k)
    }

    fn add_child(
        &mut self,
        open: Location,
        literal: Literal,
        index: usize,
        try_unify: bool,
    ) -> Location {
        let location = self.tableau.add_child(open, literal, index);
        self.atoms.insert(Atom::Place(location, literal));
        if !try_unify {
            return location;
        }

        let mut ancestor = open;
        while ancestor != ROOT {
            let node = self.tableau[ancestor];
            if !self.could_unify(node.parent.locate(node.literal), open.locate(literal)) {
                self.atoms.insert(Atom::CannotReduce(ancestor, location));
            }
            ancestor = node.parent;
        }
        location
    }

    fn explain_connection_failure(&mut self, l: Located<Literal>, k: Located<Literal>) {
        self.scratch.clear();
        assert!(self.scratch.connect(l, k));
        for atom in &self.learn {
            if let Atom::Bind(x, t) = *atom {
                if !self.scratch.unify(x.map(Term::Var), t) {
                    return;
                }
            }
        }

        'outer: loop {
            let reset = self.scratch.len();
            for atom in &self.atoms {
                if self.learn.contains(atom) {
                    continue;
                }
                let (x, t) = if let Atom::Bind(x, t) = *atom {
                    (x, t)
                } else {
                    continue;
                };
                if self.scratch.unify(x.map(Term::Var), t) {
                    continue;
                }
                self.scratch.truncate(reset);
                self.learn.insert(*atom);
                if self.scratch.unify(x.map(Term::Var), t) {
                    continue 'outer;
                } else {
                    return;
                }
            }
            unreachable!()
        }
    }

    fn explain_equal(&mut self, left: Located<Term>, right: Located<Term>) {
        self.learn.insert(Atom::Disequation(left, right));
        self.scratch.clear();
        for atom in &self.learn {
            if let Atom::Bind(x, t) = *atom {
                assert!(self.scratch.unify(x.map(Term::Var), t));
            }
        }
        if self.scratch.equal(left, right) {
            return;
        }

        'outer: loop {
            let reset = self.scratch.len();
            for atom in &self.atoms {
                if self.learn.contains(atom) {
                    continue;
                }
                let (x, t) = if let Atom::Bind(x, t) = *atom {
                    (x, t)
                } else {
                    continue;
                };
                assert!(self.scratch.unify(x.map(Term::Var), t));
                if !self.scratch.equal(left, right) {
                    continue;
                }
                self.scratch.truncate(reset);
                self.learn.insert(*atom);
                assert!(self.scratch.unify(x.map(Term::Var), t));
                if self.scratch.equal(left, right) {
                    return;
                } else {
                    continue 'outer;
                }
            }
            unreachable!()
        }
    }
}
