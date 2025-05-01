use fnv::{FnvBuildHasher, FnvHashSet};
use indexmap::IndexSet;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::db::{Atom, DB};
use crate::subst::{BANK1, BANK2, Located, Location, ROOT, Substitution};
use crate::syntax::{Clause, Extension, Literal, Matrix};
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
        eprintln!("substitution: {}", self.substitution);
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
            let grandparent = member.parent;
            if self.reduce(ancestor, open) {
                return true;
            }
            ancestor = grandparent;
        }

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
        false
    }

    fn reduce(&mut self, parent: Location, open: Location) -> bool {
        let parent_node = self.tableau[parent];
        let open_node = self.tableau[open];
        if self.atoms.contains(&Atom::CannotReduce(parent, open)) {
            self.learn.insert(Atom::CannotReduce(parent, open));
            return false;
        }

        let restore_subst = self.substitution.len();
        let left = parent_node.parent.locate(parent_node.literal);
        let right = open_node.parent.locate(open_node.literal);
        if !self.substitution.connect(left, right) {
            self.learn.insert(Atom::Place(parent, parent_node.literal));
            self.explain_unification_failure(left, right);
            return false;
        }

        let restore_atoms = self.atoms.len();
        self.atoms.insert(Atom::Connect(parent, open));
        if !self.check_atoms_since(restore_atoms) {
            self.substitution.truncate(restore_subst);
            self.atoms.truncate(restore_atoms);
            return false;
        }
        true
    }

    fn extend(&mut self, open: Location, extension: Extension) -> bool {
        let open_node = self.tableau[open];
        let el = extension.clause.literals[extension.index];
        if !self.could_unify(BANK1.locate(open_node.literal), BANK2.locate(el)) {
            return false;
        }

        let restore_subst = self.substitution.len();
        let l = open_node.parent.locate(open_node.literal);
        let k = open.locate(el);
        if !self.substitution.connect(l, k) {
            self.explain_unification_failure(l, k);
            return false;
        }

        let restore_tableau = self.tableau.len();
        let restore_atoms = self.atoms.len();
        let restore_open = self.open.len();
        for (index, literal) in extension.clause.literals.iter().copied().enumerate() {
            let location = self.add_child(open, literal, index, index != extension.index);
            if index == extension.index {
                self.atoms.insert(Atom::Connect(open, location));
            } else {
                self.open.push(location);
            }
        }
        if !self.check_atoms_since(restore_atoms) {
            self.substitution.truncate(restore_subst);
            self.tableau.truncate(restore_tableau);
            self.atoms.truncate(restore_atoms);
            self.open.truncate(restore_open);
            return false;
        }
        true
    }

    fn check_atoms_since(&mut self, after: usize) -> bool {
        let atoms = &self.atoms[after..];
        for atom in atoms {
            if let Some(conflict) = self.db.find_conflict(*atom, &self.atoms) {
                self.learn
                    .extend(conflict.iter().filter(|x| !atoms.iter().any(|a| a == *x)));
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

    fn explain_unification_failure(&mut self, l: Located<Literal>, k: Located<Literal>) {
        self.scratch.clear();
        assert!(self.scratch.connect(l, k));
        for atom in &self.learn {
            let (from, to) = if let Atom::Connect(from, to) = *atom {
                (from, to)
            } else {
                continue;
            };
            let from_node = self.tableau[from];
            let to_node = self.tableau[to];
            let l = from_node.parent.locate(from_node.literal);
            let k = to_node.parent.locate(to_node.literal);
            if !self.scratch.connect(l, k) {
                return;
            }
        }

        'outer: loop {
            let reset = self.scratch.len();
            for atom in &self.atoms {
                if self.learn.contains(atom) {
                    continue;
                }
                let (from, to) = if let Atom::Connect(from, to) = *atom {
                    (from, to)
                } else {
                    continue;
                };
                let from_node = self.tableau[from];
                let to_node = self.tableau[to];
                let l = from_node.parent.locate(from_node.literal);
                let k = to_node.parent.locate(to_node.literal);
                if !self.scratch.connect(l, k) {
                    self.scratch.truncate(reset);
                    self.learn.insert(*atom);
                    self.learn.insert(Atom::Place(from, from_node.literal));
                    self.learn.insert(Atom::Place(to, to_node.literal));
                    if self.scratch.connect(l, k) {
                        continue 'outer;
                    } else {
                        return;
                    }
                }
            }
            unreachable!()
        }
    }
}
