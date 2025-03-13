use fnv::{FnvHashMap, FnvHashSet};

use crate::subst::{Substitution, Tagged};
use crate::syntax::{Clause, Literal, Matrix};

#[derive(Debug, Clone, Copy)]
struct Member {
    parent: usize,
    literal: Literal,
}

pub(crate) struct Search {
    matrix: Matrix,
    positions: FnvHashMap<(usize, usize), usize>,
    members: FnvHashMap<usize, Member>,
    open: Vec<usize>,
    substitution: Substitution,
}

impl Search {
    pub(crate) fn new(matrix: Matrix) -> Self {
        Self {
            matrix,
            positions: FnvHashMap::default(),
            members: FnvHashMap::default(),
            open: vec![],
            substitution: Substitution::default(),
        }
    }

    pub(crate) fn graphviz(&self) {
        println!("digraph tableau {{");
        println!("\tnode [shape=none];");
        println!("\tl0 [label=\"\"];");
        for (position, member) in self.members.iter() {
            println!("\tl{} [label=\"{}\"];", position, member.literal);
            println!("\tl{} -> l{};", member.parent, position);
        }
        println!("}}");
    }

    pub(crate) fn expand_or_backtrack(&mut self) {
        if self.members.is_empty() {
            for i in 0..self.matrix.start.len() {
                if self.start(self.matrix.start[i]) {
                    return;
                }
            }
        }
        else if let Some(next) = self.open.pop() {
            let member = self.members[&next];
            dbg!(member);
        }
    }

    fn start(&mut self, clause: &'static Clause) -> bool {
        assert!(self.members.is_empty());
        assert!(self.open.is_empty());
        for (index, literal) in clause.literals.iter().enumerate() {
            let position = self.position(0, index);
            let member = Member { parent: 0, literal: *literal };
            self.members.insert(position, member);
            self.open.push(position);
        }
        true
    }

    fn position(&mut self, parent: usize, child: usize) -> usize {
        let next = self.positions.len() + 1;
        *self.positions.entry((parent, child)).or_insert_with(|| { eprintln!("{}@{} -> {}", parent, child, next); next })
    }
}
