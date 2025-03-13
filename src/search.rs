use fnv::FnvHashMap;

use crate::subst::{Substitution, Tagged};
use crate::syntax::{Clause, Literal, Matrix, Position};

#[derive(Debug, Clone, Copy)]
struct Member {
    parent: usize,
    literal: Literal,
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    locations: FnvHashMap<(usize, usize), usize>,
    members: FnvHashMap<usize, Member>,
    open: Vec<usize>,
    substitution: Substitution,
    trail: Vec<()>,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        Self {
            matrix,
            locations: FnvHashMap::default(),
            members: FnvHashMap::default(),
            open: vec![],
            substitution: Substitution::default(),
            trail: vec![],
        }
    }

    pub(crate) fn closed(&self) -> bool {
        self.open.is_empty() && !self.trail.is_empty()
    }

    pub(crate) fn graphviz(&self) {
        println!("digraph tableau {{");
        println!("\tnode [shape=none];");
        println!("\tl0 [label=\"\"];");
        for (location, member) in self.members.iter() {
            println!("\tl{} [label=\"{}\"];", location, member.literal);
            println!("\tl{} -> l{};", member.parent, location);
        }
        println!("}}");
    }

    pub(crate) fn expand_or_backtrack(&mut self) {
        assert!(!self.closed());
        dbg!(self.open.len());
        eprintln!("{}", self.substitution);

        if let Some(next) = self.open.pop() {
            let restore = self.substitution.len();
            let member = self.members[&next];
            eprintln!("selected: {}", member.literal);
            let mut parent = member.parent;
            while parent != 0 {
                let parent_member = self.members[&parent];
                let grandparent = parent_member.parent;
                if self.substitution.connect(
                    Tagged::new(grandparent, parent_member.literal),
                    Tagged::new(member.parent, member.literal),
                ) {
                    eprintln!("reduced!");
                    return;
                }
                self.substitution.undo_to(restore);
                parent = grandparent;
            }

            let Literal { polarity, atom } = member.literal;
            if let Some(positions) = self.matrix.index.get(&(!polarity, atom.symbol)) {
                for position in positions {
                    if self.extend(next, member, *position) {
                        return;
                    }
                    self.substitution.undo_to(restore);
                }
            }
        } else if self.trail.is_empty() {
            for i in 0..self.matrix.start.len() {
                if self.start(self.matrix.start[i]) {
                    self.trail.push(());
                    return;
                }
            }
        }

        todo!()
    }

    fn start(&mut self, clause: &'static Clause) -> bool {
        assert!(self.members.is_empty());
        assert!(self.open.is_empty());
        for (index, literal) in clause.literals.iter().enumerate() {
            let location = self.location(0, index);
            let member = Member {
                parent: 0,
                literal: *literal,
            };
            assert!(self.members.insert(location, member).is_none());
            self.open.push(location);
        }
        true
    }

    fn extend(&mut self, at: usize, member: Member, position: Position) -> bool {
        if !self.substitution.connect(
            Tagged::new(at, position.literal),
            Tagged::new(member.parent, member.literal),
        ) {
            return false;
        }

        for (index, literal) in position.clause.literals.iter().enumerate() {
            let location = self.location(at, index);
            let member = Member {
                parent: at,
                literal: *literal,
            };
            self.members.insert(location, member);
            if *literal != position.literal {
                self.open.push(location);
            }
        }
        true
    }

    fn location(&mut self, parent: usize, child: usize) -> usize {
        let next = self.locations.len() + 1;
        *self.locations.entry((parent, child)).or_insert_with(|| {
            eprintln!("{}@{} -> {}", parent, child, next);
            next
        })
    }
}
