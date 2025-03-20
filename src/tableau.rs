use fnv::{FnvBuildHasher, FnvHashMap};
use indexmap::IndexMap;
use std::fmt;

use crate::syntax::Literal;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Location(usize);

impl Location {
    pub(crate) fn as_usize(self) -> usize {
        self.0
    }
}

pub(crate) const ROOT: Location = Location(0);

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", self.0)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Node {
    pub(crate) parent: Location,
    pub(crate) depth: usize,
    pub(crate) literal: Literal,
}

#[derive(Default)]
pub(crate) struct Tableau {
    map: FnvHashMap<(Location, usize), Location>,
    nodes: IndexMap<Location, Node, FnvBuildHasher>,
}

impl std::ops::Index<Location> for Tableau {
    type Output = Node;
    fn index(&self, location: Location) -> &Node {
        &self.nodes[&location]
    }
}

impl Tableau {
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn clear(&mut self) {
        self.nodes.clear();
    }

    pub(crate) fn truncate(&mut self, to: usize) {
        self.nodes.truncate(to);
    }

    pub(crate) fn contains(&self, location: Location) -> bool {
        self.nodes.contains_key(&location)
    }

    pub(crate) fn locate(&mut self, parent: Location, child: usize) -> Location {
        let next = Location(self.map.len() + 1);
        *self.map.entry((parent, child)).or_insert(next)
    }

    pub(crate) fn set(
        &mut self,
        literal: Literal,
        location: Location,
        parent: Location,
        depth: usize,
    ) {
        let node = Node {
            parent,
            depth,
            literal,
        };
        self.nodes.insert(location, node);
    }

    pub(crate) fn graphviz(&self) {
        println!("digraph tableau {{");
        println!("\tnode [shape=none];");
        println!("\tl0 [label=\"\"];");
        for (location, node) in &self.nodes {
            println!("\t{} [label=\"{}. {}\"];", location, location, node.literal);
            println!("\t{} -> {};", node.parent, location);
        }
        println!("}}");
    }
}
