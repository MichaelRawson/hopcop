use fnv::{FnvBuildHasher, FnvHashMap};
use indexmap::IndexMap;

use crate::subst::{Location, ROOT};
use crate::syntax::Literal;

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
        let next = Location::new(self.map.len() + 1);
        *self.map.entry((parent, child)).or_insert(next)
    }

    pub(crate) fn add_child(
        &mut self,
        parent: Location,
        literal: Literal,
        index: usize,
    ) -> Location {
        let depth = if parent == ROOT {
            1
        } else {
            self[parent].depth + 1
        };
        let child = self.locate(parent, index);
        self.nodes.insert(
            child,
            Node {
                parent,
                depth,
                literal,
            },
        );
        child
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
