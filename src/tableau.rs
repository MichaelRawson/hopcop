use fnv::{FnvBuildHasher, FnvHashMap};
use indexmap::IndexMap;

use crate::subst::{Branch, Location, ROOT};
use crate::syntax::Clause;

#[derive(Clone, Copy)]
pub(crate) struct Node {
    pub(crate) branch: Branch,
    pub(crate) depth: usize,
    pub(crate) clause: &'static Clause,
}

#[derive(Default)]
pub(crate) struct Tableau {
    map: FnvHashMap<Branch, Location>,
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

    pub(crate) fn locate(&mut self, branch: Branch) -> Location {
        let next = Location::new(self.map.len() + 1);
        *self.map.entry(branch).or_insert(next)
    }

    pub(crate) fn locations(&self) -> impl Iterator<Item = Location> {
        self.nodes.keys().copied()
    }

    pub(crate) fn set_root_clause(&mut self, clause: &'static Clause) {
        let replaced = self.nodes.insert(
            ROOT,
            Node {
                branch: Branch {
                    location: Location::new(usize::MAX),
                    index: usize::MAX,
                },
                depth: 0,
                clause,
            },
        );
        assert!(replaced.is_none());
    }

    pub(crate) fn add_clause(&mut self, branch: Branch, clause: &'static Clause) {
        let depth = self[branch.location].depth + 1;
        let location = self.locate(branch);
        let replaced = self.nodes.insert(
            location,
            Node {
                branch,
                depth,
                clause,
            },
        );
        assert!(replaced.is_none());
    }

    pub(crate) fn graphviz(&self) {
        println!("digraph tableau {{");
        println!("\tnode [shape=none];");
        println!("\tl{}_{} [label=\"\"];", usize::MAX, usize::MAX);
        for (location, node) in &self.nodes {
            for (index, literal) in node.clause.literals.iter().enumerate() {
                let branch = Branch {
                    location: *location,
                    index,
                };
                println!("\t{branch} [label=\"{literal}\"];");
                println!("\t{} -> {};", node.branch, branch);
            }
        }
        println!("}}");
    }
}
