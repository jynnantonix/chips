use salsa::Database;

use crate::critbit::{Key, Value};

#[salsa::tracked(debug)]
pub struct Tree<'db> {
    #[tracked]
    pub node: Node<'db>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, salsa::Update)]
pub enum Node<'db> {
    Empty,
    Inner {
        left: Tree<'db>,
        right: Tree<'db>,
        bitpos: u32,
    },
    Leaf {
        key: Key,
        value: Value,
    },
}

#[salsa::tracked]
pub fn empty<'db>(db: &'db dyn Database) -> Tree<'db> {
    Tree::new(db, Node::Empty)
}
