use salsa::Database;

use crate::critbit::{Key, Value};

#[salsa::tracked(debug)]
pub struct Context<'db> {
    #[tracked]
    pub elem: Elem<'db>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, salsa::Update)]
pub enum Elem<'db> {
    Top,
    Left {
        bitpos: u32,
        right: Tree<'db>,
        ctx: Context<'db>,
    },
    Right {
        bitpos: u32,
        left: Tree<'db>,
        ctx: Context<'db>,
    },
}

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

#[salsa::tracked(debug)]
pub struct Zipper<'db> {
    #[tracked]
    pub tree: Tree<'db>,
    #[tracked]
    pub ctx: Context<'db>,
}

#[salsa::tracked]
pub fn empty<'db>(db: &'db dyn Database) -> Zipper<'db> {
    let tree = Tree::new(db, Node::Empty);
    top(db, tree)
}

#[salsa::tracked]
pub fn top<'db>(db: &'db dyn Database, tree: Tree<'db>) -> Zipper<'db> {
    let ctx = Context::new(db, Elem::Top);
    Zipper::new(db, tree, ctx)
}

#[salsa::tracked]
impl<'db> Zipper<'db> {
    #[salsa::tracked]
    pub fn left(self, db: &'db dyn Database) -> Self {
        let tree = self.tree(db);
        match tree.node(db) {
            Node::Inner {
                left,
                right,
                bitpos,
            } => self.make_left_zipper(db, left, right, bitpos),
            Node::Empty | Node::Leaf { .. } => self,
        }
    }

    #[salsa::tracked]
    pub fn right(self, db: &'db dyn Database) -> Self {
        let node = self.tree(db);
        match node.node(db) {
            Node::Inner {
                left,
                right,
                bitpos,
            } => self.make_right_zipper(db, left, right, bitpos),
            Node::Empty | Node::Leaf { .. } => self,
        }
    }

    #[salsa::tracked]
    pub fn up(self, db: &'db dyn Database) -> Self {
        let ctx = self.ctx(db);
        match ctx.elem(db) {
            Elem::Top => self,
            Elem::Left { bitpos, right, ctx } => {
                let left = self.tree(db);
                let node = Tree::new(
                    db,
                    Node::Inner {
                        left,
                        right,
                        bitpos,
                    },
                );
                Zipper::new(db, node, ctx)
            }
            Elem::Right { bitpos, left, ctx } => {
                let right = self.tree(db);
                let node = Tree::new(
                    db,
                    Node::Inner {
                        left,
                        right,
                        bitpos,
                    },
                );
                Zipper::new(db, node, ctx)
            }
        }
    }

    #[salsa::tracked]
    pub fn topmost(self, db: &'db dyn Database) -> Self {
        let mut current = self;
        while current.ctx(db).elem(db) != Elem::Top {
            current = current.up(db);
        }
        current
    }

    #[salsa::tracked]
    pub fn len(self, db: &'db dyn Database) -> usize {
        match self.tree(db).node(db) {
            Node::Empty => 0,
            Node::Inner {
                left,
                right,
                bitpos,
            } => {
                self.make_left_zipper(db, left, right, bitpos).len(db)
                    + self.make_right_zipper(db, left, right, bitpos).len(db)
            }
            Node::Leaf { .. } => 1,
        }
    }

    #[salsa::tracked]
    pub fn is_empty(self, db: &'db dyn Database) -> bool {
        matches!(self.tree(db).node(db), Node::Empty)
    }

    #[salsa::tracked]
    pub fn update(self, db: &'db dyn Database, tree: Tree<'db>) -> Self {
        Zipper::new(db, tree, self.ctx(db))
    }

    #[salsa::tracked]
    fn make_left_zipper(
        self,
        db: &'db dyn Database,
        left: Tree<'db>,
        right: Tree<'db>,
        bitpos: u32,
    ) -> Zipper<'db> {
        let ctx = self.ctx(db);
        let elem = Elem::Left { bitpos, right, ctx };
        let ctx = Context::new(db, elem);
        Zipper::new(db, left, ctx)
    }

    #[salsa::tracked]
    fn make_right_zipper(
        self,
        db: &'db dyn Database,
        left: Tree<'db>,
        right: Tree<'db>,
        bitpos: u32,
    ) -> Zipper<'db> {
        let ctx = self.ctx(db);
        let elem = Elem::Right { bitpos, left, ctx };
        let ctx = Context::new(db, elem);
        Zipper::new(db, right, ctx)
    }
}
