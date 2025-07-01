use salsa::Database;

use crate::salsa::{
    Key, Map, Value,
    zipper::{Context, Elem, Node, Tree, Zipper},
};

/// Like `Zipper`, except a `Cursor` can only focus leaf nodes.
#[salsa::tracked(debug)]
pub struct Cursor<'db> {
    #[tracked]
    pub key: Key,
    #[tracked]
    pub value: Value,
    #[tracked]
    ctx: Context<'db>,
}

#[salsa::tracked]
pub(crate) fn make_cursor<'db>(
    db: &'db dyn Database,
    key: Key,
    value: Value,
    ctx: Context<'db>,
) -> Cursor<'db> {
    Cursor::new(db, key, value, ctx)
}

#[salsa::tracked]
impl<'db> Cursor<'db> {
    #[salsa::tracked]
    fn zipper(self, db: &'db dyn Database) -> Zipper<'db> {
        let node = Node::Leaf {
            key: self.key(db),
            value: self.value(db),
        };
        let tree = Tree::new(db, node);
        let ctx = self.ctx(db);
        Zipper::new(db, tree, ctx)
    }

    #[salsa::tracked]
    pub fn next(self, db: &'db dyn Database) -> Option<Self> {
        let mut zipper = self.zipper(db);
        // Find the first left branch we took to get here.
        loop {
            match zipper.ctx(db).elem(db) {
                Elem::Top => return None,
                Elem::Left { .. } => {
                    break;
                }
                Elem::Right { .. } => {
                    zipper = zipper.up(db);
                }
            }
        }

        // We know we went down a left subtree to get here.  Go up one and then go down the left
        // side of the right subtree.
        Some(leftmost(db, zipper.up(db).right(db)))
    }

    #[salsa::tracked]
    pub fn prev(self, db: &'db dyn Database) -> Option<Self> {
        let mut zipper = self.zipper(db);
        // Find the first right branch we took to get here.
        loop {
            match zipper.ctx(db).elem(db) {
                Elem::Top => return None,
                Elem::Right { .. } => {
                    break;
                }
                Elem::Left { .. } => {
                    zipper = zipper.up(db);
                }
            }
        }

        // We know we went down a right subtree to get here.  Go up one and then go down the right
        // side of the left subtree.
        Some(rightmost(db, zipper.up(db).left(db)))
    }

    #[salsa::tracked]
    pub fn update(self, db: &'db dyn Database, value: Value) -> (Self, Value) {
        (
            Self::new(db, self.key(db), value, self.ctx(db)),
            self.value(db),
        )
    }

    #[salsa::tracked]
    pub fn remove(self, db: &'db dyn Database) -> (Value, Option<Self>) {
        match self.ctx(db).elem(db) {
            Elem::Top => (self.value(db), None),
            Elem::Left { right, ctx, .. } => {
                let zipper = Zipper::new(db, right, ctx);
                (self.value(db), Some(leftmost(db, zipper)))
            }
            Elem::Right { left, ctx, .. } => {
                let zipper = Zipper::new(db, left, ctx);
                (self.value(db), Some(rightmost(db, zipper)))
            }
        }
    }

    /// Returns a `Map` that contains this `Cursor`.
    #[salsa::tracked]
    pub fn to_map(self, db: &'db dyn Database) -> Map<'db> {
        let zipper = self.zipper(db).topmost(db);
        Map::new(db, zipper)
    }
}

#[salsa::tracked]
pub(crate) fn leftmost<'db>(db: &'db dyn Database, mut zipper: Zipper<'db>) -> Cursor<'db> {
    loop {
        match zipper.tree(db).node(db) {
            Node::Empty => unreachable!("Cannot get cursor for empty tree"),
            Node::Inner { .. } => zipper = zipper.left(db),
            Node::Leaf { key, value } => {
                return Cursor::new(db, key, value, zipper.ctx(db));
            }
        }
    }
}

#[salsa::tracked]
pub(crate) fn rightmost<'db>(db: &'db dyn Database, mut zipper: Zipper<'db>) -> Cursor<'db> {
    loop {
        match zipper.tree(db).node(db) {
            Node::Empty => unreachable!("Cannot get cursor for empty tree"),
            Node::Inner { .. } => zipper = zipper.right(db),
            Node::Leaf { key, value } => {
                return Cursor::new(db, key, value, zipper.ctx(db));
            }
        }
    }
}
