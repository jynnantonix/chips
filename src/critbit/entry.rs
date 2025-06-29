use salsa::Database;

use crate::critbit::{
    Key, Value,
    cursor::Cursor,
    zipper::{Context, Elem, Node, Zipper},
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, salsa::Update)]
pub enum Entry<'db> {
    Vacant(VacantEntry<'db>),
    Occupied(OccupiedEntry<'db>),
}

impl<'db> Entry<'db> {
    pub fn or_insert(self, db: &'db dyn Database, value: Value) -> Cursor<'db> {
        match self {
            Entry::Vacant(vacant_entry) => vacant_entry.insert(db, value),
            Entry::Occupied(occupied_entry) => occupied_entry.get(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, salsa::Update)]
pub struct VacantEntry<'db> {
    key: Key,
    bitpos: u32,
    zipper: Zipper<'db>,
}

impl<'db> VacantEntry<'db> {
    pub(crate) fn new(key: Key, bitpos: u32, zipper: Zipper<'db>) -> Self {
        Self {
            key,
            bitpos,
            zipper,
        }
    }

    /// Inserts `value` into the tree and returns a `Cursor` pointing at the newly inserted value.
    pub fn insert(self, db: &'db dyn Database, value: Value) -> Cursor<'db> {
        // If the current node is empty then we replace it.  Otherwise we insert an internal node.
        if self.zipper.tree(db).node(db) == Node::Empty {
            return Cursor::new(db, self.key, value, self.zipper.ctx(db));
        }

        let mask = 1u64 << self.bitpos;
        let elem = if self.key.k(db) & mask == 0 {
            // The new value is inserted on the left.
            Elem::Left {
                bitpos: self.bitpos,
                right: self.zipper.tree(db),
                ctx: self.zipper.ctx(db),
            }
        } else {
            // The new value is inserted on the right.
            Elem::Right {
                bitpos: self.bitpos,
                left: self.zipper.tree(db),
                ctx: self.zipper.ctx(db),
            }
        };

        let ctx = Context::new(db, elem);
        Cursor::new(db, self.key, value, ctx)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, salsa::Update)]
pub struct OccupiedEntry<'db> {
    cursor: Cursor<'db>,
}

impl<'db> OccupiedEntry<'db> {
    pub(crate) fn new(cursor: Cursor<'db>) -> Self {
        Self { cursor }
    }

    /// Returns the `Key` for this entry.
    pub fn key(self, db: &'db dyn Database) -> Key {
        self.cursor.key(db)
    }

    /// Returns the `Value` for this entry.
    pub fn value(self, db: &'db dyn Database) -> Value {
        self.cursor.value(db)
    }

    /// Returns a `Cursor` pointing at this entry.
    pub fn get(self) -> Cursor<'db> {
        self.cursor
    }

    /// Removes this entry.
    ///
    /// Returns `Value` for this entry and an optionally a new `Cursor` pointing to an adjacent
    /// node in the tree.  If this operation would remove the last node in the tree then no `Cursor`
    /// is returned.
    pub fn remove(self, db: &'db dyn Database) -> (Value, Option<Cursor<'db>>) {
        self.cursor.remove(db)
    }
}
