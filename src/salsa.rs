use std::iter::FusedIterator;

use cursor::{Cursor, leftmost, make_cursor};
use entry::{Entry, OccupiedEntry, VacantEntry};
use salsa::Database;
use zipper::{Elem, Node, Zipper};

mod cursor;
pub mod entry;
mod zipper;

#[salsa::input(debug)]
#[derive(PartialOrd, Ord)]
pub struct Key {
    pub k: u64,
}

#[salsa::input(debug)]
#[derive(PartialOrd, Ord)]
pub struct Value {
    pub v: u64,
}

#[salsa::tracked(debug)]
pub struct Map<'db> {
    #[tracked]
    zipper: Zipper<'db>,
}

#[salsa::tracked]
pub fn empty<'db>(db: &'db dyn Database) -> Map<'db> {
    Map::new(db, zipper::empty(db))
}

#[salsa::tracked]
impl<'db> Map<'db> {
    #[salsa::tracked]
    pub fn entry(self, db: &'db dyn Database, key: Key) -> Entry<'db> {
        let mut current = self.zipper(db);
        loop {
            match current.tree(db).node(db) {
                // Only the top node will ever be empty.
                Node::Empty => {
                    debug_assert_eq!(Elem::Top, current.ctx(db).elem(db));
                    return Entry::Vacant(VacantEntry::new(key, 0, current));
                }
                Node::Leaf { key: k, value } => {
                    let k1 = key.k(db);
                    let k2 = k.k(db);
                    if k1 == k2 {
                        let cursor = Cursor::new(db, key, value, current.ctx(db));
                        return Entry::Occupied(OccupiedEntry::new(cursor));
                    }

                    // The keys don't match so find the critical bit.
                    let critbit = (k1 ^ k2).trailing_zeros();
                    let zipper = get_insert_position(db, current, critbit);
                    return Entry::Vacant(VacantEntry::new(key, critbit, zipper));
                }
                Node::Inner { bitpos, .. } => {
                    let mask = 1u64 << bitpos;
                    if key.k(db) & mask == 0 {
                        current = current.left(db);
                    } else {
                        current = current.right(db);
                    }
                }
            }
        }
    }

    #[salsa::tracked]
    pub fn get(self, db: &'db dyn Database, key: Key) -> Option<Value> {
        match self.entry(db, key) {
            Entry::Vacant(_) => None,
            Entry::Occupied(occupied_entry) => Some(occupied_entry.value(db)),
        }
    }

    #[salsa::tracked]
    pub fn insert(self, db: &'db dyn Database, key: Key, value: Value) -> (Self, Option<Value>) {
        match self.entry(db, key) {
            Entry::Vacant(vacant_entry) => (vacant_entry.insert(db, value).to_map(db), None),
            Entry::Occupied(occupied_entry) => {
                let (cursor, value) = occupied_entry.get().update(db, value);
                (cursor.to_map(db), Some(value))
            }
        }
    }

    #[salsa::tracked]
    pub fn remove(self, db: &'db dyn Database, key: Key) -> (Self, Option<Value>) {
        match self.entry(db, key) {
            Entry::Vacant(_) => (self, None),
            Entry::Occupied(occupied_entry) => {
                let (value, cursor) = occupied_entry.remove(db);
                (
                    cursor.map(|c| c.to_map(db)).unwrap_or_else(|| empty(db)),
                    Some(value),
                )
            }
        }
    }

    #[salsa::tracked]
    pub fn len(self, db: &'db dyn Database) -> usize {
        self.zipper(db).len(db)
    }

    #[salsa::tracked]
    pub fn is_empty(self, db: &'db dyn Database) -> bool {
        self.zipper(db).is_empty(db)
    }
}

impl<'db> Map<'db> {
    pub fn iter(self, db: &'db dyn Database) -> Iter<'db> {
        let zipper = self.zipper(db);
        match zipper.tree(db).node(db) {
            Node::Empty => Iter { cursor: None, db },
            Node::Inner { .. } => Iter {
                cursor: Some(leftmost(db, zipper)),
                db,
            },
            Node::Leaf { key, value } => Iter {
                cursor: Some(make_cursor(db, key, value, zipper.ctx(db))),
                db,
            },
        }
    }

    pub fn keys(self, db: &'db dyn Database) -> impl FusedIterator<Item = Key> {
        self.iter(db).map(|(k, _)| k)
    }

    pub fn values(self, db: &'db dyn Database) -> impl FusedIterator<Item = Value> {
        self.iter(db).map(|(_, v)| v)
    }
}

fn get_insert_position<'db>(
    db: &'db dyn Database,
    mut current: Zipper<'db>,
    critbit: u32,
) -> Zipper<'db> {
    // If the current zipper is already at the top of the tree then we just insert at the top.
    if current.ctx(db).elem(db) == Elem::Top {
        return current;
    }

    let mut parent = current.up(db);
    loop {
        match parent.tree(db).node(db) {
            Node::Inner { bitpos, .. } => {
                // If the critical bit position of the parent is smaller than the one we want
                // then we're done here.
                if bitpos < critbit {
                    return current;
                }
                // If we've reached the top of the tree then `parent` is the insert position.
                if parent.ctx(db).elem(db) == Elem::Top {
                    return parent;
                }

                current = parent;
                parent = parent.up(db);
            }
            Node::Empty | Node::Leaf { .. } => unreachable!(),
        }
    }
}

pub struct Iter<'db> {
    cursor: Option<Cursor<'db>>,
    db: &'db dyn Database,
}

impl<'db> Iterator for Iter<'db> {
    type Item = (Key, Value);

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.cursor.take()?;
        self.cursor = current.next(self.db);
        Some((current.key(self.db), current.value(self.db)))
    }
}

impl FusedIterator for Iter<'_> {}

#[cfg(test)]
mod tests {
    use super::*;

    use salsa::DatabaseImpl;

    fn check_critbit_is_sorted<'db>(
        db: &'db dyn Database,
        current: Zipper<'db>,
        last_bitpos: Option<u32>,
    ) {
        match current.tree(db).node(db) {
            Node::Empty => assert_eq!(Elem::Top, current.ctx(db).elem(db)),
            Node::Inner { bitpos, .. } => {
                if let Some(last) = last_bitpos {
                    assert!(last < bitpos);
                }
                check_critbit_is_sorted(db, current.left(db), Some(bitpos));
                check_critbit_is_sorted(db, current.right(db), Some(bitpos));
            }
            Node::Leaf { .. } => {}
        }
    }

    fn insert<'db>(
        db: &'db dyn Database,
        map: &mut Map<'db>,
        key: Key,
        value: Value,
    ) -> Option<Value> {
        let (m, v) = map.insert(db, key, value);
        *map = m;
        v
    }

    fn remove<'db>(db: &'db dyn Database, map: &mut Map<'db>, key: Key) -> Option<Value> {
        let (m, v) = map.remove(db, key);
        *map = m;
        v
    }

    fn sorted<T: Ord>(mut items: Vec<T>) -> Vec<T> {
        items.sort();
        items
    }

    #[test]
    fn test_basic_small() {
        let db = DatabaseImpl::new();
        let mut map = empty(&db);

        let key1 = Key::new(&db, 1);
        let value1 = Value::new(&db, 1);

        // Empty, root is absent (None):
        assert_eq!(remove(&db, &mut map, key1), None);
        assert_eq!(map.len(&db), 0);
        assert_eq!(map.get(&db, key1), None);
        // assert_eq!(map.get_mut(&db&1), None);
        // assert_eq!(map.first_key_value(&db), None);
        // assert_eq!(map.last_key_value(&db), None);
        assert_eq!(map.keys(&db).count(), 0);
        assert_eq!(map.values(&db).count(), 0);
        // assert_eq!(map.range(&db..).next(), None);
        // assert_eq!(map.range(&db..1).next(), None);
        // assert_eq!(map.range(&db1..).next(), None);
        // assert_eq!(map.range(&db1..=1).next(), None);
        // assert_eq!(map.range(&db1..2).next(), None);
        // assert_eq!(map.height(&db), None);
        assert_eq!(insert(&db, &mut map, key1, value1), None);
        // assert_eq!(map.height(&db), Some(0));
        check_critbit_is_sorted(&db, map.zipper(&db), None);

        // 1 key-value pair:
        assert_eq!(map.len(&db), 1);
        assert_eq!(map.get(&db, key1), Some(value1));
        // assert_eq!(map.get_mut(&db), Some(&mut 1));
        // assert_eq!(map.first_key_value(&db), Some((&1, &1)));
        // assert_eq!(map.last_key_value(&db), Some((&1, &1)));
        assert_eq!(sorted(map.keys(&db).collect::<Vec<_>>()), vec![key1]);
        assert_eq!(sorted(map.values(&db).collect::<Vec<_>>()), vec![value1]);

        let value2 = Value::new(&db, 2);
        assert_eq!(insert(&db, &mut map, key1, value2), Some(value1));
        assert_eq!(map.len(&db), 1);
        assert_eq!(map.get(&db, key1), Some(value2));
        // assert_eq!(map.get_mut(&db&1), Some(&mut 2));
        // assert_eq!(map.first_key_value(&db), Some((&1, &2)));
        // assert_eq!(map.last_key_value(&db), Some((&1, &2)));
        assert_eq!(sorted(map.keys(&db).collect::<Vec<_>>()), vec![key1]);
        assert_eq!(sorted(map.values(&db).collect::<Vec<_>>()), vec![value2]);

        let key2 = Key::new(&db, 2);
        let value4 = Value::new(&db, 4);
        assert_eq!(insert(&db, &mut map, key2, value4), None);
        // assert_eq!(map.height(&db), Some(0));
        check_critbit_is_sorted(&db, map.zipper(&db), None);

        // 2 key-value pairs:
        assert_eq!(map.len(&db), 2);
        assert_eq!(map.get(&db, key2), Some(value4));
        // assert_eq!(map.get_mut(&db&2), Some(&mut 4));
        // assert_eq!(map.first_key_value(&db), Some((&1, &2)));
        // assert_eq!(map.last_key_value(&db), Some((&2, &4)));
        assert_eq!(sorted(map.keys(&db).collect::<Vec<_>>()), vec![key1, key2]);
        assert_eq!(
            sorted(map.values(&db).collect::<Vec<_>>()),
            vec![value2, value4]
        );
        assert_eq!(remove(&db, &mut map, key1), Some(value2));
        // assert_eq!(map.height(&db), Some(0));
        check_critbit_is_sorted(&db, map.zipper(&db), None);

        // 1 key-value pair:
        assert_eq!(map.len(&db), 1);
        assert_eq!(map.get(&db, key1), None);
        // assert_eq!(map.get_mut(&db&1), None);
        assert_eq!(map.get(&db, key2), Some(value4));
        // assert_eq!(map.get_mut(&db&2), Some(&mut 4));
        // assert_eq!(map.first_key_value(&db), Some((&2, &4)));
        // assert_eq!(map.last_key_value(&db), Some((&2, &4)));
        assert_eq!(sorted(map.keys(&db).collect::<Vec<_>>()), vec![key2]);
        assert_eq!(sorted(map.values(&db).collect::<Vec<_>>()), vec![value4]);
        assert_eq!(remove(&db, &mut map, key2), Some(value4));
        // assert_eq!(map.height(&db), Some(0));
        check_critbit_is_sorted(&db, map.zipper(&db), None);

        // Empty but root is owned (Some(...)):
        assert_eq!(map.len(&db), 0);
        assert_eq!(map.get(&db, key1), None);
        // assert_eq!(map.get_mut(&db&1), None);
        // assert_eq!(map.first_key_value(&db), None);
        // assert_eq!(map.last_key_value(&db), None);
        assert_eq!(map.keys(&db).count(), 0);
        assert_eq!(map.values(&db).count(), 0);
        // assert_eq!(map.range(&db..).next(), None);
        // assert_eq!(map.range(&db..1).next(), None);
        // assert_eq!(map.range(&db1..).next(), None);
        // assert_eq!(map.range(&db1..=1).next(), None);
        // assert_eq!(map.range(&db1..2).next(), None);
        assert_eq!(remove(&db, &mut map, key1), None);
        // assert_eq!(map.height(&db), Some(0));
        check_critbit_is_sorted(&db, map.zipper(&db), None);
    }

    #[test]
    fn test_basic_large() {
        let db = DatabaseImpl::new();
        let mut map = empty(&db);

        // Miri is too slow
        // let size = if cfg!(miri) {
        //     MIN_INSERTS_HEIGHT_2
        // } else {
        //     10000
        // };
        let size = 100;
        assert_eq!(map.len(&db), 0);

        for i in 0..size {
            let key = Key::new(&db, i);
            let value = Value::new(&db, 10 * i);
            assert_eq!(insert(&db, &mut map, key, value), None);
            assert_eq!(map.len(&db) as u64, i + 1);
        }

        // assert_eq!(map.first_key_value(), Some((&0, &0)));
        // assert_eq!(
        //     map.last_key_value(),
        //     Some((&(size - 1), &(10 * (size - 1))))
        // );
        // assert_eq!(map.first_entry().unwrap().key(), &0);
        // assert_eq!(map.last_entry().unwrap().key(), &(size - 1));

        for (key, value) in map.iter(&db) {
            println!("key = {}, value = {}", key.k(&db), value.v(&db));
        }
        for i in 0..size {
            let key = Key::new(&db, i);
            assert_eq!(map.get(&db, key).unwrap().v(&db), i * 10);
        }

        for i in size..size * 2 {
            let key = Key::new(&db, i);
            assert_eq!(map.get(&db, key), None);
        }

        for i in 0..size {
            let key = Key::new(&db, i);
            let value = Value::new(&db, 100 * i);
            assert_eq!(insert(&db, &mut map, key, value).unwrap().v(&db), 10 * i);
            assert_eq!(map.len(&db) as u64, size);
        }

        for i in 0..size {
            let key = Key::new(&db, i);
            assert_eq!(map.get(&db, key).unwrap().v(&db), i * 100);
        }

        for i in 0..size / 2 {
            let key = Key::new(&db, i * 2);
            assert_eq!(remove(&db, &mut map, key).unwrap().v(&db), i * 200);
            assert_eq!(map.len(&db) as u64, size - i - 1);
        }

        for i in 0..size / 2 {
            let key = Key::new(&db, 2 * i);
            assert_eq!(map.get(&db, key), None);
            let key = Key::new(&db, 2 * i + 1);
            assert_eq!(map.get(&db, key).unwrap().v(&db), i * 200 + 100);
        }

        for i in 0..size / 2 {
            let key = Key::new(&db, 2 * i);
            assert_eq!(remove(&db, &mut map, key), None);
            let key = Key::new(&db, 2 * i + 1);
            assert_eq!(remove(&db, &mut map, key).unwrap().v(&db), i * 200 + 100);
            assert_eq!(map.len(&db) as u64, size / 2 - i - 1);
        }
        check_critbit_is_sorted(&db, map.zipper(&db), None);
    }
}
