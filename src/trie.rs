use std::collections::HashMap;

use crate::codec::{DataType, NodeCodec};
use crate::db::DB;
use crate::errors::TrieError;
use crate::nibbles::Nibbles;
use crate::node::{BranchNode, ExtensionNode, HashNode, LeafNode, Node};

pub type TrieResult<T, C, D> = Result<T, TrieError<C, D>>;

pub trait Trie<C: NodeCodec, D: DB> {
    /// returns the value for key stored in the trie.
    fn get(&self, key: &[u8]) -> TrieResult<Option<Vec<u8>>, C, D>;

    /// check that the key is present in the trie
    fn contains(&self, key: &[u8]) -> TrieResult<bool, C, D>;

    /// inserts value into trie and modifies it if it exists
    fn insert(&mut self, key: &[u8], value: &[u8]) -> TrieResult<(), C, D>;

    /// removes any existing value for key from the trie.
    fn remove(&mut self, key: &[u8]) -> TrieResult<bool, C, D>;

    /// returns the root hash of the trie.
    fn root(&mut self) -> TrieResult<C::Hash, C, D>;
}

#[derive(Debug)]
pub struct PatriciaTrie<'db, C, D>
where
    C: NodeCodec,
    D: DB,
{
    root: Node,
    db: &'db mut D,
    codec: C,

    cache: HashMap<C::Hash, Vec<u8>>,

    deleted_keys: Vec<C::Hash>,
}

impl<'db, C, D> Trie<C, D> for PatriciaTrie<'db, C, D>
where
    C: NodeCodec,
    D: DB,
{
    fn get(&self, key: &[u8]) -> TrieResult<Option<Vec<u8>>, C, D> {
        self.get_at(&self.root, &Nibbles::from_raw(key, true))
    }

    fn contains(&self, key: &[u8]) -> TrieResult<bool, C, D> {
        Ok(self
            .get_at(&self.root, &Nibbles::from_raw(key, true))?
            .map_or(false, |_| true))
    }

    fn insert(&mut self, key: &[u8], value: &[u8]) -> TrieResult<(), C, D> {
        let root = self.insert_at(self.root.clone(), &Nibbles::from_raw(key, true), value)?;
        self.root = root;
        Ok(())
    }

    fn remove(&mut self, key: &[u8]) -> TrieResult<bool, C, D> {
        let (n, removed) = self.delete_at(self.root.clone(), &Nibbles::from_raw(key, true))?;
        self.root = n;
        Ok(removed)
    }

    fn root(&mut self) -> TrieResult<C::Hash, C, D> {
        self.commit()
    }
}

impl<'db, C, D> PatriciaTrie<'db, C, D>
where
    C: NodeCodec,
    D: DB,
{
    pub fn new(db: &'db mut D, codec: C) -> Self {
        PatriciaTrie {
            root: Node::Empty,
            db,
            codec,

            cache: HashMap::new(),
            deleted_keys: vec![],
        }
    }

    pub fn from(db: &'db mut D, codec: C, root: &C::Hash) -> TrieResult<Self, C, D> {
        match db.get(root.as_ref()).map_err(TrieError::DB)? {
            Some(data) => {
                let mut trie = PatriciaTrie {
                    root: Node::Empty,
                    db,
                    codec,

                    cache: HashMap::new(),
                    deleted_keys: vec![],
                };

                trie.root = trie.decode_node(&data).map_err(TrieError::NodeCodec)?;
                Ok(trie)
            }
            None => Err(TrieError::InvalidStateRoot),
        }
    }

    fn get_at<'a>(&self, n: &'a Node, partial: &Nibbles) -> TrieResult<Option<Vec<u8>>, C, D> {
        match n {
            Node::Empty => Ok(None),
            Node::Leaf(ref leaf) => {
                if partial == leaf.get_key() {
                    Ok(Some(leaf.get_value().to_vec()))
                } else {
                    Ok(None)
                }
            }
            Node::Branch(ref branch) => {
                if partial.is_empty() || partial.at(0) == 16 {
                    Ok(branch.get_value().and_then(|v| Some(v.to_vec())))
                } else {
                    let index = partial.at(0) as usize;
                    let node = branch.at_children(index);
                    self.get_at(node, &partial.slice(1, partial.len()))
                }
            }
            Node::Extension(extension) => {
                let prefix = extension.get_prefix();
                let match_len = partial.common_prefix(prefix);
                if match_len == prefix.len() {
                    self.get_at(
                        extension.get_node(),
                        &partial.slice(match_len, partial.len()),
                    )
                } else {
                    Ok(None)
                }
            }
            Node::Hash(hash) => {
                let n = self.get_node_from_hash(hash.get_hash())?;
                self.get_at(&n, partial)
            }
        }
    }

    fn delete_at(&mut self, n: Node, partial: &Nibbles) -> TrieResult<(Node, bool), C, D> {
        match n {
            Node::Empty => Ok((Node::Empty, false)),
            Node::Leaf(leaf) => {
                if leaf.get_key() == partial {
                    Ok((Node::Empty, true))
                } else {
                    Ok((leaf.into_node(), false))
                }
            }
            Node::Branch(mut branch) => {
                if partial.is_empty() || partial.at(0) == 16 {
                    branch.set_value(None);
                    Ok((branch.into_node(), true))
                } else {
                    let index = partial.at(0) as usize;
                    let node = branch.at_children(index);
                    self.delete_at(node.clone(), &partial.slice(1, partial.len()))
                }
            }
            Node::Extension(extension) => {
                let prefix = extension.get_prefix();
                let match_len = partial.common_prefix(prefix);
                if match_len == prefix.len() {
                    self.delete_at(
                        extension.get_node().clone(),
                        &partial.slice(match_len, partial.len()),
                    )
                } else {
                    Ok((extension.into_node(), false))
                }
            }
            Node::Hash(hash) => {
                let (new_n, deleted) =
                    self.delete_at(self.get_node_from_hash(hash.get_hash())?, partial)?;
                if deleted {
                    self.deleted_keys
                        .push(self.codec.decode_hash(hash.get_hash(), true));
                }
                Ok((new_n, deleted))
            }
        }
    }

    fn insert_at(&mut self, n: Node, partial: &Nibbles, value: &[u8]) -> TrieResult<Node, C, D> {
        match n {
            Node::Empty => Ok(LeafNode::new(partial, value).into_node()),
            Node::Leaf(leaf) => {
                let old_partial = leaf.get_key();
                let match_index = partial.common_prefix(old_partial);
                if match_index == old_partial.len() {
                    // replace leaf value
                    return Ok(LeafNode::new(old_partial, value).into_node());
                }

                // create branch node
                let mut branch = BranchNode::new();
                let n = LeafNode::new(&partial.slice(match_index + 1, partial.len()), value)
                    .into_node();
                branch.insert(partial.at(match_index) as usize, n);

                let n = LeafNode::new(
                    &old_partial.slice(match_index + 1, old_partial.len()),
                    leaf.get_value(),
                )
                .into_node();
                branch.insert(old_partial.at(match_index) as usize, n);

                if match_index == 0 {
                    return Ok(branch.into_node());
                }

                // if include a common prefix
                Ok(
                    ExtensionNode::new(&partial.slice(0, match_index), branch.into_node())
                        .into_node(),
                )
            }
            Node::Branch(mut branch) => {
                if partial.is_empty() {
                    branch.set_value(Some(value.to_vec()));
                    Ok(branch.into_node())
                } else {
                    let index = partial.at(0) as usize;
                    let new_n = self.insert_at(
                        branch.at_children(index).clone(),
                        &partial.slice(1, partial.len()),
                        value,
                    )?;
                    branch.insert(index, new_n);
                    Ok(branch.into_node())
                }
            }
            Node::Extension(extension) => {
                let prefix = extension.get_prefix();
                let match_index = partial.common_prefix(&prefix);

                if match_index == 0 {
                    // Don't match, create a branch node.
                    self.insert_at(Node::Empty, partial, value)
                } else if match_index == prefix.len() {
                    let new_node = self.insert_at(
                        extension.get_node().clone(),
                        &partial.slice(match_index, partial.len()),
                        value,
                    )?;

                    Ok(ExtensionNode::new(prefix, new_node).into_node())
                } else {
                    let new_ext = ExtensionNode::new(
                        &prefix.slice(match_index, prefix.len()),
                        extension.get_node().clone(),
                    );

                    let new_n = self.insert_at(
                        new_ext.into_node(),
                        &partial.slice(match_index, partial.len()),
                        value,
                    )?;

                    Ok(ExtensionNode::new(&prefix.slice(0, match_index), new_n).into_node())
                }
            }
            Node::Hash(hash) => {
                let n = self.get_node_from_hash(hash.get_hash())?;
                self.insert_at(n, partial, value)
            }
        }
    }

    fn commit(&mut self) -> TrieResult<C::Hash, C, D> {
        let encoded = self.encode_node(&self.root.clone());
        let root_hash = if encoded.len() < C::HASH_LENGTH {
            let hash = self.codec.decode_hash(&encoded, false);
            self.cache.insert(hash.clone(), encoded);
            hash
        } else {
            self.codec.decode_hash(&encoded, true)
        };

        // TODO: batch operation
        for (k, v) in self.cache.drain() {
            self.db.insert(k.as_ref(), &v).map_err(TrieError::DB)?;
        }

        for key in self.deleted_keys.drain(..) {
            self.db.remove(key.as_ref()).map_err(TrieError::DB)?;
        }

        Ok(root_hash)
    }

    fn decode_node(&self, data: &[u8]) -> Result<Node, C::Error> {
        self.codec.decode(data, |dp| match dp {
            DataType::Empty => Ok(Node::Empty),
            DataType::Pair(key, value) => {
                let nibble = Nibbles::from_compact(key);
                if nibble.is_leaf() {
                    Ok(LeafNode::new(&nibble, value).into_node())
                } else {
                    let n = self.try_decode_hash_node(value)?;;
                    Ok(ExtensionNode::new(&nibble, n).into_node())
                }
            }
            DataType::Values(values) => {
                let mut branch = BranchNode::new();
                for (index, item) in values.iter().enumerate().take(16) {
                    let n = self.try_decode_hash_node(item)?;
                    branch.insert(index, n);
                }

                if self.codec.encode_empty() == values[16] {
                    branch.set_value(None)
                } else {
                    branch.set_value(Some(values[16].to_vec()))
                }
                Ok(branch.into_node())
            }
        })
    }

    fn encode_node(&mut self, n: &Node) -> Vec<u8> {
        let data = match n {
            Node::Empty => self.codec.encode_empty(),
            Node::Leaf(ref leaf) => self
                .codec
                .encode_pair(&leaf.get_key().encode_compact(), leaf.get_value()),
            Node::Branch(branch) => {
                let mut values = vec![];
                for index in 0..16 {
                    let data = self.encode_node(branch.at_children(index));
                    values.push(data);
                }
                match branch.get_value() {
                    Some(v) => values.push(v.to_vec()),
                    None => values.push(self.codec.encode_empty()),
                }
                self.codec.encode_values(&values)
            }
            Node::Extension(extension) => {
                let key = extension.get_prefix().encode_compact();
                let value = self.encode_node(extension.get_node());

                self.codec.encode_pair(&key, &value)
            }
            Node::Hash(hash) => hash.get_hash().to_vec(),
        };

        // Nodes smaller than 32 bytes are stored inside their parent,
        // Nodes equal to 32 bytes are returned directly
        if data.len() < C::HASH_LENGTH || data.len() == C::HASH_LENGTH {
            data
        } else {
            let hash = self.codec.decode_hash(&data, false);
            self.cache.insert(hash.clone(), data);
            Vec::from(hash.as_ref())
        }
    }

    fn try_decode_hash_node(&self, data: &[u8]) -> Result<Node, C::Error> {
        if data.len() == C::HASH_LENGTH {
            Ok(HashNode::new(data).into_node())
        } else {
            self.decode_node(data)
        }
    }

    fn get_node_from_hash(&self, hash: &[u8]) -> TrieResult<Node, C, D> {
        match self.db.get(hash).map_err(TrieError::DB)? {
            Some(data) => self.decode_node(&data).map_err(TrieError::NodeCodec),
            None => Ok(Node::Empty),
        }
    }
}

#[cfg(test)]
mod tests {
    use hex::FromHex;
    use rand::distributions::Alphanumeric;
    use rand::{thread_rng, Rng};

    use super::{PatriciaTrie, Trie};
    use crate::codec::{NodeCodec, RLPNodeCodec};
    use crate::db::MemoryDB;

    #[test]
    fn test_trie_insert() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
        trie.insert(b"test", b"test").unwrap();
    }

    #[test]
    fn test_trie_get() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
        trie.insert(b"test", b"test").unwrap();
        let v = trie.get(b"test").unwrap().map(|v| v.to_vec());

        assert_eq!(Some(b"test".to_vec()), v)
    }

    #[test]
    fn test_trie_random_insert() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());

        for _ in 0..1000 {
            let rand_str: String = thread_rng().sample_iter(&Alphanumeric).take(30).collect();
            let val = rand_str.as_bytes();
            trie.insert(val, val).unwrap();

            let v = trie.get(val).unwrap();
            assert_eq!(v.map(|v| v.to_vec()), Some(val.to_vec()));
        }
    }

    #[test]
    fn test_trie_contains() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
        trie.insert(b"test", b"test").unwrap();
        assert_eq!(true, trie.contains(b"test").unwrap());
        assert_eq!(false, trie.contains(b"test2").unwrap());
    }

    #[test]
    fn test_trie_remove() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
        trie.insert(b"test", b"test").unwrap();
        let removed = trie.remove(b"test").unwrap();
        assert_eq!(true, removed)
    }

    #[test]
    fn test_trie_random_remove() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());

        for _ in 0..1000 {
            let rand_str: String = thread_rng().sample_iter(&Alphanumeric).take(30).collect();
            let val = rand_str.as_bytes();
            trie.insert(val, val).unwrap();

            let removed = trie.remove(val).unwrap();
            assert_eq!(true, removed);
        }
    }

    #[test]
    fn test_trie_empty_commit() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());

        let codec = RLPNodeCodec::default();
        let empty_node_data = codec.decode_hash(&codec.encode_empty(), false);
        let root = trie.commit().unwrap();

        assert_eq!(hex::encode(root), hex::encode(empty_node_data))
    }

    #[test]
    fn test_trie_commit() {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
        trie.insert(b"test", b"test").unwrap();
        let root = trie.commit().unwrap();

        let codec = RLPNodeCodec::default();
        let empty_node_data = codec.decode_hash(&codec.encode_empty(), false);
        assert_ne!(hex::encode(root), hex::encode(empty_node_data))
    }

    #[test]
    fn test_trie_from_root() {
        let mut memdb = MemoryDB::new();
        let root = {
            let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
            trie.insert(b"test", b"test").unwrap();
            trie.insert(b"test1", b"test").unwrap();
            trie.insert(b"test2", b"test").unwrap();
            trie.insert(b"test23", b"test").unwrap();
            trie.insert(b"test33", b"test").unwrap();
            trie.insert(b"test44", b"test").unwrap();
            trie.root().unwrap()
        };

        let mut trie = PatriciaTrie::from(&mut memdb, RLPNodeCodec::default(), &root).unwrap();
        let v1 = trie.get(b"test33").unwrap();
        assert_eq!(Some(b"test".to_vec()), v1);
        let v2 = trie.get(b"test44").unwrap();
        assert_eq!(Some(b"test".to_vec()), v2);
        let root2 = trie.commit().unwrap();
        assert_eq!(hex::encode(root), hex::encode(root2));
    }

    #[test]
    fn test_trie_from_root_and_insert() {
        let mut memdb = MemoryDB::new();
        let root = {
            let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
            trie.insert(b"test", b"test").unwrap();
            trie.insert(b"test1", b"test").unwrap();
            trie.insert(b"test2", b"test").unwrap();
            trie.insert(b"test23", b"test").unwrap();
            trie.insert(b"test33", b"test").unwrap();
            trie.insert(b"test44", b"test").unwrap();
            trie.commit().unwrap()
        };

        let mut trie = PatriciaTrie::from(&mut memdb, RLPNodeCodec::default(), &root).unwrap();
        trie.insert(b"test55", b"test55").unwrap();
        let v = trie.get(b"test55").unwrap();
        assert_eq!(Some(b"test55".to_vec()), v);
    }

    #[test]
    fn test_trie_from_root_and_delete() {
        let mut memdb = MemoryDB::new();
        let root = {
            let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
            trie.insert(b"test", b"test").unwrap();
            trie.insert(b"test1", b"test").unwrap();
            trie.insert(b"test2", b"test").unwrap();
            trie.insert(b"test23", b"test").unwrap();
            trie.insert(b"test33", b"test").unwrap();
            trie.insert(b"test44", b"test").unwrap();
            trie.commit().unwrap()
        };

        let mut trie = PatriciaTrie::from(&mut memdb, RLPNodeCodec::default(), &root).unwrap();
        let removed = trie.remove(b"test44").unwrap();
        assert_eq!(true, removed);
    }

    fn assert_root(data: Vec<(&[u8], &[u8])>, hash: &str) {
        let mut memdb = MemoryDB::new();
        let mut trie = PatriciaTrie::new(&mut memdb, RLPNodeCodec::default());
        for (k, v) in data.iter() {
            trie.insert(k, v).unwrap();
        }
        let r = format!("0x{}", hex::encode(trie.root().unwrap()));
        assert_eq!(r.as_str(), hash);
    }

    #[test]
    fn test_root() {
        // See: https://github.com/ethereum/tests/blob/develop/TrieTests
        // Copy from trietest.json and trieanyorder.json
        assert_root(
            vec![(b"A", b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")],
            "0xd23786fb4a010da3ce639d66d5e904a11dbc02746d1ce25029e53290cabf28ab",
        );
        assert_root(
            vec![
                (b"doe", b"reindeer"),
                (b"dog", b"puppy"),
                (b"dogglesworth", b"cat"),
            ],
            "0x8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3",
        );
        assert_root(
            vec![
                (b"do", b"verb"),
                (b"horse", b"stallion"),
                (b"doge", b"coin"),
                (b"dog", b"puppy"),
            ],
            "0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84",
        );
        assert_root(
            vec![(b"foo", b"bar"), (b"food", b"bass")],
            "0x17beaa1648bafa633cda809c90c04af50fc8aed3cb40d16efbddee6fdf63c4c3",
        );

        assert_root(
            vec![(b"be", b"e"), (b"dog", b"puppy"), (b"bed", b"d")],
            "0x3f67c7a47520f79faa29255d2d3c084a7a6df0453116ed7232ff10277a8be68b",
        );
        assert_root(
            vec![(b"test", b"test"), (b"te", b"testy")],
            "0x8452568af70d8d140f58d941338542f645fcca50094b20f3c3d8c3df49337928",
        );
        assert_root(
            vec![
                (
                    Vec::from_hex("0045").unwrap().as_slice(),
                    Vec::from_hex("0123456789").unwrap().as_slice(),
                ),
                (
                    Vec::from_hex("4500").unwrap().as_slice(),
                    Vec::from_hex("9876543210").unwrap().as_slice(),
                ),
            ],
            "0x285505fcabe84badc8aa310e2aae17eddc7d120aabec8a476902c8184b3a3503",
        );
        assert_root(
            vec![
                (b"do", b"verb"),
                (b"ether", b"wookiedoo"),
                (b"horse", b"stallion"),
                (b"shaman", b"horse"),
                (b"doge", b"coin"),
                (b"ether", b""),
                (b"dog", b"puppy"),
                (b"shaman", b""),
            ],
            "0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84",
        );
        assert_root(
            vec![
                (b"do", b"verb"),
                (b"ether", b"wookiedoo"),
                (b"horse", b"stallion"),
                (b"shaman", b"horse"),
                (b"doge", b"coin"),
                (b"ether", b""),
                (b"dog", b"puppy"),
                (b"shaman", b""),
            ],
            "0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84",
        );
        assert_root(
            vec![
                (
                    Vec::from_hex("04110d816c380812a427968ece99b1c963dfbce6")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("095e7baea6a6c7c4c2dfeb977efac326af552d87")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("0a517d755cebbf66312b30fff713666a9cb917e0")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("24dd378f51adc67a50e339e8031fe9bd4aafab36")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("293f982d000532a7861ab122bdc4bbfd26bf9030")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("2cf5732f017b0cf1b1f13a1478e10239716bf6b5")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("31c640b92c21a1f1465c91070b4b3b4d6854195f")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("37f998764813b136ddf5a754f34063fd03065e36")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("37fa399a749c121f8a15ce77e3d9f9bec8020d7a")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("4f36659fa632310b6ec438dea4085b522a2dd077")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("62c01474f089b07dae603491675dc5b5748f7049")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("729af7294be595a0efd7d891c9e51f89c07950c7")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("83e3e5a16d3b696a0314b30b2534804dd5e11197")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("8703df2417e0d7c59d063caa9583cb10a4d20532")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("8dffcd74e5b5923512916c6a64b502689cfa65e1")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("95a4d7cccb5204733874fa87285a176fe1e9e240")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("99b2fcba8120bedd048fe79f5262a6690ed38c39")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("a4202b8b8afd5354e3e40a219bdc17f6001bf2cf")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("a94f5374fce5edbc8e2a8697c15331677e6ebf0b")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("a9647f4a0a14042d91dc33c0328030a7157c93ae")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("aa6cffe5185732689c18f37a7f86170cb7304c2a")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("aae4a2e3c51c04606dcb3723456e58f3ed214f45")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("c37a43e940dfb5baf581a0b82b351d48305fc885")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("d2571607e241ecf590ed94b12d87c94babe36db6")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("f735071cbee190d76b704ce68384fc21e389fbe7")
                        .unwrap()
                        .as_slice(),
                    b"something",
                ),
                (
                    Vec::from_hex("04110d816c380812a427968ece99b1c963dfbce6")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("095e7baea6a6c7c4c2dfeb977efac326af552d87")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("0a517d755cebbf66312b30fff713666a9cb917e0")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("24dd378f51adc67a50e339e8031fe9bd4aafab36")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("293f982d000532a7861ab122bdc4bbfd26bf9030")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("2cf5732f017b0cf1b1f13a1478e10239716bf6b5")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("31c640b92c21a1f1465c91070b4b3b4d6854195f")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("37f998764813b136ddf5a754f34063fd03065e36")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("37fa399a749c121f8a15ce77e3d9f9bec8020d7a")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("4f36659fa632310b6ec438dea4085b522a2dd077")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("62c01474f089b07dae603491675dc5b5748f7049")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("729af7294be595a0efd7d891c9e51f89c07950c7")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("83e3e5a16d3b696a0314b30b2534804dd5e11197")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("8703df2417e0d7c59d063caa9583cb10a4d20532")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("8dffcd74e5b5923512916c6a64b502689cfa65e1")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("95a4d7cccb5204733874fa87285a176fe1e9e240")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("99b2fcba8120bedd048fe79f5262a6690ed38c39")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("a4202b8b8afd5354e3e40a219bdc17f6001bf2cf")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("a94f5374fce5edbc8e2a8697c15331677e6ebf0b")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("a9647f4a0a14042d91dc33c0328030a7157c93ae")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("aa6cffe5185732689c18f37a7f86170cb7304c2a")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("aae4a2e3c51c04606dcb3723456e58f3ed214f45")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("c37a43e940dfb5baf581a0b82b351d48305fc885")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("d2571607e241ecf590ed94b12d87c94babe36db6")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
                (
                    Vec::from_hex("f735071cbee190d76b704ce68384fc21e389fbe7")
                        .unwrap()
                        .as_slice(),
                    b"",
                ),
            ],
            "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421",
        );
        assert_root(
            vec![
                (
                    Vec::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000045",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex("22b224a1420a802ab51d326e29fa98e34c4f24ea")
                        .unwrap()
                        .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000046",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex(
                        "67706c2076330000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap()
                    .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "0000000000000000000000000000000000000000000000000000001234567890",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex("697c7b8c961b56f675d570498424ac8de1a918f6")
                        .unwrap()
                        .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex("1234567890").unwrap().as_slice(),
                ),
                (
                    Vec::from_hex(
                        "0000000000000000000000007ef9e639e2733cb34e4dfc576d4b23f72db776b2",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex(
                        "4655474156000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap()
                    .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "000000000000000000000000ec4f34c97e43fbb2816cfd95e388353c7181dab1",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex(
                        "4e616d6552656700000000000000000000000000000000000000000000000000",
                    )
                    .unwrap()
                    .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "4655474156000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex("7ef9e639e2733cb34e4dfc576d4b23f72db776b2")
                        .unwrap()
                        .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "4e616d6552656700000000000000000000000000000000000000000000000000",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex("ec4f34c97e43fbb2816cfd95e388353c7181dab1")
                        .unwrap()
                        .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "0000000000000000000000000000000000000000000000000000001234567890",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex("").unwrap().as_slice(),
                ),
                (
                    Vec::from_hex(
                        "000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex(
                        "6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000",
                    )
                    .unwrap()
                    .as_slice(),
                ),
                (
                    Vec::from_hex(
                        "6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000",
                    )
                    .unwrap()
                    .as_slice(),
                    Vec::from_hex("697c7b8c961b56f675d570498424ac8de1a918f6")
                        .unwrap()
                        .as_slice(),
                ),
            ],
            "0x9f6221ebb8efe7cff60a716ecb886e67dd042014be444669f0159d8e68b42100",
        );
        assert_root(
            vec![
                (b"key1aa", b"0123456789012345678901234567890123456789xxx"),
                (
                    b"key1",
                    b"0123456789012345678901234567890123456789Very_Long",
                ),
                (b"key2bb", b"aval3"),
                (b"key2", b"short"),
                (b"key3cc", b"aval3"),
                (b"key3", b"1234567890123456789012345678901"),
            ],
            "0xcb65032e2f76c48b82b5c24b3db8f670ce73982869d38cd39a624f23d62a9e89",
        );
        assert_root(
            vec![(b"abc", b"123"), (b"abcd", b"abcd"), (b"abc", b"abc")],
            "0x7a320748f780ad9ad5b0837302075ce0eeba6c26e3d8562c67ccc0f1b273298a",
        );
    }
}
