use bytemuck::{Pod, Zeroable};
use std::cmp::max;

// Constant to represent an empty value.
const SENTINEL: u32 = 0;

// Enum representing the fields of a node.
#[derive(Copy, Clone)]
enum Register {
    Left,
    Right,
    Height,
}

// Enum representing the fields of the allocator.
enum Field {
    Root,
    Size,
    Capacity,
    FreeListHead,
    Sequence,
}

/// Macro to access a node.
macro_rules! node {
    ( $array:expr, $index:expr ) => {
        $array[($index - 1) as usize]
    };
}

// Type representing a path entry (parent, branch, child) when
// traversing the tree.
type Ancestor = (Option<u32>, Option<Register>, u32);

/// AVL tree struct, which is a self-balancing binary search tree. Values in the
/// tree are stored as such the height of two sibling subtrees differ by one at
/// most.
///
/// This type can be used to reference a read-only tree.
pub struct AVLTree<
    'a,
    K: PartialOrd + Default + Copy + Clone + Pod + Zeroable,
    V: Default + Copy + Clone + Pod + Zeroable,
> {
    /// Node allocator.
    allocator: &'a Allocator,

    /// Array of nodes to store the tree.
    nodes: &'a [Node<K, V>],
}

impl<
        'a,
        K: PartialOrd + Default + Copy + Clone + Pod + Zeroable,
        V: Default + Copy + Clone + Pod + Zeroable,
    > AVLTree<'a, K, V>
{
    /// Returns the required data length (in bytes) to store a tree with the specified capacity.
    pub const fn data_len(capacity: usize) -> usize {
        std::mem::size_of::<Allocator>() + (capacity * std::mem::size_of::<Node<K, V>>())
    }

    /// Loads a tree from a byte array.
    pub fn from_bytes(bytes: &'a [u8]) -> Self {
        let (allocator, nodes) = bytes.split_at(std::mem::size_of::<Allocator>());

        let allocator = bytemuck::from_bytes::<Allocator>(allocator);
        let nodes = bytemuck::cast_slice(nodes);

        Self { allocator, nodes }
    }

    /// Returns the capacity of the tree.
    pub fn capacity(&self) -> usize {
        self.allocator.get_field(Field::Capacity) as usize
    }

    /// Returns the number of nodes in the tree.
    pub fn len(&self) -> usize {
        self.allocator.get_field(Field::Size) as usize
    }

    /// Indicates whether the tree is full or not.
    pub fn is_full(&self) -> bool {
        self.allocator.get_field(Field::Size) >= self.allocator.get_field(Field::Capacity)
    }

    /// Indicates whether the tree is empty or not.
    pub fn is_empty(&self) -> bool {
        self.allocator.get_field(Field::Size) == 0
    }

    /// Return the value under the specified key, if one is found.
    ///
    /// # Arguments
    ///
    /// * `key` - key to look up the value.
    pub fn get(&self, key: &K) -> Option<V> {
        self.find(key)
            .map(|node_index| node!(self.nodes, node_index).value)
    }

    // Find the lowest entry.
    pub fn lowest(&self) -> Option<K> {
        let mut node = self.allocator.get_field(Field::Root);

        if node == SENTINEL {
            return None;
        }

        while node!(self.nodes, node).get_register(Register::Left) != SENTINEL {
            node = node!(self.nodes, node).get_register(Register::Left);
        }

        Some(node!(self.nodes, node).key)
    }

    /// Checks whether a key is present in the tree or not.
    ///
    /// # Arguments
    ///
    /// * `key` - the key of the node.
    pub fn contains(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    fn find(&self, key: &K) -> Option<u32> {
        let mut reference_node = self.allocator.get_field(Field::Root);

        while reference_node != SENTINEL {
            let current = node!(self.nodes, reference_node).key;

            let target = if *key < current {
                node!(self.nodes, reference_node).get_register(Register::Left)
            } else if *key > current {
                node!(self.nodes, reference_node).get_register(Register::Right)
            } else {
                return Some(reference_node);
            };

            reference_node = target;
        }

        None
    }
}

/// AVL tree struct, which is a self-balancing binary search tree. Values in the
/// tree are stored as such the height of two sibling subtrees differ by one at
/// most.
///
/// This type can be used to reference a writable tree.
pub struct AVLTreeMut<
    'a,
    K: PartialOrd + Default + Copy + Clone + Pod + Zeroable,
    V: Default + Copy + Clone + Pod + Zeroable,
> {
    /// Node allocator.
    allocator: &'a mut Allocator,

    /// Array of nodes to store the tree.
    nodes: &'a mut [Node<K, V>],
}

impl<
        'a,
        K: PartialOrd + Default + Copy + Clone + Pod + Zeroable,
        V: Default + Copy + Clone + Pod + Zeroable,
    > AVLTreeMut<'a, K, V>
{
    /// Returns the required data length (in bytes) to store a tree with the specified capacity.
    pub const fn data_len(capacity: usize) -> usize {
        std::mem::size_of::<Allocator>() + (capacity * std::mem::size_of::<Node<K, V>>())
    }

    /// Loads a tree from a byte array.
    pub fn from_bytes_mut(bytes: &'a mut [u8]) -> Self {
        let (allocator, nodes) = bytes.split_at_mut(std::mem::size_of::<Allocator>());

        let allocator = bytemuck::from_bytes_mut::<Allocator>(allocator);
        let nodes = bytemuck::cast_slice_mut(nodes);

        Self { allocator, nodes }
    }

    /// Initializes the tree with the specified capacity.
    ///
    /// This function should be called once when the tree is created.
    pub fn initialize(&mut self, capacity: u32) {
        self.allocator.initialize(capacity)
    }

    /// Returns the capacity of the tree.
    pub fn capacity(&self) -> usize {
        self.allocator.get_field(Field::Capacity) as usize
    }

    /// Returns the number of nodes in the tree.
    pub fn len(&self) -> usize {
        self.allocator.get_field(Field::Size) as usize
    }

    /// Indicates whether the tree is full or not.
    pub fn is_full(&self) -> bool {
        self.allocator.get_field(Field::Size) >= self.allocator.get_field(Field::Capacity)
    }

    /// Indicates whether the tree is empty or not.
    pub fn is_empty(&self) -> bool {
        self.allocator.get_field(Field::Size) == 0
    }

    /// Return the value under the specified key, if one is found.
    ///
    /// # Arguments
    ///
    /// * `key` - key to look up the value.
    pub fn get(&self, key: &K) -> Option<V> {
        self.find(key)
            .map(|node_index| node!(self.nodes, node_index).value)
    }

    /// Return a mutable reference to the  value under the specified key, if one is found.
    ///
    /// # Arguments
    ///
    /// * `key` - key to look up the value.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.find(key)
            .map(|node_index| &mut node!(self.nodes, node_index).value)
    }

    /// Insert a value on the tree at the specified key.
    ///
    /// The value is inserted in the tree maintaining the natural order based on
    /// its key value.
    ///
    /// # Arguments
    ///
    /// * `key` - the key of the node.
    /// • `value` - the value of the node.
    pub fn insert(&mut self, key: K, value: V) -> Option<u32> {
        let mut reference_node = self.allocator.get_field(Field::Root);

        if reference_node == SENTINEL {
            let root = self.add(key, value);
            self.allocator.set_field(Field::Root, root);
            return Some(root);
        }

        let mut path: Vec<Ancestor> = Vec::with_capacity((self.len() as f64).log2() as usize);
        path.push((None, None, reference_node));

        loop {
            let current_key = node!(self.nodes, reference_node).key;
            let parent = reference_node;

            let branch = if key < current_key {
                reference_node = node!(self.nodes, parent).get_register(Register::Left);
                Register::Left
            } else if key > current_key {
                reference_node = node!(self.nodes, parent).get_register(Register::Right);
                Register::Right
            } else {
                return None;
            };

            if reference_node == SENTINEL {
                if self.is_full() {
                    return None;
                }

                reference_node = self.add(key, value);
                self.update_child(parent, branch, reference_node);

                break;
            } else {
                path.push((Some(parent), Some(branch), reference_node));
            }
        }

        self.rebalance(path);

        Some(reference_node)
    }

    /// Removes a node from the tree specified key.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let mut node_index = self.allocator.get_field(Field::Root);

        if node_index == SENTINEL {
            return None;
        }

        let mut path: Vec<Ancestor> = Vec::with_capacity((self.len() as f64).log2() as usize);
        path.push((None, None, node_index));

        while node_index != SENTINEL {
            let current_key = node!(self.nodes, node_index).key;
            let parent = node_index;

            let branch = if *key < current_key {
                node_index = node!(self.nodes, parent).get_register(Register::Left);
                Register::Left
            } else if *key > current_key {
                node_index = node!(self.nodes, parent).get_register(Register::Right);
                Register::Right
            } else {
                break;
            };

            path.push((Some(parent), Some(branch), node_index));
        }
        // sanity check: the loop should be stopped by the break statement
        // (node_index == SENTINEL indicates that the key was not found)
        if node_index == SENTINEL {
            return None;
        }

        let left = node!(self.nodes, node_index).get_register(Register::Left);
        let right = node!(self.nodes, node_index).get_register(Register::Right);

        let replacement = if left != SENTINEL && right != SENTINEL {
            let mut leftmost = right;
            let mut leftmost_parent = SENTINEL;
            // path to the leftmost descendant
            let mut inner_path = Vec::with_capacity((self.len() as f64).log2() as usize);

            while node!(self.nodes, leftmost).get_register(Register::Left) != SENTINEL {
                leftmost_parent = leftmost;
                leftmost = node!(self.nodes, leftmost).get_register(Register::Left);
                inner_path.push((Some(leftmost_parent), Some(Register::Left), leftmost));
            }

            if leftmost_parent != SENTINEL {
                self.update_child(
                    leftmost_parent,
                    Register::Left,
                    node!(self.nodes, leftmost).get_register(Register::Right),
                );
            }

            self.update_child(leftmost, Register::Left, left);

            if right != leftmost {
                self.update_child(leftmost, Register::Right, right);
            }

            let (parent, branch, _) = path.pop().unwrap();

            if let Some(parent) = parent {
                self.update_child(parent, branch.expect("invalid tree structure"), leftmost);
            }

            path.push((parent, branch, leftmost));
            if right != leftmost {
                path.push((Some(leftmost), Some(Register::Right), right));
            }
            // drop the last inner_path element since it references the leftmost node
            if !inner_path.is_empty() {
                inner_path.pop();
            }
            path.extend(inner_path);

            leftmost
        } else {
            let child = if left == SENTINEL && right == SENTINEL {
                SENTINEL
            } else if left != SENTINEL {
                left
            } else {
                right
            };

            let (parent, branch, _) = path.pop().unwrap();

            if let Some(parent) = parent {
                self.update_child(parent, branch.expect("invalid tree structure"), child);

                if child != SENTINEL {
                    path.push((Some(parent), branch, child));
                }
            }

            child
        };

        if node_index == self.allocator.get_field(Field::Root) {
            self.allocator.set_field(Field::Root, replacement);
        }

        self.rebalance(path);
        // clears the node information
        self.remove_node(node_index)
    }

    // Find the lowest entry.
    pub fn lowest(&self) -> Option<K> {
        let mut node = self.allocator.get_field(Field::Root);

        if node == SENTINEL {
            return None;
        }

        while node!(self.nodes, node).get_register(Register::Left) != SENTINEL {
            node = node!(self.nodes, node).get_register(Register::Left);
        }

        Some(node!(self.nodes, node).key)
    }

    /// Checks whether a key is present in the tree or not.
    ///
    /// # Arguments
    ///
    /// * `key` - the key of the node.
    pub fn contains(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    fn find(&self, key: &K) -> Option<u32> {
        let mut reference_node = self.allocator.get_field(Field::Root);

        while reference_node != SENTINEL {
            let current = node!(self.nodes, reference_node).key;

            let target = if *key < current {
                node!(self.nodes, reference_node).get_register(Register::Left)
            } else if *key > current {
                node!(self.nodes, reference_node).get_register(Register::Right)
            } else {
                return Some(reference_node);
            };

            reference_node = target;
        }

        None
    }

    /// Adds a node to the tree.
    ///
    /// The node is only added if there is space on the tree.
    ///
    /// # Arguments
    ///
    /// * `key` - the key of the node.
    /// * `value` - the value of the node.
    fn add(&mut self, key: K, value: V) -> u32 {
        let free_node = self.allocator.get_field(Field::FreeListHead);
        let sequence = self.allocator.get_field(Field::Sequence);

        if free_node == sequence {
            if (sequence - 1) == self.allocator.get_field(Field::Capacity) {
                panic!(
                    "tree is full ({} nodes)",
                    self.allocator.get_field(Field::Size)
                );
            }

            self.allocator.set_field(Field::Sequence, sequence + 1);
            self.allocator.set_field(Field::FreeListHead, sequence + 1);
        } else {
            self.allocator.set_field(
                Field::FreeListHead,
                node!(self.nodes, free_node).get_register(Register::Height),
            );
        }

        let entry = &mut node!(self.nodes, free_node);

        entry.key = key;
        entry.value = value;
        // the height field is used to store the free list head, so we make
        // sure we reset its value
        entry.set_register(Register::Height, 0);

        self.allocator
            .set_field(Field::Size, self.allocator.get_field(Field::Size) + 1);

        free_node
    }

    /// Rebalances the tree to maintain the AVL rule.
    ///
    /// The AVL rule maintains the difference in height of two sibling subtrees by one at most. While
    /// this increases the computational time of insert operations, it provides faster lookup times.
    ///
    /// # Arguments
    ///
    /// * `path` - path to rebalance. The path is visited in reverse order.
    fn rebalance(&mut self, path: Vec<Ancestor>) {
        for (parent, branch, child) in path.iter().rev() {
            let left = node!(self.nodes, *child).get_register(Register::Left);
            let right = node!(self.nodes, *child).get_register(Register::Right);

            let balance_factor = self.balance_factor(left, right);

            let index = if balance_factor > 1 {
                let left_left = node!(self.nodes, left).get_register(Register::Left);
                let left_right = node!(self.nodes, left).get_register(Register::Right);
                let left_balance_factor = self.balance_factor(left_left, left_right);

                if left_balance_factor < 0 {
                    let index = self.left_rotate(left);
                    self.update_child(*child, Register::Left, index);
                }
                Some(self.right_rotate(*child))
            } else if balance_factor < -1 {
                let right_left = node!(self.nodes, right).get_register(Register::Left);
                let right_right = node!(self.nodes, right).get_register(Register::Right);
                let right_balance_factor = self.balance_factor(right_left, right_right);

                if right_balance_factor > 0 {
                    let index = self.right_rotate(right);
                    self.update_child(*child, Register::Right, index);
                }
                Some(self.left_rotate(*child))
            } else {
                self.update_height(*child);
                None
            };

            if let Some(index) = index {
                if let Some(parent) = parent {
                    self.update_child(*parent, branch.expect("invalid tree structure"), index);
                } else {
                    self.allocator.set_field(Field::Root, index);
                    self.update_height(index);
                }
            }
        }
    }

    /// Calculate the balance factor of a node.
    ///
    /// The balance factor is determined by the difference between the height
    /// of its left and right children subtrees.
    ///
    /// # Arguments
    ///
    /// * `left` - index of the left child.
    /// * `right` - index of the right child.
    fn balance_factor(&self, left: u32, right: u32) -> i32 {
        // safe to convert to i32 since height will be at most log2(capacity)
        let left_height = if left != SENTINEL {
            node!(self.nodes, left).get_register(Register::Height) as i32 + 1
        } else {
            0
        };
        let right_height = if right != SENTINEL {
            node!(self.nodes, right).get_register(Register::Height) as i32 + 1
        } else {
            0
        };

        left_height - right_height
    }

    /// Perform a left AVL rotation.
    ///
    /// # Arguments
    ///
    /// * `index` - index of the unballanced node.
    fn left_rotate(&mut self, index: u32) -> u32 {
        let right = node!(self.nodes, index).get_register(Register::Right);
        let right_left = node!(self.nodes, right).get_register(Register::Left);

        self.update_child(index, Register::Right, right_left);
        self.update_child(right, Register::Left, index);

        right
    }

    /// Perform a right AVL rotation.
    ///
    /// # Arguments
    ///
    /// * `index` - index of the unballanced node.
    fn right_rotate(&mut self, index: u32) -> u32 {
        let left = node!(self.nodes, index).get_register(Register::Left);
        let left_right = node!(self.nodes, left).get_register(Register::Right);

        self.update_child(index, Register::Left, left_right);
        self.update_child(left, Register::Right, index);

        left
    }

    /// Updates the child of a parent node.
    ///
    /// This is a convenience function to update the child value of a parent node
    /// and trigger the [`update_height`] on the node. This is necessary since the
    /// child node being set might be the larger subtree on its new parent node.
    ///
    /// # Arguments
    ///
    /// * `parent` - index of the parent node.
    /// * `branch` - indicates whether it is the [`Field::Left`] or [`Field::Right`] child.
    /// * `child` - index of the child node.
    #[inline]
    fn update_child(&mut self, parent: u32, branch: Register, child: u32) {
        match branch {
            Register::Left => node!(self.nodes, parent).set_register(Register::Left, child),
            Register::Right => node!(self.nodes, parent).set_register(Register::Right, child),
            _ => panic!("invalid branch"),
        }

        self.update_height(parent);
    }

    /// Updates the height of a node.
    ///
    /// The height of a node is determined by the height of the larger child's subtree plus one.
    ///
    /// # Arguments
    ///
    /// * `index` - index of the node.
    fn update_height(&mut self, index: u32) {
        let left = node!(self.nodes, index).get_register(Register::Left);
        let right = node!(self.nodes, index).get_register(Register::Right);

        let height = if left == SENTINEL && right == SENTINEL {
            0
        } else {
            let left_height = if left != SENTINEL {
                node!(self.nodes, left).get_register(Register::Height)
            } else {
                0
            };
            let right_height = if right != SENTINEL {
                node!(self.nodes, right).get_register(Register::Height)
            } else {
                0
            };

            max(left_height, right_height) + 1
        };

        node!(self.nodes, index).set_register(Register::Height, height);
    }

    /// Remove a node from the tree, returning its value.
    fn remove_node(&mut self, index: u32) -> Option<V> {
        if index == SENTINEL {
            return None;
        }

        let node = &mut node!(self.nodes, index);
        let value = node.value;

        // clears the node values
        node.initialize(K::default(), V::default());

        let free_list_head = self.allocator.get_field(Field::FreeListHead);
        // we use the height field to create a linked list
        // of free nodes
        node.set_register(Register::Height, free_list_head);
        self.allocator.set_field(Field::FreeListHead, index);
        self.allocator
            .set_field(Field::Size, self.allocator.get_field(Field::Size) - 1);

        Some(value)
    }
}

/// The allocator is responsible to keep track of the status of the tree.
///
/// It uses two special fields to determine if the tree is full and to reuse
/// deleted nodes. Until the tree is full, the `sequence` has the same value
/// as the `free_list_head` field. When the tree is full, the `sequence` field
/// will be equal to the capacity of the tree. At this point, the `free_list_head`
/// is used to determine the index of free nodes.
#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
pub struct Allocator {
    /// Allocator fields:
    ///   [0] - root
    ///   [1] - size
    ///   [2] - capacity
    ///   [3] - free_list_head
    ///   [4] - sequence
    ///   [5] - not in use (padding)
    fields: [u32; 6],
}

impl Allocator {
    pub fn initialize(&mut self, capacity: u32) {
        self.fields = [SENTINEL, 0, capacity, 1, 1, 0];
    }

    #[inline(always)]
    fn get_field(&self, field: Field) -> u32 {
        self.fields[field as usize]
    }

    #[inline(always)]
    fn set_field(&mut self, field: Field, value: u32) {
        self.fields[field as usize] = value;
    }
}
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct Node<
    K: PartialOrd + Copy + Clone + Default + Pod + Zeroable,
    V: Default + Copy + Clone + Pod + Zeroable,
> {
    /// Registers for a node. This is fixed to include:
    ///   [0] - left child
    ///   [1] - right child
    ///   [2] - height
    ///   [3] - not in use (padding)
    registers: [u32; 4],
    /// Account key.
    key: K,
    /// The value associated with the node.
    value: V,
}

impl<
        K: PartialOrd + Copy + Clone + Default + Pod + Zeroable,
        V: Default + Copy + Clone + Pod + Zeroable,
    > Node<K, V>
{
    fn initialize(&mut self, key: K, value: V) {
        self.registers = [SENTINEL, SENTINEL, 0, 0];
        self.key = key;
        self.value = value;
    }

    #[inline(always)]
    fn get_register(&self, register: Register) -> u32 {
        self.registers[register as usize]
    }

    #[inline(always)]
    fn set_register(&mut self, register: Register, value: u32) {
        self.registers[register as usize] = value;
    }
}

unsafe impl<
        K: PartialOrd + Copy + Clone + Default + Pod + Zeroable,
        V: Default + Copy + Clone + Pod + Zeroable,
    > Zeroable for Node<K, V>
{
}
unsafe impl<
        K: PartialOrd + Copy + Clone + Default + Pod + Zeroable,
        V: Default + Copy + Clone + Pod + Zeroable,
    > Pod for Node<K, V>
{
}

#[cfg(test)]
mod tests {
    use crate::collections::AVLTreeMut;

    #[test]
    fn test_insert() {
        const CAPACITY: usize = 10;

        let mut data = [0u8; AVLTreeMut::<u64, u64>::data_len(CAPACITY)];
        let mut tree = AVLTreeMut::from_bytes_mut(&mut data);

        tree.allocator.initialize(CAPACITY as u32);

        for i in 0..CAPACITY {
            let key = i as u64;
            let value = i as u64;
            let _ = tree.insert(key, value);
        }

        assert_eq!(tree.len(), CAPACITY);

        for i in 0..CAPACITY {
            let key = i as u64;

            tree.get(&key).unwrap();
        }
    }

    #[test]
    fn test_large_insert() {
        const CAPACITY: usize = 10_000;

        let mut data = [0u8; AVLTreeMut::<u64, u64>::data_len(CAPACITY)];
        let mut tree = AVLTreeMut::from_bytes_mut(&mut data);
        tree.allocator.initialize(CAPACITY as u32);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;
            let value = (i + 1) as u64;
            let _ = tree.insert(key, value);
        }

        assert_eq!(tree.len(), CAPACITY);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;

            tree.get(&key).unwrap();
        }
    }

    #[test]
    fn test_large_remove() {
        const CAPACITY: usize = 10_000;

        let mut data = [0u8; AVLTreeMut::<u64, u64>::data_len(CAPACITY)];
        let mut tree = AVLTreeMut::from_bytes_mut(&mut data);
        tree.allocator.initialize(CAPACITY as u32);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;
            let value = (i + 1) as u64;
            let _ = tree.insert(key, value);
        }

        assert_eq!(tree.len(), CAPACITY);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;

            tree.remove(&key).unwrap();
        }

        assert_eq!(tree.len(), 0);
    }

    #[test]
    fn test_large_remove_add() {
        const CAPACITY: usize = 10_000;

        let mut data = [0u8; AVLTreeMut::<u64, u64>::data_len(CAPACITY)];
        let mut tree = AVLTreeMut::from_bytes_mut(&mut data);
        tree.allocator.initialize(CAPACITY as u32);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;
            let value = (i + 1) as u64;
            let _ = tree.insert(key, value);
        }

        assert_eq!(tree.len(), CAPACITY);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;

            tree.remove(&key).unwrap();
        }

        assert_eq!(tree.len(), 0);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;
            let value = (i + 1) as u64;
            let _ = tree.insert(key, value);
        }

        assert_eq!(tree.len(), CAPACITY);

        for i in 0..CAPACITY {
            let key = (i + 1) as u64;

            tree.get(&key).unwrap();
        }
    }

    #[test]
    fn test_insert_when_full() {
        const CAPACITY: usize = 10;

        let mut data = [0u8; AVLTreeMut::<u64, u64>::data_len(CAPACITY)];
        let mut tree = AVLTreeMut::from_bytes_mut(&mut data);

        tree.allocator.initialize(CAPACITY as u32);

        for i in 0..CAPACITY {
            let key = i as u64;
            let value = i as u64;
            let _ = tree.insert(key, value);
        }

        assert_eq!(tree.len(), CAPACITY);
        assert!(tree.is_full());

        // we should not be able to insert when full
        assert!(tree.insert(10, 0).is_none());

        // when we remove an item
        tree.remove(&0).unwrap();
        // then we can insert
        tree.insert(10, 0).unwrap();

        // but then the tree is full again
        assert!(tree.is_full());
        assert!(tree.insert(20, 0).is_none());
    }
}
