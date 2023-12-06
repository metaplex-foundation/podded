use bytemuck::{Pod, Zeroable};
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

// Constant to represent an empty value.
const SENTINEL: u32 = 0;

// Enum representing the fields of a node.
#[derive(Copy, Clone)]
enum Register {
    Bucket,
    Next,
}

// Enum representing the fields of the allocator.
enum Field {
    Size,
    Capacity,
    FreeListHead,
    Sequence,
}

/// Simple `HashSet` implementation where values are stored in a contiguous array.
pub struct HashSet<'a, V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> {
    /// Node allocator.
    allocator: &'a mut Allocator,

    /// Array to store the values.
    nodes: &'a mut [Node<V>],
}

impl<'a, V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> HashSet<'a, V> {
    /// Returns the required data length (in bytes) to store a set with the specified capacity.
    pub const fn required_data_len(capacity: usize) -> usize {
        std::mem::size_of::<Allocator>() + (capacity * std::mem::size_of::<Node<V>>())
    }

    /// Loads a set from a byte array.
    pub fn from_bytes(bytes: &'a mut [u8]) -> Self {
        let (allocator, nodes) = bytes.split_at_mut(std::mem::size_of::<Allocator>());

        let allocator = bytemuck::from_bytes_mut::<Allocator>(allocator);
        let nodes = bytemuck::cast_slice_mut(nodes);

        Self { allocator, nodes }
    }

    /// Returns the capacity of the set.
    pub fn capacity(&self) -> usize {
        self.allocator.get_field(Field::Capacity) as usize
    }

    /// Returns the number of values in the set.
    pub fn size(&self) -> usize {
        self.allocator.get_field(Field::Size) as usize
    }

    /// Indicates whether the set is full or not.
    pub fn is_full(&self) -> bool {
        self.allocator.get_field(Field::Size) >= self.allocator.get_field(Field::Capacity)
    }

    /// Indicates whether the set is empty or not.
    pub fn is_empty(&self) -> bool {
        self.allocator.get_field(Field::Size) == 0
    }

    /// Add a value on the set.
    ///
    /// This function will return the index of the value added; otherwise,
    /// it will return `None`.
    ///
    /// # Arguments
    ///
    /// * `value` - the value to add.
    pub fn add(&mut self, value: V) -> Option<u32> {
        if self.size() == self.capacity() {
            return None;
        }

        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        let index = hasher.finish() as u32 % self.allocator.get_field(Field::Capacity);

        let head = self.nodes[index as usize].get_register(Register::Bucket);
        let mut current = head;

        while current != SENTINEL {
            let node = self.nodes[(current - 1) as usize];
            // if the value is already present, we won't add
            // it again
            if node.value == value {
                return None;
            }

            current = node.get_register(Register::Next);
        }

        let node = self.add_node(value);
        self.nodes[index as usize].set_register(Register::Bucket, node);
        self.nodes[(node - 1) as usize].set_register(Register::Next, head);

        Some(node)
    }

    /// Remove a value from the set.
    ///
    /// If the value is not present in the set, this function will return `false`.
    ///
    /// # Arguments
    ///
    /// * `value` - the value to remove.
    pub fn remove(&mut self, value: &V) -> bool {
        if self.is_empty() {
            return false;
        }

        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        let index = hasher.finish() as u32 % self.allocator.get_field(Field::Capacity);

        let head = self.nodes[index as usize].get_register(Register::Bucket);
        let mut current = head;
        let mut previous = SENTINEL;

        while current != SENTINEL {
            let node = self.nodes[(current - 1) as usize];
            // if the value is already present, we won't add
            // it again
            if &node.value == value {
                if previous == SENTINEL {
                    self.nodes[index as usize].set_register(Register::Bucket, SENTINEL);
                } else {
                    self.nodes[(previous - 1) as usize]
                        .set_register(Register::Next, node.get_register(Register::Next));
                }

                return self.remove_node(current).is_some();
            }

            previous = current;
            current = node.get_register(Register::Next);
        }

        false
    }

    /// Checks whether a value is present in the set or not.
    ///
    /// # Arguments
    ///
    /// * `value` - the value to check.
    pub fn contains(&self, value: &V) -> bool {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        let index = hasher.finish() as u32 % self.allocator.get_field(Field::Capacity);

        let head = self.nodes[index as usize].get_register(Register::Bucket);
        let mut current = head;

        while current != SENTINEL {
            let node = self.nodes[(current - 1) as usize];
            if &node.value == value {
                return true;
            }

            current = node.get_register(Register::Next);
        }

        false
    }

    pub fn iter(&self) -> HashSetIterator<'_, V> {
        HashSetIterator::<V> {
            hash_set: self,
            bucket: SENTINEL,
            node: SENTINEL,
        }
    }

    /// Adds a node to the set.
    ///
    /// The node is only added if there is space on the nodes' array. The index
    /// where the node was added is returned.
    ///
    /// # Arguments
    ///
    /// * `value` - the value of the node.
    fn add_node(&mut self, value: V) -> u32 {
        let free_node = self.allocator.get_field(Field::FreeListHead);
        let sequence = self.allocator.get_field(Field::Sequence);

        if free_node == sequence {
            if (sequence - 1) == self.allocator.get_field(Field::Capacity) {
                panic!(
                    "set is full ({} nodes)",
                    self.allocator.get_field(Field::Size)
                );
            }

            self.allocator.set_field(Field::Sequence, sequence + 1);
            self.allocator.set_field(Field::FreeListHead, sequence + 1);
        } else {
            self.allocator.set_field(
                Field::FreeListHead,
                self.nodes[(free_node - 1) as usize].get_register(Register::Next),
            );
        }

        let entry = &mut self.nodes[(free_node - 1) as usize];

        entry.value = value;
        // the height field is used to store the free list head, so we make
        // sure we reset its value
        entry.set_register(Register::Next, SENTINEL);

        self.allocator
            .set_field(Field::Size, self.allocator.get_field(Field::Size) + 1);

        free_node
    }

    /// Remove a node from the set, returning its value.
    ///
    /// # Arguments
    ///
    /// * `index` - index of the node to remove.
    fn remove_node(&mut self, index: u32) -> Option<V> {
        if index == SENTINEL {
            return None;
        }

        let node = &mut self.nodes[(index - 1) as usize];
        let value = node.value;
        // clears the node value
        node.value = V::default();

        let free_list_head = self.allocator.get_field(Field::FreeListHead);
        // we use the `Next` register to create a linked list
        // of free nodes
        node.set_register(Register::Next, free_list_head);
        self.allocator.set_field(Field::FreeListHead, index);
        self.allocator
            .set_field(Field::Size, self.allocator.get_field(Field::Size) - 1);

        Some(value)
    }
}

/// The allocator is responsible to keep track of the status of the tree.
///
/// It uses two special fields to determine if the set is full and to reuse
/// deleted nodes. Until the set is full, the `sequence` has the same value
/// as the `free_list_head` field. When the set is full, the `sequence` field
/// will be equal to the capacity of the tree. At this point, the `free_list_head`
/// is used to determine the index of free nodes.
#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
pub struct Allocator {
    /// Allocator fields:
    ///   [0] - size
    ///   [1] - capacity
    ///   [2] - free_list_head
    ///   [3] - sequence
    fields: [u32; 4],
}

impl Allocator {
    pub fn initialize(&mut self, capacity: u32) {
        self.fields = [0, capacity, 1, 1];
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
pub struct Node<V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> {
    /// Registers for a node. This is fixed to include:
    ///   [0] - bucket
    ///   [1] - next
    ///
    /// Note that the index of nodes are always stored as `index + 1` to
    /// reserve the index 0 as the SENTINEL value.
    registers: [u32; 2],

    /// The value associated with the node.
    value: V,
}

impl<V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> Node<V> {
    #[inline(always)]
    fn get_register(&self, register: Register) -> u32 {
        self.registers[register as usize]
    }

    #[inline(always)]
    fn set_register(&mut self, register: Register, value: u32) {
        self.registers[register as usize] = value;
    }
}

pub struct HashSetIterator<'a, V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> {
    hash_set: &'a HashSet<'a, V>,
    bucket: u32,
    node: u32,
}

impl<'a, V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> Iterator
    for HashSetIterator<'a, V>
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        if self.bucket <= self.hash_set.capacity() as u32 {
            while self.node == SENTINEL {
                self.bucket += 1;
                if self.bucket > self.hash_set.capacity() as u32 {
                    return None;
                }
                self.node =
                    self.hash_set.nodes[(self.bucket - 1) as usize].get_register(Register::Bucket);
            }
            let node = &self.hash_set.nodes[(self.node - 1) as usize];
            self.node = node.get_register(Register::Next);
            Some(&node.value)
        } else {
            None
        }
    }
}

unsafe impl<V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> Zeroable for Node<V> {}

unsafe impl<V: Default + Copy + Clone + Hash + PartialEq + Pod + Zeroable> Pod for Node<V> {}

#[cfg(test)]
mod tests {
    use crate::collections::{
        hash_set::{Allocator, Node},
        HashSet,
    };

    #[test]
    fn test_add() {
        const CAPACITY: usize = 10;

        let mut data = [0u8; HashSet::<u64>::required_data_len(CAPACITY)];
        let mut set = HashSet::<u64>::from_bytes(&mut data);

        set.allocator.initialize(CAPACITY as u32);
        assert_eq!(set.capacity(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.add(value).is_some());
        }

        assert_eq!(set.size(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.contains(&value));
        }
    }

    #[test]
    fn test_large_add() {
        const CAPACITY: usize = 10_000;

        let mut data = [0u8; std::mem::size_of::<Allocator>()
            + ((1 + CAPACITY) * std::mem::size_of::<Node<u64>>())];
        let mut set = HashSet::<u64>::from_bytes(&mut data);

        set.allocator.initialize(CAPACITY as u32);
        assert_eq!(set.capacity(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.add(value).is_some());
        }

        assert_eq!(set.size(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.contains(&value));
        }
    }

    #[test]
    fn test_large_remove() {
        const CAPACITY: usize = 10_000;

        let mut data = [0u8; std::mem::size_of::<Allocator>()
            + ((1 + CAPACITY) * std::mem::size_of::<Node<u64>>())];
        let mut set = HashSet::<u64>::from_bytes(&mut data);

        set.allocator.initialize(CAPACITY as u32);
        assert_eq!(set.capacity(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.add(value).is_some());
        }

        assert_eq!(set.size(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.remove(&value));
        }

        assert_eq!(set.size(), 0);
    }

    #[test]
    fn test_large_remove_add() {
        const CAPACITY: usize = 10_000;

        let mut data = [0u8; std::mem::size_of::<Allocator>()
            + ((1 + CAPACITY) * std::mem::size_of::<Node<u64>>())];
        let mut set = HashSet::<u64>::from_bytes(&mut data);

        set.allocator.initialize(CAPACITY as u32);
        assert_eq!(set.capacity(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.add(value).is_some());
        }

        assert_eq!(set.size(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.remove(&value));
        }

        assert_eq!(set.size(), 0);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.add(value).is_some());
        }

        assert_eq!(set.size(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.contains(&value));
        }
    }

    #[test]
    fn test_insert_when_full() {
        const CAPACITY: usize = 10;

        let mut data = [0u8; std::mem::size_of::<Allocator>()
            + ((1 + CAPACITY) * std::mem::size_of::<Node<u64>>())];
        let mut set = HashSet::<u64>::from_bytes(&mut data);

        set.allocator.initialize(CAPACITY as u32);
        assert_eq!(set.capacity(), CAPACITY);

        for i in 0..CAPACITY {
            let value = (i + 1) as u64;
            assert!(set.add(value).is_some());
        }

        assert_eq!(set.size(), CAPACITY);
        assert!(set.is_full());

        // we should not be able to insert when full
        assert!(set.add(10).is_none());

        // when we remove an item
        assert!(set.remove(&1));
        // we can insert a value
        assert!(set.add(11).is_some());

        // and then the set is full again
        assert!(set.is_full());
        assert!(set.add(20).is_none());
    }
}
