use sha2::{Sha256, Digest};

pub struct BloomFilter {
    bits: Vec<u64>,
    num_bits: usize,
    num_hashes: usize,
}

impl BloomFilter {
    /// Creates a BloomFilter sized for the given expected element count and target false positive rate.
    ///
    /// The filter's internal bit array and number of hash functions are computed from `expected_elements`
    /// and `false_positive_rate`; storage is allocated and minimum sizes of one bit and one hash are enforced.
    ///
    /// # Parameters
    ///
    /// - `expected_elements`: estimated number of elements to be stored in the filter.
    /// - `false_positive_rate`: desired probability of false positives (typical values are between 0 and 1).
    ///
    /// # Examples
    ///
    /// ```
    /// let mut bf = BloomFilter::new(100, 0.01);
    /// let item = (42u32, 1u8);
    /// assert!(!bf.contains(&item));
    /// bf.insert(&item);
    /// assert!(bf.contains(&item));
    /// ```
    pub fn new(expected_elements: usize, false_positive_rate: f64) -> Self {
        let num_bits = (-(expected_elements as f64) * false_positive_rate.ln() / (std::f64::consts::LN_2.powi(2))).ceil() as usize;
        let num_hashes = (std::f64::consts::LN_2 * (num_bits as f64) / (expected_elements as f64)).ceil() as usize;
        let vec_len = (num_bits + 63) / 64;
        Self {
            bits: vec![0; vec_len.max(1)],
            num_bits,
            num_hashes: num_hashes.max(1),
        }
    }

    /// Derives multiple bit indices for an item by hashing its bytes and applying double-hash arithmetic.
    ///
    /// This computes a SHA-256 digest of the item's bytes (the `u32` in little-endian followed by the `u8`),
    /// interprets the first two 64-bit words of the digest as unsigned values, and produces `self.num_hashes`
    /// indices by repeated addition (wrapping) of the second word to the first. Each index is in the range
    /// `[0, self.num_bits)`.
    ///
    /// # Examples
    ///
    /// ```
    /// let bf = BloomFilter::new(100, 0.01);
    /// let indices = bf.get_hash_indices(&(42u32, 7u8));
    /// assert_eq!(indices.len(), bf.num_hashes);
    /// assert!(indices.iter().all(|&i| i < bf.num_bits));
    /// ```
    ///
    /// # Returns
    ///
    /// A `Vec<usize>` containing `self.num_hashes` bit indices, each within `0..self.num_bits`.
    fn get_hash_indices(&self, item: &(u32, u8)) -> Vec<usize> {
        let mut hasher = Sha256::new();
        hasher.update(&item.0.to_le_bytes());
        hasher.update(&[item.1]);
        let hash_bytes = hasher.finalize();
        
        let mut indices = Vec::with_capacity(self.num_hashes);
        let mut current_hash = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap());
        let hash2 = u64::from_le_bytes(hash_bytes[8..16].try_into().unwrap());
        
        for i in 0..self.num_hashes {
            indices.push((current_hash % (self.num_bits as u64).max(1)) as usize);
            current_hash = current_hash.wrapping_add(hash2).wrapping_add(i as u64);
        }
        indices
    }

    /// Adds an item to the Bloom filter by setting the bits at the hashed indices.
    ///
    /// Computes the hash-derived bit positions for `item` and sets each corresponding bit in the filter's internal bit vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut bf = BloomFilter::new(100, 0.01);
    /// let item = (42u32, 7u8);
    /// bf.insert(&item);
    /// assert!(bf.contains(&item));
    /// ```
    pub fn insert(&mut self, item: &(u32, u8)) {
        for idx in self.get_hash_indices(item) {
            self.bits[idx / 64] |= 1 << (idx % 64);
        }
    }

    /// Checks whether the Bloom filter probably contains the given item.
    ///
    /// Returns `true` if all hash-derived bit positions for the item are set, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut bf = BloomFilter::new(100, 0.01);
    /// let item = (42u32, 7u8);
    /// bf.insert(&item);
    /// assert!(bf.contains(&item));
    /// ```
    pub fn contains(&self, item: &(u32, u8)) -> bool {
        for idx in self.get_hash_indices(item) {
            if self.bits[idx / 64] & (1 << (idx % 64)) == 0 {
                return false;
            }
        }
        true
    }
}
