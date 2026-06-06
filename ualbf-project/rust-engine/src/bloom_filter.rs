use sha2::{Sha256, Digest};

pub struct BloomFilter {
    bits: Vec<u64>,
    num_bits: usize,
    num_hashes: usize,
}

impl BloomFilter {
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

    pub fn insert(&mut self, item: &(u32, u8)) {
        for idx in self.get_hash_indices(item) {
            self.bits[idx / 64] |= 1 << (idx % 64);
        }
    }

    pub fn contains(&self, item: &(u32, u8)) -> bool {
        for idx in self.get_hash_indices(item) {
            if self.bits[idx / 64] & (1 << (idx % 64)) == 0 {
                return false;
            }
        }
        true
    }
}
