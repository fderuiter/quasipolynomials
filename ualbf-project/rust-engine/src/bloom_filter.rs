use std::error::Error;
use std::fmt;

#[cfg(feature = "signing")]
use sha2::{Digest, Sha256};

#[derive(Debug, PartialEq, Clone)]
pub enum BloomFilterError {
    InvalidExpectedElements,
    InvalidFalsePositiveRate,
    AllocationOverflow,
}

impl fmt::Display for BloomFilterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BloomFilterError::InvalidExpectedElements => {
                write!(f, "expected_elements must be greater than zero")
            }
            BloomFilterError::InvalidFalsePositiveRate => write!(
                f,
                "false_positive_rate must be strictly between 0.0 and 1.0"
            ),
            BloomFilterError::AllocationOverflow => write!(
                f,
                "Bloom filter allocation calculation caused an integer overflow"
            ),
        }
    }
}

impl Error for BloomFilterError {}

#[derive(Debug)]
pub struct BloomFilter {
    bits: Vec<u64>,
    num_bits: usize,
    num_hashes: usize,
}

impl BloomFilter {
    pub fn try_new(
        expected_elements: usize,
        false_positive_rate: f64,
    ) -> Result<Self, BloomFilterError> {
        if expected_elements == 0 {
            return Err(BloomFilterError::InvalidExpectedElements);
        }
        if !false_positive_rate.is_finite()
            || false_positive_rate <= 0.0
            || false_positive_rate >= 1.0
        {
            return Err(BloomFilterError::InvalidFalsePositiveRate);
        }

        let num_bits_f64 = (-(expected_elements as f64) * false_positive_rate.ln()
            / (std::f64::consts::LN_2.powi(2)))
        .ceil();
        if !num_bits_f64.is_finite() || num_bits_f64 < 0.0 || num_bits_f64 > (usize::MAX as f64) {
            return Err(BloomFilterError::AllocationOverflow);
        }

        let num_bits = num_bits_f64 as usize;

        let num_hashes_f64 =
            (std::f64::consts::LN_2 * num_bits_f64 / (expected_elements as f64)).ceil();
        if !num_hashes_f64.is_finite()
            || num_hashes_f64 <= 0.0
            || num_hashes_f64 > (usize::MAX as f64)
        {
            return Err(BloomFilterError::AllocationOverflow);
        }
        let num_hashes = num_hashes_f64 as usize;

        let vec_len = num_bits
            .checked_add(63)
            .ok_or(BloomFilterError::AllocationOverflow)?
            / 64;

        if vec_len > (isize::MAX as usize) / 8 {
            return Err(BloomFilterError::AllocationOverflow);
        }

        Ok(Self {
            bits: vec![0; vec_len.max(1)],
            num_bits,
            num_hashes: num_hashes.max(1),
        })
    }

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
        Self::try_new(expected_elements, false_positive_rate).unwrap()
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
    #[cfg(feature = "signing")]
    fn get_hash_indices(&self, item: &(u32, u8)) -> Vec<usize> {
        let mut hasher = Sha256::new();
        hasher.update(&item.0.to_le_bytes());
        hasher.update(&[item.1]);
        let hash_bytes = hasher.finalize();

        let mut indices = Vec::with_capacity(self.num_hashes);
        let hash1 = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap());
        let hash2 = u64::from_le_bytes(hash_bytes[8..16].try_into().unwrap());

        for i in 0..self.num_hashes {
            let idx = unsafe {
                crate::lean_ffi::ualbf_bloom_get_index(
                    hash1,
                    hash2,
                    (self.num_bits as u64).max(1),
                    i as u32,
                )
            };
            indices.push(idx as usize);
        }
        indices
    }

    #[cfg(not(feature = "signing"))]
    fn get_hash_indices(&self, item: &(u32, u8)) -> Vec<usize> {
        let mut indices = Vec::with_capacity(self.num_hashes);

        // FNV-1a constants for 64-bit
        let fnv_prime: u64 = 0x00000100000001B3;
        let fnv_offset: u64 = 0xCBF29CE484222325;

        // Compute hash1
        let mut hash1 = fnv_offset;
        for b in item.0.to_le_bytes() {
            hash1 ^= b as u64;
            hash1 = hash1.wrapping_mul(fnv_prime);
        }
        hash1 ^= item.1 as u64;
        hash1 = hash1.wrapping_mul(fnv_prime);

        // Compute hash2
        let mut hash2 = fnv_offset;
        for b in item.0.to_le_bytes() {
            hash2 ^= b as u64;
            hash2 = hash2.wrapping_mul(fnv_prime);
        }
        hash2 ^= item.1 as u64;
        hash2 = hash2.wrapping_mul(fnv_prime);
        hash2 ^= 0xFFu64; // Differentiator suffix byte
        hash2 = hash2.wrapping_mul(fnv_prime);

        for i in 0..self.num_hashes {
            let idx = unsafe {
                crate::lean_ffi::ualbf_bloom_get_index(
                    hash1,
                    hash2,
                    (self.num_bits as u64).max(1),
                    i as u32,
                )
            };
            indices.push(idx as usize);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_filter_try_new_invalid_elements() {
        assert_eq!(
            BloomFilter::try_new(0, 0.01).unwrap_err(),
            BloomFilterError::InvalidExpectedElements
        );
    }

    #[test]
    fn test_bloom_filter_try_new_invalid_fp_rate() {
        assert_eq!(
            BloomFilter::try_new(100, 0.0).unwrap_err(),
            BloomFilterError::InvalidFalsePositiveRate
        );
        assert_eq!(
            BloomFilter::try_new(100, 1.0).unwrap_err(),
            BloomFilterError::InvalidFalsePositiveRate
        );
        assert_eq!(
            BloomFilter::try_new(100, -0.1).unwrap_err(),
            BloomFilterError::InvalidFalsePositiveRate
        );
        assert_eq!(
            BloomFilter::try_new(100, f64::NAN).unwrap_err(),
            BloomFilterError::InvalidFalsePositiveRate
        );
    }

    #[test]
    fn test_bloom_filter_try_new_overflow() {
        // High false positive rate or extreme elements causing overflow
        // E.g. expected_elements = usize::MAX, fp_rate = 0.0001
        assert_eq!(
            BloomFilter::try_new(usize::MAX, 0.0001).unwrap_err(),
            BloomFilterError::AllocationOverflow
        );
    }

    #[test]
    fn test_bloom_filter_fallback_hashing_uncorrelated() {
        let bf = BloomFilter::new(100, 0.01);
        let idx1 = bf.get_hash_indices(&(42, 1));
        let idx2 = bf.get_hash_indices(&(42, 2));
        assert_ne!(idx1, idx2);

        let idx3 = bf.get_hash_indices(&(43, 1));
        assert_ne!(idx1, idx3);
    }
}
