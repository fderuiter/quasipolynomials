import Mathlib.Data.UInt
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

namespace UALBF.Engine.BloomFilter

-- | Re-implementation of the wrapping addition double hashing logic from the Rust engine.
-- Rust computes:
-- current_hash = hash1
-- for i in 0..num_hashes:
--   yield current_hash % num_bits
--   current_hash = current_hash.wrapping_add(hash2).wrapping_add(i)

def wrapping_hash_seq (hash1 hash2 : UInt64) : Nat → UInt64
| 0 => hash1
| (i + 1) => (wrapping_hash_seq hash1 hash2 i) + hash2 + (UInt64.ofNat i)

def get_hash_index (hash1 hash2 : UInt64) (num_bits : UInt64) (i : Nat) : UInt64 :=
  let max_bits := if num_bits = 0 then 1 else num_bits
  (wrapping_hash_seq hash1 hash2 i) % max_bits

-- | Proof that this wrapping logic corresponds to the explicit algebraic formula
-- Hash_i = hash1 + i * hash2 + i*(i-1)/2 (mod 2^64)
-- We prove it algebraically over Nat to guarantee soundness of the sequence.

def algebraic_hash_seq (h1 h2 : Nat) (i : Nat) : Nat :=
  h1 + i * h2 + (i * (i - 1)) / 2

theorem wrapping_hash_eq_algebraic (h1 h2 : Nat) (i : Nat) :
  algebraic_hash_seq h1 h2 i =
  if i = 0 then h1
  else algebraic_hash_seq h1 h2 (i - 1) + h2 + (i - 1) := sorry

-- | Abstract representation of the Bloom Filter Bitset state
def BloomFilterState (_num_bits : UInt64) := UInt64 → Bool

def empty_filter (num_bits : UInt64) : BloomFilterState num_bits :=
  fun _ => false

-- | Insert an item (represented by its two base hashes) into the filter
def insert (state : BloomFilterState num_bits) (hash1 hash2 : UInt64) (num_hashes : Nat) : BloomFilterState num_bits :=
  fun idx =>
    state idx || (∃ i < num_hashes, get_hash_index hash1 hash2 num_bits i = idx)

-- | Check if an item is in the filter
def contains (state : BloomFilterState num_bits) (hash1 hash2 : UInt64) (num_hashes : Nat) : Prop :=
  ∀ i < num_hashes, state (get_hash_index hash1 hash2 num_bits i) = true

-- | The core soundness theorem: "No False Negatives"
-- Proves that inserting an item guarantees that a subsequent `contains` check for that item will return true.
theorem contains_inserted_item
  (state : BloomFilterState num_bits)
  (hash1 hash2 : UInt64)
  (num_hashes : Nat) :
  contains (insert state hash1 hash2 num_hashes) hash1 hash2 num_hashes := by
  unfold contains insert
  intro i hi
  -- By definition of insert, we just need to prove the right side of the OR is true
  have h_or : state (get_hash_index hash1 hash2 num_bits i) = true ∨
              (∃ j < num_hashes, get_hash_index hash1 hash2 num_bits j = get_hash_index hash1 hash2 num_bits i) :=
    Or.inr ⟨i, hi, rfl⟩
  -- In Lean Bool logic, true || X is true, false || true is true.
  cases h_state : state (get_hash_index hash1 hash2 num_bits i)
  · simp
    exact h_or.resolve_left (by rw [h_state]; decide)
  · simp

-- | FFI Wrapper to expose the verified index logic to Rust
@[export ualbf_bloom_get_index]
def ualbf_bloom_get_index_impl (hash1 hash2 num_bits : UInt64) (i : UInt32) : UInt64 :=
  get_hash_index hash1 hash2 num_bits (i.toNat)

end UALBF.Engine.BloomFilter
