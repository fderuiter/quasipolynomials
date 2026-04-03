import Mathlib

lemma x_sq_add_three_le_two_pow (X : ℕ) (hX : 5 ≤ X) : X ^ 2 + 3 ≤ 2 ^ X := by
  induction X, hq using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : (k + 1) ^ 2 + 3 = k ^ 2 + 2 * k + 4 := by ring
    have h_k : 2 * k + 4 ≤ k ^ 2 + 3 := by nlinarith
    calc (k + 1) ^ 2 + 3
      _ ≤ k ^ 2 + 3 + (k ^ 2 + 3) := Nat.add_le_add_left h_k _
      _ = 2 * (k ^ 2 + 3) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [← pow_one 2, ← pow_add]; congr 1; omega

lemma composite_bound_simple (Y p X : ℕ) (hp : 3 ≤ p) (hX : 5 ≤ X) (hpX : p ≤ X) :
    p * X * 2 ^ X < (2 ^ X - 1) ^ (p - 1) := by
  have H : X ^ 2 + 3 ≤ 2 ^ X := x_sq_add_three_le_two_pow X hX
  have H1 : p * X ≤ X ^ 2 := Nat.mul_le_mul_right X hpX
  have H2 : p * X + 2 ≤ 2 ^ X := by
    calc p * X + 2
      _ ≤ X ^ 2 + 2 := Nat.add_le_add_right H1 2
      _ ≤ X ^ 2 + 3 := by omega
      _ ≤ 2 ^ X := H
  have h_pow_pos : 1 ≤ 2 ^ X := Nat.one_le_pow _ 2 (by omega)
  have H3 : (2 ^ X - 1) ^ 2 + 2 * 2 ^ X = 2 ^ X * 2 ^ X + 1 := by
    have h_sub : 2 ^ X = (2 ^ X - 1) + 1 := (Nat.sub_add_cancel h_pow_pos).symm
    calc (2 ^ X - 1) ^ 2 + 2 * 2 ^ X
      _ = (2 ^ X - 1) ^ 2 + 2 * ((2 ^ X - 1) + 1) := by rw [h_sub]
      _ = (2 ^ X - 1) ^ 2 + 2 * (2 ^ X - 1) + 2 := by ring
      _ = (2 ^ X - 1) ^ 2 + 2 * (2 ^ X - 1) + 1 + 1 := by omega
      _ = ((2 ^ X - 1) + 1) ^ 2 + 1 := by ring
      _ = (2 ^ X) ^ 2 + 1 := by rw [← h_sub]
      _ = 2 ^ X * 2 ^ X + 1 := by ring
  have H4 : (p * X + 2) * 2 ^ X ≤ 2 ^ X * 2 ^ X := Nat.mul_le_mul_right _ H2
  have H5 : p * X * 2 ^ X + 2 * 2 ^ X + 1 ≤ 2 ^ X * 2 ^ X + 1 := by
    calc p * X * 2 ^ X + 2 * 2 ^ X + 1
      _ = (p * X + 2) * 2 ^ X + 1 := by ring
      _ ≤ 2 ^ X * 2 ^ X + 1 := Nat.add_le_add_right H4 1
  have H6 : p * X * 2 ^ X + 2 * 2 ^ X + 1 ≤ (2 ^ X - 1) ^ 2 + 2 * 2 ^ X := by
    rw [← H3] at H5
    exact H5
  have H7 : p * X * 2 ^ X + 1 ≤ (2 ^ X - 1) ^ 2 := by
    calc p * X * 2 ^ X + 1
      _ = p * X * 2 ^ X + 2 * 2 ^ X + 1 - 2 * 2 ^ X := by omega
      _ ≤ (2 ^ X - 1) ^ 2 + 2 * 2 ^ X - 2 * 2 ^ X := Nat.sub_le_sub_right H6 _
      _ = (2 ^ X - 1) ^ 2 := by omega
  have H8 : p * X * 2 ^ X < (2 ^ X - 1) ^ 2 := by omega
  have h_pow_ge_2 : 2 ≤ p - 1 := by omega
  have H9 : (2 ^ X - 1) ^ 2 ≤ (2 ^ X - 1) ^ (p - 1) := Nat.pow_le_pow_right (by omega) h_pow_ge_2
  omega
