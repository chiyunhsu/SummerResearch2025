import Mathlib
open Nat Partition
-- The multiset of `2 ^ i` in the binary expansion of a natural number
def binary (a : ℕ) : Multiset ℕ := a.bitIndices.map (fun i ↦ 2 ^ i)

lemma binary_nodup (a : ℕ) : (binary a).Nodup := by
  apply Multiset.coe_nodup.mpr
  exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) (List.Sorted.nodup (bitIndices_sorted))

lemma binary_sum (a : ℕ) : (binary a).sum = a := by
  apply Nat.twoPowSum_bitIndices

-- Highest odd factor of a natural number
def hof (b : ℕ) : ℕ := ordCompl[2] b

lemma ordCompl_PrimePow_eq_one {p k : ℕ} (hp : Nat.Prime p) : ordCompl[p] (p ^ k) = 1 := by
  have pow_ne_zero : p ^ k ≠ 0 := pow_ne_zero k (Nat.Prime.ne_zero hp)
  apply Nat.eq_of_factorization_eq
  · exact pos_iff_ne_zero.mp (ordCompl_pos p pow_ne_zero)
  · exact one_ne_zero
  · simp [Nat.factorization_ordCompl, Nat.Prime.factorization_pow hp, Nat.factorization_one]

lemma ordCompl_mul_PrimePow_eq_self (n k : ℕ) {p : ℕ} (hp : Nat.Prime p) : ordCompl[p] (p ^ k * n) = ordCompl[p] n := by
  rw [ordCompl_mul, ordCompl_PrimePow_eq_one hp, one_mul]

lemma not_dvd_of_ordComp_eq_self (n : ℕ) {p : ℕ} (hp : Nat.Prime p) : ordCompl[p] n = n ↔ n = 0 ∨ ¬p ∣ n := by
  constructor
  · intro h
    by_cases n_zero : n = 0
    · simp [n_zero]
    · right
      rw [← h]
      exact not_dvd_ordCompl hp n_zero
  · rintro (n_eq_zero | not_dvd)
    · simp [n_eq_zero]
    · have : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd not_dvd
      rw [this]
      simp

lemma hof_eq_iff_odd_or_zero (b : ℕ) : hof b = b ↔ (b = 0 ∨ Odd b) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_of_ordComp_eq_self b prime_two

lemma hof_is_odd {b : ℕ} (b_ne_zero : b ≠ 0) : Odd (hof b) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_ordCompl prime_two b_ne_zero

lemma hof_ne_zero_of_ne_zero {b : ℕ} (b_ne_zero : b ≠ 0) : hof b ≠ 0 := Nat.pos_iff_ne_zero.mp (ordCompl_pos 2 b_ne_zero)

lemma hof_zero_iff_zero (b : ℕ) : b = 0 ↔ hof b = 0 := by
  constructor
  · intro b_eq_zero
    simp [b_eq_zero, hof]
  · contrapose
    exact hof_ne_zero_of_ne_zero

lemma hof_eq_of_odd {b : ℕ} (hodd : Odd b) : hof b = b := ((hof_eq_iff_odd_or_zero b).mpr (Or.inr hodd))

lemma hof_two_pow_mul (b i : ℕ) : hof (2 ^ i * b) = hof (b) := ordCompl_mul_PrimePow_eq_self b i prime_two

lemma hof_dvd (b : ℕ) : hof b ∣ b := ordCompl_dvd b 2

lemma hof_div_eq_two_pow {b : ℕ} (b_ne_zero : b ≠ 0) : ∃ k : ℕ, 2 ^ k = b / hof b := by
  use (b.factorization 2)
  symm
  apply Nat.div_eq_of_eq_mul_right
  rw [Nat.pos_iff_ne_zero]
  exact (mt (hof_zero_iff_zero b).mpr) b_ne_zero
  symm
  rw [mul_comm]
  exact (ordProj_mul_ordCompl_eq_self b 2)

lemma hof_mul_two_pow_eq (b : ℕ) : ∃ (k : ℕ), 2 ^ k * hof b = b := by
  use (b.factorization 2)
  exact ordProj_mul_ordCompl_eq_self b 2

lemma hof_le (b : ℕ) : hof b ≤ b := ordCompl_le b 2


--agreed on using finset sum for both right inverse and left inverse
--need to carefully rewrite the proof uing just finset sum later
-- Mapping a part `a` of a partition `P` to the multiset consisting of `a * 2 ^ i`, where `2 ^ i` is in the binary expansion of the multiplicity of `a`
def FromOddPart {n : ℕ} (P : n.Partition) (a : ℕ) : Multiset ℕ :=
  (binary (Multiset.count a P.parts)).map (fun x ↦ x * a)
