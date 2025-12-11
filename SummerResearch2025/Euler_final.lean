/-
Copyright (c) 2025 Chi-Yun Hsu, Hanzhe Zhang, Tamanna Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chi-Yun Hsu, Hanzhe Zhang, Tamanna Agarwal
-/

import Mathlib

/-!
# Euler's Partition Theorem with Combinatorial Proof

This files proves Euler's Partition Theorem using combinatorial constructions.

Euler's Partition Theorem states that the number of integer partitions of `n` into `odd` parts
equals the number of partitions of `n` into `distinct` parts.

The combinatorial proof constructs explicit bijections between
the set of partitions of `n` into odd parts and the set of partitions of `n` into distinct parts.

Starting from an odd partition, we map each part `a` with multiplicity `m` to
the multiset consisting of `a * 2 ^ i`, where `2 ^ i` is in the binary expansion of `m`.

Conversely, starting from a distinct partition, we map each part `b` (with multiplicity 1) to
the multiset consisting of `hof b`, the highest odd factor of `b`, with multiplicity `b / hof(b)`.

## References

* [G. E. Andrews, *Euler’s partition identity-finite version*][andrews2016]
* <https://dspace.mit.edu/bitstream/handle/1721.1/123321/18-312-spring-2009/contents/readings-and-lecture-notes/MIT18_312S09_lec10_Patitio.pdf>

## Tags

integer partition, bijection
-/

open Nat Partition

/-- The multiset of `2 ^ i` in the binary expansion of a natural number `a` -/
def binary (a : ℕ) : Multiset ℕ := a.bitIndices.map (fun i ↦ 2 ^ i)

lemma binary_nodup (a : ℕ) : (binary a).Nodup := by
  apply Multiset.coe_nodup.mpr
  exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) (List.Sorted.nodup (bitIndices_sorted))

lemma binary_sum (a : ℕ) : (binary a).sum = a := by
  apply Nat.twoPowSum_bitIndices

/-- The highest odd factor of a natural number `b` -/
def hof (b : ℕ) : ℕ := ordCompl[2] b

-- Suggest to add
theorem ordProj_PrimePow_eq_self {p k : ℕ} (hp : Nat.Prime p) : ordProj[p] (p ^ k) = p ^ k := by
  have pow_ne_zero : p ^ k ≠ 0 := pow_ne_zero k (Nat.Prime.ne_zero hp)
  apply Nat.eq_of_factorization_eq
  · exact pos_iff_ne_zero.mp (ordProj_pos (p ^ k) p)
  · exact pow_ne_zero
  · simp [Nat.Prime.factorization_pow hp]

theorem ordCompl_PrimePow_eq_one {p k : ℕ} (hp : Nat.Prime p) : ordCompl[p] (p ^ k) = 1 := by
  have pow_ne_zero : p ^ k ≠ 0 := pow_ne_zero k (Nat.Prime.ne_zero hp)
  apply Nat.eq_of_factorization_eq
  · exact pos_iff_ne_zero.mp (ordCompl_pos p pow_ne_zero)
  · exact one_ne_zero
  · simp [Nat.Prime.factorization_pow hp]

theorem ordCompl_PrimePow_mul_eq_self (n k : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    ordCompl[p] (p ^ k * n) = ordCompl[p] n := by
  rw [ordCompl_mul, ordCompl_PrimePow_eq_one hp, one_mul]

theorem ordCompl_eq_self_iff_zero_or_not_dvd (n : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    ordCompl[p] n = n ↔ n = 0 ∨ ¬p ∣ n := by
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
-- End of Suggest to Add

lemma hof_eq_iff_odd_or_zero (b : ℕ) : hof b = b ↔ (b = 0 ∨ Odd b) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact ordCompl_eq_self_iff_zero_or_not_dvd b prime_two

lemma hof_is_odd {b : ℕ} (b_ne_zero : b ≠ 0) : Odd (hof b) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_ordCompl prime_two b_ne_zero

lemma hof_ne_zero_of_ne_zero {b : ℕ} (b_ne_zero : b ≠ 0) : hof b ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (ordCompl_pos 2 b_ne_zero)

lemma hof_zero_iff_zero (b : ℕ) : hof b = 0 ↔ b = 0 := by
  constructor
  · contrapose
    exact hof_ne_zero_of_ne_zero
  · intro b_eq_zero
    simp [b_eq_zero, hof]

lemma hof_eq_of_odd {b : ℕ} (hodd : Odd b) : hof b = b := ((hof_eq_iff_odd_or_zero b).mpr (Or.inr hodd))

lemma hof_two_pow_mul (b i : ℕ) : hof (2 ^ i * b) = hof (b) := ordCompl_PrimePow_mul_eq_self b i prime_two

lemma hof_dvd (b : ℕ) : hof b ∣ b := ordCompl_dvd b 2

lemma hof_div_eq_two_pow {b : ℕ} (b_ne_zero : b ≠ 0) : ∃ k : ℕ, b / hof b = 2 ^ k:= by
  use (b.factorization 2)
  apply Nat.div_eq_of_eq_mul_right
  rw [Nat.pos_iff_ne_zero]
  exact (mt (hof_zero_iff_zero b).mp) b_ne_zero
  symm
  rw [mul_comm]
  exact (ordProj_mul_ordCompl_eq_self b 2)

lemma hof_mul_two_pow_eq (b : ℕ) : ∃ (k : ℕ), hof b * 2 ^ k = b := by
  use (b.factorization 2)
  rw [mul_comm]
  exact ordProj_mul_ordCompl_eq_self b 2

lemma hof_le (b : ℕ) : hof b ≤ b := ordCompl_le b 2

/-- Given a part `a` of a partition `P`, construct the multiset consisting of `a * 2 ^ i`,
where `2 ^ i` is in the binary expansion of the multiplicity of `a`. -/
def FromOddPart {n : ℕ} (P : n.Partition) (a : ℕ) : Multiset ℕ :=
  (binary (Multiset.count a P.parts)).map (fun x ↦ x * a)

lemma FromOddPart_empty_of_notMem {n : ℕ} (P : n.Partition) (a : ℕ) :
    a ∉ P.parts → FromOddPart P a = 0 := by
  intro ha
  unfold FromOddPart
  apply Multiset.count_eq_zero_of_notMem at ha
  simp [ha, binary]

lemma FromOddPart_pos {n : ℕ} (P : n.Partition) (a : ℕ) {b : ℕ} :
    b ∈ (FromOddPart P a) → b > 0 := by
  intro hb
  by_cases ha : a ∈ P.parts
  · apply Multiset.mem_map.mp at hb
    rcases hb with ⟨x, hx, hb⟩
    have x_pos : x > 0 := by
      unfold binary at hx
      apply List.mem_map.mp at hx
      rcases hx with ⟨y, hy, hx⟩
      rw [← hx]
      exact Nat.pow_pos zero_lt_two
    rw [← hb]
    have a_pos : a > 0 := P.parts_pos ha
    exact Nat.mul_pos x_pos a_pos
  · rw [FromOddPart_empty_of_notMem P a ha] at hb
    contradiction

lemma FromOddPart_sum {n : ℕ} (P : n.Partition) (a : ℕ) :
    (FromOddPart P a).sum = (Multiset.count a P.parts) * a := by
  unfold FromOddPart
  rw [Multiset.sum_map_mul_right, Multiset.map_id']
  rw [binary_sum]

lemma FromOddPart_nodup {n : ℕ} (P : n.Partition) (a : ℕ):
    (FromOddPart P a).Nodup := by
  by_cases ha : a ∈ P.parts
  · apply Multiset.Nodup.map
    -- fun x => x * a is injective
    · rintro x1 x2 heq
      dsimp at heq
      have a_ne_zero : a ≠ 0 := by
        apply Nat.pos_iff_ne_zero.mp
        exact P.parts_pos ha
      exact (Nat.mul_left_inj a_ne_zero).mp heq
    -- binary has no duplicates
    · exact binary_nodup _
  · rw [FromOddPart_empty_of_notMem P a ha]
    exact Multiset.nodup_zero

lemma FromOddPart_hof {n : ℕ} (P : n.Partition) (P_odd : P ∈ (odds n)) (a : ℕ) :
    ∀ b ∈ FromOddPart P a, hof b = a := by
  rintro b hb
  by_cases ha : a ∈ P.parts
  · apply Multiset.mem_map.mp at hb
    rcases hb with ⟨x, hx, hb⟩
    unfold binary at hx
    simp at hx
    rcases hx with ⟨i, hi, hx⟩
    rw [← hb, ← hx, hof_two_pow_mul a i]
    apply (hof_eq_iff_odd_or_zero a).mpr
    right
    apply Nat.not_even_iff_odd.mp
    exact (Finset.mem_filter.mp P_odd).2 a ha
  · rw [FromOddPart_empty_of_notMem P a ha] at hb
    contradiction

lemma FromOddPart_disjoint {n : ℕ} (P : n.Partition) (P_odd : P ∈ (odds n)) (a a' : ℕ) :
    a ≠ a' → Disjoint (FromOddPart P a) (FromOddPart P a') := by
  rintro hneq
  apply Multiset.disjoint_iff_ne.mpr
  rintro x hx y hy heqxy
  have heq : a = a' := by
    calc
      a = hof x := (FromOddPart_hof P P_odd a x hx).symm
      _ = hof y := by rw [heqxy]
      _ = a' := FromOddPart_hof P P_odd a' y hy
  contradiction

/-- The multiset which is the union of `FromOddPart a` over distinct parts `a` of a partition `P`.
This is the map from odd partitions to distinct partitions on the `Multiset` level. -/
def FromOdd_parts {n : ℕ} (P : n.Partition) : Multiset ℕ :=
  Multiset.bind (P.parts.dedup) (FromOddPart P)
  --∑ a ∈ P.parts.toFinset, (FromOddPart P a)

lemma Finsetsum_eq_Bind {n : ℕ} (P : n.Partition) :
  ∑ a ∈ P.parts.toFinset, (FromOddPart P a)
  = Multiset.bind (P.parts.dedup) (FromOddPart P) := by rfl

-- Each part in the multiset `FromOdd_parts` is positive
lemma FromOdd_parts_pos {n : ℕ} (P : n.Partition) {b : ℕ} : b ∈ (FromOdd_parts P) → b > 0 := by
  rintro hb
  unfold FromOdd_parts at hb
  apply Multiset.mem_bind.mp at hb
  --apply Multiset.mem_sum.mp at hb
  rcases hb with ⟨a, ha, hb⟩
  exact FromOddPart_pos P a hb

-- The image of a partition of `n` under `FromOdd_parts` is still a partition of `n`
lemma FromOdd_parts_sum {n : ℕ} (P : n.Partition) : (FromOdd_parts P).sum = n := by
  unfold FromOdd_parts
  rw [Multiset.sum_bind]
  rw [(funext (FromOddPart_sum P))]
  simpa [P.parts_sum] using (Finset.sum_multiset_count P.parts).symm

/-- The map from odd partitions to distinct partitions on the `Partition` level. -/
def FromOdd {n : ℕ} (P : n.Partition) (_ : P ∈ odds n) : n.Partition :=
  { parts := FromOdd_parts P,
    parts_pos := FromOdd_parts_pos P,
    parts_sum := FromOdd_parts_sum P }

lemma InDist {n : ℕ} (P : n.Partition) (P_odd : P ∈ (odds n)) : FromOdd P P_odd ∈ (distincts n) := by
  unfold distincts
  simp
  unfold FromOdd
  simp
  unfold FromOdd_parts
  apply Multiset.nodup_bind.mpr
  constructor
  · intro a _
    exact FromOddPart_nodup P a
  · unfold Multiset.Pairwise
    let PListPart := Multiset.sort (· ≤ ·) P.parts.dedup
    have PListPart_nodup : PListPart.Nodup := by
      apply Multiset.coe_nodup.mp
      rw [Multiset.sort_eq]
      apply Multiset.nodup_dedup
    use PListPart
    constructor
    rw [Multiset.sort_eq]
    apply (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint (f := FromOddPart P) PListPart_nodup).mp
    rw [List.coe_toFinset]
    intro a ha a' ha' hneq
    simp only [Set.mem_setOf_eq] at ha ha'
    unfold PListPart at ha ha'
    rw [Multiset.mem_sort] at ha ha'
    dsimp[Function.onFun]
    exact FromOddPart_disjoint P P_odd a a' hneq

/-- The multiset consisting of `hof b` with multiplicity `b / hof(b)` of a natural number `b` -/
def FromDistPart (b : ℕ) : Multiset ℕ :=
  Multiset.replicate (ordProj[2] b) (hof b)

lemma FromDistPart_pos {n : ℕ} (Q : n.Partition) (b : ℕ) (hb : b ∈ Q.parts) {a : ℕ} :
    a ∈ (FromDistPart b) → a > 0 := by
  rintro ha
  apply Multiset.mem_replicate.mp at ha
  rw [ha.2]
  apply Nat.pos_iff_ne_zero.mpr
  apply Nat.div_ne_zero_iff.mpr
  constructor
  · exact pow_ne_zero _ two_ne_zero
  · have b_pos : b > 0 := Q.parts_pos hb
    apply le_of_dvd b_pos (ordProj_dvd b 2)

lemma FromDistPart_sum (b : ℕ) : (FromDistPart b).sum = b := by
  simp [FromDistPart]
  exact ordProj_mul_ordCompl_eq_self b 2

/-- The multiset which is the union of `FromDistPart b` over distinct parts `b` of a partition `Q`.
This is the map from distinct partitions to odd partitions on the `Multiset` level. -/
def FromDist_parts {n : ℕ} (Q : n.Partition) : Multiset ℕ :=
  -- Multiset.bind (Q.parts) (FromDistPart)
  -- ∑ b ∈ Q.parts.toFinset, (Multiset.count b Q.parts) • (FromDistPart_same_hof b)
  ∑ b' ∈ Q.parts.toFinset, (FromDistPart b')

lemma FromDist_parts_pos {n : ℕ} (Q : n.Partition) {a : ℕ} : a ∈ (FromDist_parts Q) → a > 0 := by
  rintro ha
  unfold FromDist_parts at ha
  apply Multiset.mem_sum.mp at ha
  rcases ha with ⟨b, hb, ha⟩
  rw [Multiset.mem_toFinset] at hb
  exact FromDistPart_pos Q b hb ha

lemma FromDist_parts_sum {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) : (FromDist_parts Q).sum = n := by
  unfold FromDist_parts
  --rw [Multiset.sum_bind]
  rw [Multiset.sum_sum]
  rw [(funext FromDistPart_sum)]
  have : ∑ x ∈ Q.parts.toFinset, x = (Multiset.map (fun x ↦ x) (Q.parts.dedup)).sum := by rfl
  rw [this, Multiset.map_id']
  have Q_Nodup : Q.parts.Nodup := by simpa [distincts] using Q_dist
  rw [Multiset.dedup_eq_self.mpr Q_Nodup]
  exact Q.parts_sum

/-- The map from distinct partitions to odd partitions on the `Partition` level. -/
def FromDist {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) : n.Partition :=
  { parts := FromDist_parts Q
    parts_pos := FromDist_parts_pos Q
    parts_sum := FromDist_parts_sum Q Q_dist }

lemma InOdd {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) : FromDist Q Q_dist ∈ odds n := by
  unfold odds
  simp
  intro a ha
  unfold FromDist at ha
  simp at ha
  unfold FromDist_parts at ha
  simp at ha
  rcases ha with ⟨b, hb, ha⟩
  unfold FromDistPart at ha
  apply Multiset.mem_replicate.mp at ha
  rw [ha.2]
  have b_ne_zero : b ≠ 0 := by
    apply Nat.pos_iff_ne_zero.mp
    apply Q.parts_pos
    apply hb
  exact hof_is_odd b_ne_zero

lemma LeftInvPart_same_hof {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) :
    ∑ b ∈ (FromOddPart P a).toFinset, ordProj[2] b = Multiset.count a P.parts := by
  by_cases a_zero : a = 0
  · have ha : a ∉ P.parts := by
      intro ha
      have : a ≠ 0 := Nat.pos_iff_ne_zero.mp (P.parts_pos ha)
      contradiction
    rw [FromOddPart_empty_of_notMem P a ha]
    rw [Multiset.count_eq_zero_of_notMem ha]
    simp
  · apply (Nat.mul_left_inj a_zero).mp
    rw [Finset.sum_mul]

    have lem1 (b : ℕ) (hb : b ∈ (FromOddPart P a).toFinset) : (2 ^ b.factorization 2) * a = b := by
      rw [← FromOddPart_hof P P_odd a b (Multiset.mem_toFinset.mp hb)]
      exact ordProj_mul_ordCompl_eq_self b 2
    rw [Finset.sum_congr rfl lem1]
    rw [← FromOddPart_sum P a]
    rw [Finset.sum_multiset_count (FromOddPart P a)]
    apply Finset.sum_congr rfl
    rintro b hb
    have count_eq_one : Multiset.count b (FromOddPart P a) = 1 := by
      exact ((Multiset.nodup_iff_count_eq_one.mp (FromOddPart_nodup P a) b) (Multiset.mem_toFinset.mp hb))
    simp [count_eq_one]

lemma LeftInvPart_diff_hof {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) :
    ∀ b ∈ (FromOdd_parts P).toFinset, b ∉ (FromOddPart P a).toFinset → Multiset.count a (FromDistPart b) = 0 := by
  intro b hb b_notfrom_a
  rw [Multiset.mem_toFinset] at hb b_notfrom_a
  rw [Multiset.count_eq_zero_of_notMem]
  by_contra contra
  simp [FromOdd_parts] at hb
  rcases hb with ⟨a', ha', b_from_a'⟩
  unfold FromDistPart at contra
  rw [Multiset.mem_replicate] at contra
  have hof_eq_a' : hof b = a' := FromOddPart_hof P P_odd a' b b_from_a'
  have a_eq_a' : a = a' := by rw [contra.2, hof_eq_a']
  rw [a_eq_a'] at b_notfrom_a
  contradiction

/- Proof strategy:
count a = count g f a
g = ∑ b. Only b = hof a matters
f = ∑ a'. Only a' with hof a' = hof a matters
-/

lemma LemForCong {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a b : ℕ) (hb : b ∈ (FromOddPart P a).toFinset) :
    Multiset.count a (FromDistPart b) = ordProj[2] b := by
  rw [← FromOddPart_hof P P_odd a b (Multiset.mem_toFinset.mp hb)]
  simp [FromDistPart]

lemma LeftInv {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) :
  FromDist (FromOdd P P_odd) (InDist P P_odd) = P := by
  ext a
  simp [FromDist, FromDist_parts]
  --rw [← Finsetsum_eq_Bind']
  simp [Multiset.count_sum']
  have hsubset : (FromOddPart P a).toFinset ⊆ (FromOdd P P_odd).parts.toFinset := by
    apply Multiset.toFinset_subset.mpr
    simp [FromOdd, FromOdd_parts]
    apply Multiset.subset_of_le
    by_cases ha : a ∈ P.parts
    · exact Multiset.le_bind P.parts.dedup (Multiset.mem_dedup.mpr ha)
    · simp [Multiset.count_eq_zero_of_notMem ha, FromOddPart, binary]
  rw [← Finset.sum_subset hsubset (LeftInvPart_diff_hof P P_odd a)]
  rw [Finset.sum_congr rfl (LemForCong P P_odd a)]
  exact LeftInvPart_same_hof P P_odd a

-- Now we use FromDistPart_same_hof rather than FromDistPart to help with the right inverse proof
/-- The sub multiset of a partition `Q` consisting of parts with the same `hof` value as `b`. -/
def Same_hof {n : ℕ} (Q : n.Partition) (b : ℕ) :
  Multiset ℕ := Multiset.filter (fun b' ↦ (hof b' = hof b)) Q.parts

/-- The multiset consisting of `hof b` with multiplicity equal to the sum of `b' / hof(b')`
over all parts `b'` in `Q` with the same `hof` value as `b`. -/
def FromDistPart_same_hof {n : ℕ} (Q : n.Partition) (b : ℕ) : Multiset ℕ :=
  Multiset.replicate (Multiset.map (fun b' ↦ ordProj[2] b') (Same_hof Q b)).sum (hof b)
  -- ∑ b' ∈ (Same_hof Q b).toFinset, FromDistPart b'

-- def FromDistPart' {n : ℕ} (Q : n.Partition) (a : ℕ) : Multiset ℕ :=
-- --Multiset.bind (Multiset.filter (fun b ↦ (hof b = a)) P.parts) (FromDistPart)
--   Multiset.replicate (Multiset.map (fun b ↦ ordProj[2] b) (Same_hof Q a)).sum a

lemma FromDistPart_same_hof_eq_Finset_sum {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
  FromDistPart_same_hof Q b = ∑ b' ∈ (Same_hof Q b).toFinset, FromDistPart b' := by
  unfold FromDistPart_same_hof FromDistPart
  have : ∀ b' ∈ (Same_hof Q b).toFinset,
    Multiset.replicate (2 ^ b'.factorization 2) (hof b') =
    Multiset.replicate (2 ^ b'.factorization 2) (hof b) := by
    intro b' hb'
    simp [Same_hof] at hb'
    rw [hb'.2]
  rw [Finset.sum_congr rfl this]
  symm
  rw [Multiset.eq_replicate]
  constructor
  · simp
    have : ∑ x ∈ (Same_hof Q b).toFinset, ordProj[2] x = (Multiset.map (fun x ↦ ordProj[2] x) ((Same_hof Q b).dedup)).sum := by rfl
    rw [this]
    have Q_Nodup : Q.parts.Nodup := by simpa [distincts] using Q_dist
    rw [Same_hof]
    rw [Multiset.dedup_eq_self.mpr (Multiset.Nodup.filter _ Q_Nodup)]
  · intro b' hb'
    simp at hb'
    rcases hb' with ⟨i, hi, hb'⟩
    rw [Multiset.mem_replicate] at hb'
    exact hb'.2

lemma Same_hof_subset {n : ℕ} (Q : n.Partition) (b : ℕ) :
  Same_hof Q b ⊆ Q.parts := Multiset.filter_subset _ _

lemma Count_FromDist_parts_eq_FromDistPart_same_hof {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    Multiset.count (hof b) (FromDist_parts Q) = Multiset.count (hof b) (FromDistPart_same_hof Q b) := by
  unfold FromDist_parts
  rw [FromDistPart_same_hof_eq_Finset_sum Q Q_dist]
  repeat rw [Multiset.count_sum']
  symm
  apply Finset.sum_subset (Multiset.toFinset_subset.mpr (Same_hof_subset Q b))
  intro b' hb' hb''
  rw [Multiset.mem_toFinset] at *
  unfold FromDistPart
  rw [Multiset.count_replicate]
  simp
  simp [Same_hof] at hb''
  exact hb'' hb'

/-- The multiset of exponents of 2 for parts in `Q` with the same `hof` value as `b`. -/
def Same_hof_bitIndices {n : ℕ} (Q : n.Partition) (b : ℕ) : Multiset ℕ :=
  Multiset.map (fun b' ↦ b'.factorization 2) (Same_hof Q b)

/-- The finite set of exponents of 2 for parts in `Q` with the same `hof` value as `b`.
Non-duplication is implied by `Q` being a distinct partition. -/
def Same_hof_bitIndices_finset {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    Finset ℕ :=
  { val := Same_hof_bitIndices Q b
    nodup := by
      apply Multiset.Nodup.map_on
      · intro x hx y hy heq
        rw [← ordProj_mul_ordCompl_eq_self x 2, ← ordProj_mul_ordCompl_eq_self y 2]
        simp [Same_hof, hof] at hx hy
        rw [hx.2, hy.2, heq]
      · apply Multiset.Nodup.filter
        simpa [distincts] using Q_dist }

/-- The sorted list of exponents of 2 for parts in `Q` with the same `hof` value as `b`. -/
def Same_hof_bitIndices_list {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
  List ℕ := Finset.sort (· ≤ ·) (Same_hof_bitIndices_finset Q Q_dist b)

lemma Same_hof_ordProj_eq_twopow_bitIndices {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    Multiset.map (fun b' ↦ ordProj[2] b') (Same_hof Q b) =
    List.map (fun i ↦ 2 ^ i) (Same_hof_bitIndices_list Q Q_dist b) := by
    --Multiset.map (fun i ↦ 2 ^ i) (Same_hof_bitIndices Q b) := by
  unfold Same_hof_bitIndices_list
  rw [← Multiset.map_coe, Finset.sort_eq]
  simp [Same_hof_bitIndices_finset, Same_hof_bitIndices]

lemma Same_hof_count_eq_bitIndices {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    (Multiset.count (hof b) (FromDistPart_same_hof Q b)).bitIndices =
    Same_hof_bitIndices_list Q Q_dist b := by
  simp [FromDistPart_same_hof]
  rw [Same_hof_ordProj_eq_twopow_bitIndices Q Q_dist b, Multiset.sum_coe]
  have sort : List.Sorted (· < ·) (Same_hof_bitIndices_list Q Q_dist b) := Finset.sort_sorted_lt _
  exact bitIndices_twoPowsum sort

lemma RightInvPart {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    (FromOddPart (FromDist Q Q_dist) (hof b)) = Same_hof Q b := by
  simp [FromOddPart, FromDist]
  rw [Count_FromDist_parts_eq_FromDistPart_same_hof Q Q_dist b]
  rw [binary]
  rw [Same_hof_count_eq_bitIndices Q Q_dist b]
  simp only [Same_hof_bitIndices_list, Same_hof_bitIndices_finset, Same_hof_bitIndices]
  simp only [Finset.sort_mk, ← Multiset.map_coe, Multiset.sort_eq]
  nth_rewrite 2 [Multiset.map_map]
  rw [Multiset.map_map]
  have same_hof_eq_composedMap :
      ∀ b' ∈ Same_hof Q b,
        ((fun x => x * hof b) ∘ (fun i => 2 ^ i) ∘ (fun b'' => b''.factorization 2)) b' =
        (fun b'' => b'') b' := by
    intro b' hb'
    simp [Same_hof] at hb'
    simp [hof] at *
    rw [← hb'.2]
    exact ordProj_mul_ordCompl_eq_self b' 2
  rw [Multiset.map_congr rfl same_hof_eq_composedMap]
  simp

lemma RightInvPart_diff_hof {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    ∀ a ∈ (FromDist Q Q_dist).parts.toFinset,
      a ∉ (FromDistPart_same_hof Q b).toFinset →
      Multiset.count b (FromOddPart (FromDist Q Q_dist) a) = 0 := by
  intro a ha a_not_in_hofb
  -- Show a = hof b' for some b' in Q
  simp [Multiset.mem_toFinset] at ha
  have a_odd : Odd a := by
    have FromDist_Q_odd : FromDist Q Q_dist ∈ odds n := InOdd Q Q_dist
    simp [odds] at FromDist_Q_odd
    exact FromDist_Q_odd a ha
  simp [FromDist, FromDist_parts] at ha
  rcases ha with ⟨b', b'_in_Q, ha⟩
  simp [FromDistPart, Multiset.mem_replicate] at ha
  -- Assume for the sake of contradiction that count b ≠ 0; then b = 2 ^ i * a for some i
  rw [Multiset.count_eq_zero]
  intro contra
  simp [FromOddPart] at contra
  rcases contra with ⟨x, hx, contra⟩
  simp [binary] at hx
  rcases hx with ⟨i, hi, hx⟩
  rw [← hx] at contra

  have a_eq_hofb : a = hof b := by
    rw [← contra, hof_two_pow_mul a i, hof_eq_of_odd a_odd]
  simp only [FromDistPart_same_hof, Multiset.toFinset_replicate] at a_not_in_hofb
  -- Prove by cases depending on `Same_hof Q b is empty or not`
  by_cases h : (Multiset.map (fun b' => ordProj[2] b') (Same_hof Q b)).sum = 0
  · simp [h] at a_not_in_hofb
    rw [a_eq_hofb] at ha
    have b'_in_Same_hof : b' ∈ Same_hof Q b := by simpa [Same_hof] using ⟨b'_in_Q, ha.symm⟩
    have eq_zero : ordProj[2] b' = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← h]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun b' => ordProj[2] b') b'_in_Same_hof)
    have ne_zero : ordProj[2] b' ≠ 0 := Nat.pos_iff_ne_zero.mp (ordProj_pos b' 2)
    contradiction
  · simp [h] at a_not_in_hofb
    contradiction

/- Proof strategy : For each b ∈ Q, count FromOdd (FromDist b) = count b.
count b = count f g b
f = ∑ a. Only a = hof b matters
g = ∑ b'. Only b' with hof b' = hof b matters
-/

lemma RightInv {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) :
    FromOdd (FromDist Q Q_dist) (InOdd Q Q_dist) = Q := by
  ext b
  simp [FromOdd, FromOdd_parts]
  rw [← Finsetsum_eq_Bind]
  simp [Multiset.count_sum']
  have hsubset : (FromDistPart_same_hof Q b) ⊆ (FromDist Q Q_dist).parts := by
    simp [FromDist]
    apply Multiset.subset_of_le
    rw [FromDistPart_same_hof_eq_Finset_sum Q Q_dist, FromDist_parts]
    apply Finset.sum_le_sum_of_subset
    apply Multiset.toFinset_subset.mpr
    rw [Same_hof]
    apply Multiset.filter_subset
  rw [← Finset.sum_subset (Multiset.toFinset_subset.mpr hsubset) (RightInvPart_diff_hof Q Q_dist b)]
  -- Prove by cases depending on `Same_hof Q b is empty or not`
  by_cases h : (Multiset.map (fun b' => ordProj[2] b') (Same_hof Q b)).sum = 0
  · simp [FromDistPart_same_hof, h]
    rw [Multiset.count_eq_zero.mpr]
    intro b_in_Q
    have b_in_Same_hof : b ∈ Same_hof Q b := by simpa [Same_hof] using b_in_Q
    have eq_zero : ordProj[2] b = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← h]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun b' => ordProj[2] b') b_in_Same_hof)
    have ne_zero : ordProj[2] b ≠ 0 := Nat.pos_iff_ne_zero.mp (ordProj_pos b 2)
    contradiction
  · simp [FromDistPart_same_hof, h]
    rw [RightInvPart Q Q_dist b]
    simp [Same_hof]

theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card :=
    Finset.card_bij' FromOdd FromDist InDist InOdd LeftInv RightInv

--11/7/2025
-- Rename lemmas which are called lemmas, e.g. the eq's, aux, this.
-- Add some comments to make the proof more understandable
--    in the middle of lemmas add comments
-- Find anyways to make the code slightly more readable,
--    by combine shortlines and break up long lines
-- Try to make consistent spacing and notation convention
-- Read from bottom to top to check dependencies
-- Hanzhe look at more general things
--

--11/14/2025
--renamed eq aux lemmas
-- look at count_eq for potential rename

--11/21/2025
-- finished count_eq rename
-- made lemmas name and statement consistent up until fromoddparts
-- question: FromOddPart_pos we put comment on top of it, should we get rid of it since it's quite obvious?
--    or should we add comments to more lemmas?
