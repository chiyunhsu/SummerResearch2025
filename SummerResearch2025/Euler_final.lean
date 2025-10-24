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


lemma FromOddPart_empty_of_notMem {n : ℕ} (P : n.Partition) (a : ℕ) : a ∉ P.parts → FromOddPart P a = 0 := by
  intro ha
  unfold FromOddPart
  apply Multiset.count_eq_zero_of_notMem at ha
  simp [ha, binary]

-- Each part in the multiset `FromOddPart` is positive
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

lemma FromOddPart_sum {n : ℕ} (P : n.Partition) (a : ℕ) : (FromOddPart P a).sum = (Multiset.count a P.parts) * a := by
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

-- Map from (odd) partitions to (distinct) partitions, only as a multiset : the union of `FromOddPart` of a part `a`
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
  /- Suggest to add
  theorem Multiset.sum_multiset_count.{u_4} {M : Type u_4} [AddCommMonoid M] [DecidableEq M] (s : Multiset M) :
    s.sum = (Multiset.map (fun m => Multiset.count m s • m) s.dedup).sum := by
    simpa using (Finset.sum_multiset_count s)
  to Multiset
  -/

-- Map from (odd) partitions to (distinct) partitions
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

--10/17/2025
--will come back to the difference between fromdist to odd since its simple lemmas
--which there is also not oo many differences
--inOdd also similar length


--10/24/2025
-- 1) Agreed with using Prof. Hsu from dis definition since it shows proof strategy more clearly
-- 2) fromdis map changed name of same_hof_ind to same_hof_bitIndices such that it
-- matches with binary definition which uses bitIndices on Euler_Chiyun.lean
-- 3) Will use fromdis0 as the core fromDis map.
-- Will put the other fromdis_part, eq and counteq lemmas just before when they are used
-- in rightInverse proofs for sake of readability for the whole file.
-- 4) Hanzhe will try to do a first draft of the above on EULER_final.lean file for this week.
