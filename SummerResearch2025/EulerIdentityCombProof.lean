import Mathlib

open Nat Partition

-- The multiset of `2 ^ i` in the binary expansion of a natural number
def binary (a : ℕ) : Multiset ℕ := a.bitIndices.map (fun i ↦ 2 ^ i)

lemma binary_sum (a : ℕ) : (binary a).sum = a := by
  unfold binary
  rw [Multiset.sum_coe, twoPowSum_bitIndices]

lemma binary_nodup (a : ℕ) : (binary a).Nodup := by
  unfold binary
  apply Multiset.coe_nodup.mpr
  exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) (List.Sorted.nodup (bitIndices_sorted))

-- Highest odd factor of a natural number
def hof (b : ℕ) : ℕ := ordCompl[2] b
-- Alternative definition
-- def hof : ℕ → ℕ
-- | 0       => 0
-- | n@(k+1) =>
--   if n % 2 = 1 then n
--   else hof (n / 2)

-- Suggest to add
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
-- End of Suggest to Add

lemma hof_two_pow_mul (x i : ℕ) : hof (2 ^ i * x) = hof (x) := ordCompl_mul_PrimePow_eq_self x i prime_two

lemma hof_eq_iff_odd_or_zero (a : ℕ) : hof a = a ↔ (a = 0 ∨ Odd a) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_of_ordComp_eq_self a prime_two

-- Define FromOdd
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

-- Define FromDist
