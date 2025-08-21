import Mathlib
/-
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Bitindices
-/

open Nat Partition

-- The multiset of `2 ^ i` in the binary expansion of a natural number
def binary (n : ℕ): Multiset ℕ := n.bitIndices.map (fun i ↦ 2 ^ i)

lemma binary_sum (n : ℕ) : (binary n).sum = n := by
  unfold binary
  rw [Multiset.sum_coe]
  rw [twoPowSum_bitIndices]

lemma binary_nodup (n : ℕ) : (binary n).Nodup := by
  unfold binary
  apply Multiset.coe_nodup.mpr
  exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) (List.Sorted.nodup (bitIndices_sorted))
  /- Suggest to add
  theorem bitIndices_nodup {n : ℕ} : n.bitIndices.Nodup := (List.Sorted.nodup (bitIndices_sorted))
  to Nat/BitIndices.lean
  -/

-- Mapping a part `a` of a partition `P` to the multiset consisting of `a * 2 ^ i`, where `2 ^ i` is in the binary expansion of the multiplicity of `a`

def FromOddPart (count a : ℕ) : Multiset ℕ :=
  (binary count).map (fun x ↦ x * a)

-- Each part in the multiset `FromOddPart` is positive
lemma FromOddPart_pos (count a : ℕ) (a_pos : a > 0) {b : ℕ} :
    b ∈ (FromOddPart count a) → b > 0 := by
  intro hb
  apply Multiset.mem_map.mp at hb
  rcases hb with ⟨x, hx, hb⟩
  have x_pos : x > 0 := by
    unfold binary at hx
    apply List.mem_map.mp at hx
    rcases hx with ⟨i, hi, hx⟩
    rw [← hx]
    exact Nat.pow_pos zero_lt_two
  rw [← hb]
  exact Nat.mul_pos x_pos a_pos

lemma FromOddPart_sum (count a : ℕ) : (FromOddPart count a).sum = count * a := by
  unfold FromOddPart
  rw [Multiset.sum_map_mul_right, Multiset.map_id']
  rw [binary_sum]

-- Map from (odd) partitions to (distinct) partitions, only as a multiset : the union of `FromOddPart` of a part `a`
def FromOdd_parts (n : ℕ) (P : n.Partition) : Multiset ℕ :=
  --Multiset.bind (P.parts.dedup) (FromOddPart n P)
  ∑ a ∈ P.parts.toFinset, (FromOddPart (Multiset.count a P.parts) a)

lemma Finsetsum_eq_Bind (n : ℕ) (P : n.Partition) :
  ∑ a ∈ P.parts.toFinset, (FromOddPart (Multiset.count a P.parts) a) = Multiset.bind P.parts.dedup FromOddPart (Multiset.count · P.parts)) := by sorry

-- Each part in the multiset `FromOdd_parts` is positive
lemma FromOdd_parts_pos (n : ℕ) (P : n.Partition) {b : ℕ} : b ∈ (FromOdd_parts n P) → b > 0 := by
  rintro hb
  unfold FromOdd_parts at hb
  --apply Multiset.mem_bind.mp at hb
  apply Multiset.mem_sum.mp at hb
  rcases hb with ⟨a, ha, hb⟩
  have a_pos : a > 0 := P.parts_pos (Multiset.mem_toFinset.mp ha)
  exact FromOddPart_pos (Multiset.count a P.parts) a a_pos hb

-- The sum of different parts `a` multiplied with its multiplicity is equal to `n`
lemma parts_sum (n : ℕ) (P : n.Partition) : ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a = n := by
  calc
  ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a
    = ∑ a ∈ P.parts.toFinset, (P.parts.count a) • a
    := by simp only [smul_eq_mul]
  _ = (Multiset.map (fun x ↦ x) P.parts).sum
    := by rw [← Finset.sum_multiset_map_count]
  _ = P.parts.sum := by simp
  _ = n := by rw [P.parts_sum]

-- The image of a partition of `n` under `FromOdd_parts` is still a partition of `n`
lemma FromOdd_parts_sum (n : ℕ) (P : n.Partition) : (FromOdd_parts n P).sum = n := by
  nth_rewrite 2 [← parts_sum n P]
  unfold FromOdd_parts
  --Add the next line when using `bind` definition in `FromOdd_parts`
  --rw [← Finsetsum_eq_Bind n P]
  rw [Multiset.sum_sum]
  apply Finset.sum_congr rfl
  rintro a _
  exact FromOddPart_sum (Multiset.count a P.parts) a

-- Map from (odd) partitions to (distinct) partitions
def FromOdd (n : ℕ) (P : n.Partition) (_ : P ∈ odds n) : n.Partition :=
{ parts := FromOdd_parts n P,
  parts_pos := FromOdd_parts_pos n P,
  parts_sum := FromOdd_parts_sum n P }

lemma FromOddPart_nodup (n : ℕ) (P : n.Partition) :
    ∀ a ∈ P.parts.dedup, (FromOddPart (Multiset.count a P.parts) a).Nodup := by
  rintro a a_in_parts
  apply Multiset.Nodup.map
  -- fun x => x * a is injective
  · rintro x1 x2 heq
    dsimp at heq
    have a_ne_zero : a ≠ 0 := by
      apply Nat.pos_iff_ne_zero.mp
      apply P.parts_pos
      apply Multiset.mem_toFinset.mp a_in_parts
    exact (Nat.mul_left_inj a_ne_zero).mp heq
  -- binary has no duplicates
  · exact binary_nodup _

-- Highest odd factor of a natural number
def hof (b : ℕ) : ℕ := b / (2 ^ (Nat.factorization b 2))
-- Use `ordProj[p] n` with `p = 2` instead.
-- ordProj_dvd (n p : ℕ) : ordProj[p] n ∣ n

lemma prime_factorization_self {p : ℕ} (hp : Nat.Prime p) : p.factorization p = 1 := by
  have : (p^1).factorization = Finsupp.single p 1 := Prime.factorization_pow (k := 1) hp
  simp at this
  rw [this]
  simp

lemma prime_factorization_diff {p n : ℕ} (hp : Nat.Prime p) (h : p ≠ n): p.factorization n = 0 := by
  have : (p^1).factorization = Finsupp.single p 1 := Prime.factorization_pow (k := 1) hp
  simp at this
  rw [this]
  exact Finsupp.single_eq_of_ne h

lemma two_pow_dvd (x : ℕ) : 2 ^ (x.factorization 2) ∣ x := by
  have two_pow_ne_zero : 2 ^ (x.factorization 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  by_cases x_zero : x = 0
  · simp [x_zero]
  apply (factorization_le_iff_dvd two_pow_ne_zero x_zero).mp
  simp only [Nat.factorization_pow]
  intro p
  by_cases two : 2 = p
  · simp [← two]
    rw [prime_factorization_self prime_two]
    simp
  · simp
    rw [prime_factorization_diff prime_two two]
    simp

lemma two_pow_mul_hof_eq_self (x : ℕ) : 2 ^ (x.factorization 2) * hof x = x := by
  unfold hof
  exact Nat.mul_div_cancel_left' (two_pow_dvd x)

lemma hof_mul_two_pow (x i : ℕ) : hof (2 ^ i * x) = hof (x) := by
  unfold hof
  by_cases xzero : x = 0
  · simp [xzero]
  · have two_pow_x_ne_zero : 2 ^ i * x ≠ 0 := by
      apply Nat.mul_ne_zero
      exact pow_ne_zero i two_ne_zero
      exact xzero
    simp [xzero, two_pow_x_ne_zero]
    simp [prime_factorization_self prime_two]
    calc
    (2 ^ i * x) / 2 ^ (i + x.factorization 2) = (2 ^ i * x) / (2 ^ i * 2 ^ (x.factorization 2)) := by rw [Nat.pow_add]
    _ = (2 ^ i  / 2 ^ i) * (x / (2 ^ (x.factorization 2))) := Nat.mul_div_mul_comm (dvd_refl _) (two_pow_dvd x)
    _ = x / (2 ^ (x.factorization 2)) := by simp

lemma hof_eq_of_odd (a : ℕ) (a_odd : Odd a) : hof a = a := by
  unfold hof
  have : a.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact Odd.not_two_dvd_nat a_odd
  rw [this]
  simp

lemma hof_odd (x : ℕ) (x_ne_zero : x ≠ 0) : Odd (hof x) := by
  have hofx_ne_zero : hof x ≠ 0 := by
    unfold hof
    rw [Nat.div_ne_zero_iff]
    constructor
    · exact pow_ne_zero _ two_ne_zero
    · apply le_of_dvd (zero_lt_iff.mpr x_ne_zero) (two_pow_dvd x)
  have pow_succ_not_dvd : ¬ 2 ^ (x.factorization 2 + 1) ∣ x := pow_succ_factorization_not_dvd x_ne_zero prime_two
  by_contra contra
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at contra
  rw [← factorization_le_iff_dvd two_ne_zero hofx_ne_zero] at contra
  have pow_succ_dvd : 2 ^ (x.factorization 2 + 1) ∣ x := by
    rw [← factorization_le_iff_dvd (pow_ne_zero _ two_ne_zero) x_ne_zero]
    nth_rewrite 2 [← two_pow_mul_hof_eq_self x]
    rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hofx_ne_zero]
    intro p
    by_cases two : 2 = p
    · simp [← two]
      rw [prime_factorization_self prime_two]
      simp
      have contra_two := contra 2
      rw [prime_factorization_self prime_two] at contra_two
      exact contra_two
    · simp
      rw [prime_factorization_diff prime_two two]
      simp
  contradiction

lemma FromOddPart_hof (count a : ℕ) (a_odd : Odd a) :
    ∀ x ∈ FromOddPart count a, hof x = a := by
  rintro x hx
  apply Multiset.mem_map.mp at hx
  rcases hx with ⟨y, hy, hx⟩
  unfold binary at hy
  simp at hy
  rcases hy with ⟨i, hi, hy⟩
  rw [← hx, ← hy, hof_mul_two_pow a i]
  exact hof_eq_of_odd a a_odd

lemma FromOddPart_disjoint (n : ℕ) (P : n.Partition) (P_odd : P ∈ (odds n)) :
    ∀ a ∈ P.parts.dedup, ∀ b ∈ P.parts.dedup, a ≠ b → Disjoint (FromOddPart (Multiset.count a P.parts) a) (FromOddPart (Multiset.count b P.parts) b) := by
  rintro a ha b hb hneqab
  apply Multiset.disjoint_iff_ne.mpr
  rintro x hx y hy heqxy
  have a_odd : Odd a := by
    apply Nat.not_even_iff_odd.mp
    exact (Finset.mem_filter.mp P_odd).2 a (Multiset.mem_dedup.mp ha)
  have b_odd : Odd b := by
    apply Nat.not_even_iff_odd.mp
    exact (Finset.mem_filter.mp P_odd).2 b (Multiset.mem_dedup.mp hb)
  have heqab : a = b := by
    calc
    a = hof x := (FromOddPart_hof (Multiset.count a P.parts) a a_odd x hx).symm
    _ = hof y := by rw [heqxy]
    _ = b := FromOddPart_hof (Multiset.count b P.parts) b b_odd y hy
  contradiction

lemma InDist (n : ℕ) (P : n.Partition) (P_odd : P ∈ (odds n)) : FromOdd n P P_odd ∈ (distincts n) := by
  unfold distincts
  simp
  unfold FromOdd
  simp
  unfold FromOdd_parts
  rw [Finsetsum_eq_Bind n P]
  apply Multiset.nodup_bind.mpr
  constructor
  · exact FromOddPart_nodup n P
  · unfold Multiset.Pairwise
    let PListPart := Multiset.sort (· ≤ ·) P.parts.dedup
    have PListPart_nodup : PListPart.Nodup := by
      apply Multiset.coe_nodup.mp
      rw [Multiset.sort_eq]
      apply Multiset.nodup_dedup
    use PListPart
    constructor
    rw [Multiset.sort_eq]
    apply (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint (f := FromOddPart n P) PListPart_nodup).mp
    rw [List.coe_toFinset]
    intro a ha b hb hneq
    simp only [Set.mem_setOf_eq] at ha hb
    unfold PListPart at ha hb
    rw [Multiset.mem_sort] at ha hb
    dsimp[Function.onFun]
    exact FromOddPart_disjoint n P P_odd a ha b hb hneq

-- Mapping a part `a` of a partition `P` to the multiset consisting of `the highest odd factor of a` with multiplicity ``the highest two pwer of a`
def FromDistPart (b : ℕ) : Multiset ℕ :=
  Multiset.replicate (2 ^ (Nat.factorization b 2)) (hof b)

-- Each part in the multiset `FromDistPart` is positive
lemma FromDistPart_pos {a : ℕ} (n : ℕ) (Q : n.Partition) (b : ℕ) (hb : b ∈ Q.parts) :
    a ∈ (FromDistPart b) → a > 0 := by
  rintro ha
  apply Multiset.mem_replicate.mp at ha
  rw [ha.2]
  apply Nat.pos_iff_ne_zero.mpr
  apply Nat.div_ne_zero_iff.mpr
  constructor
  · exact pow_ne_zero _ two_ne_zero
  · have b_pos : b > 0 := Q.parts_pos hb
    apply le_of_dvd b_pos (two_pow_dvd b)

-- Map from (distinct) partitions to (odd) partitions, only as a multiset : the union of `FromDistPart` of a part `a`
def FromDist_parts (n : ℕ) (Q : n.Partition) : Multiset ℕ :=
  ∑ b ∈ Q.parts.toFinset, FromDistPart b

lemma FromDist_parts_pos {a : ℕ} (n : ℕ) (Q : n.Partition) : a ∈ (FromDist_parts n Q) → a > 0 := by
  rintro ha
  unfold FromDist_parts at ha
  apply Multiset.mem_sum.mp at ha
  rcases ha with ⟨b, hb, ha⟩
  exact FromDistPart_pos n Q b (Multiset.mem_toFinset.mp hb) ha

lemma FromDistPart_sum (b : ℕ) : (FromDistPart b).sum = b := by
  unfold FromDistPart
  simp only [Multiset.sum_replicate, smul_eq_mul]
  by_cases b_zero : b = 0
  · simp [hof, b_zero]
  · rw [two_pow_mul_hof_eq_self b]

lemma FromDist_parts_sum (n : ℕ) (Q : n.Partition) (Q_dist : Q ∈ distincts n) : (FromDist_parts n Q).sum = n := by
  nth_rewrite 2 [← parts_sum n Q]
  --Add the next line when using `bind` definition in `FromOdd_parts`
  --rw [← Finsetsum_eq_Bind n P]
  unfold FromDist_parts
  rw [Multiset.sum_sum]
  apply Finset.sum_congr rfl
  rintro b hb
  rw [FromDistPart_sum b]
  have count_eq_one : Multiset.count b Q.parts = 1 := by
    simp [distincts] at Q_dist
    rw [Multiset.nodup_iff_count_eq_one] at Q_dist
    exact Q_dist b (Multiset.mem_toFinset.mp hb)
  simp only [count_eq_one, one_mul]

def FromDist (n : ℕ) (Q : n.Partition) (hQ : Q ∈ distincts n) : n.Partition :=
  { parts := FromDist_parts n Q
    parts_pos := FromDist_parts_pos n Q
    parts_sum := FromDist_parts_sum n Q hQ }

lemma InOdd (n : ℕ) (Q : n.Partition) (Q_dist : Q ∈ distincts n) : FromDist n Q Q_dist ∈ odds n := by
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
  exact hof_odd b b_ne_zero

lemma LeftInvPart_self (n : ℕ) (P : n.Partition) (hP : P ∈ odds n) (a : ℕ) : ∑ b ∈ (FromOddPart n P a).toFinset, Multiset.count a (FromDistPart b) = Multiset.count a P.parts := by
  unfold FromDistPart
  have lem2 (b : ℕ) (hb : b ∈ (FromOddPart n P a).toFinset) : Multiset.count a (Multiset.replicate (2 ^ b.factorization 2) (hof b)) = Multiset.count a (Multiset.replicate (2 ^ b.factorization 2) a) := by
    by_cases ha : a ∈ P.parts
    · congr
      exact FromOddPart_hof n P hP a ha b (Multiset.mem_toFinset.mp hb)
    · have FromOddPart_empty : FromOddPart n P a = 0 := by
        unfold FromOddPart
        apply Multiset.count_eq_zero_of_notMem at ha
        simp [ha, binary]
      rw [FromOddPart_empty] at hb
      contradiction
  rw [Finset.sum_congr rfl lem2]
  simp
  by_cases a_zero : a = 0
  · sorry
  · apply (Nat.mul_left_inj a_zero).mp
    rw [Finset.sum_mul]
    have lem1 (b : ℕ) (hb : b ∈ (FromOddPart n P a).toFinset) : (2 ^ b.factorization 2) * a = b := by
      rw [FromOddPart_hof n P hP a ha b (Multiset.mem_toFinset.mp hb)]
    rw [Finset.sum_congr rfl lem1]
    rw [← FromOddPart_sum n P a]
    rw [Finset.sum_multiset_count (FromOddPart n P a)]
    apply Finset.sum_congr rfl
    rintro b hb
    have ha : a ∈ P.parts.dedup := by sorry
    have count_eq_one : Multiset.count b (FromOddPart n P a) = 1 := by
      exact ((Multiset.nodup_iff_count_eq_one.mp (FromOddPart_nodup n P a ha) b) (Multiset.mem_toFinset.mp hb))
    simp [count_eq_one]

lemma parts_sum' (n : ℕ) (P : n.Partition) : ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a = n := by
  calc
  ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a
    = ∑ a ∈ P.parts.toFinset, (P.parts.count a) • a
    := by simp only [smul_eq_mul]
  _ = (Multiset.map (fun x ↦ x) P.parts).sum
    := by rw [← Finset.sum_multiset_map_count]
  _ = P.parts.sum := by simp
  _ = n := by rw [P.parts_sum]

lemma LeftInvPart_others (n : ℕ) (P : n.Partition) (hP : P ∈ odds n) (a : ℕ) : ∀ b ∈ (FromOdd_parts n P).toFinset, b ∉ (FromOddPart n P a).toFinset → Multiset.count a (FromDistPart b) = 0 := by
  sorry

lemma LeftInv (n : ℕ) (P : n.Partition) (hP : P ∈ odds n) : FromDist n (FromOdd n P hP) (InDist n P hP) = P := by
  ext a
  simp [FromDist, FromDist_parts, FromOdd]
  simp [Multiset.count_sum']
  have hsubset : (FromOddPart n P a).toFinset ⊆ (FromOdd_parts n P).toFinset := by
    apply Multiset.toFinset_subset.mpr
    simp [FromOdd_parts]
    rw [Finsetsum_eq_Bind n P]
    apply Multiset.subset_of_le
    by_cases ha : a ∈ P.parts
    · exact Multiset.le_bind P.parts.dedup (Multiset.mem_dedup.mpr ha)
    · simp [Multiset.count_eq_zero_of_notMem ha, FromOddPart, binary]
  rw [← Finset.sum_subset hsubset (LeftInvPart_others n P hP a)]
  exact LeftInvPart_self n P hP a

lemma RightInv (n : ℕ) (P : n.Partition) (hP : P ∈ distincts n) : FromOdd n (FromDist n P hP) (InOdd n P hP) = P := by
  sorry

-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := Finset.card_bij' (FromOdd n) (FromDist n) (InDist n) (InOdd n) (LeftInv n) (RightInv n)
