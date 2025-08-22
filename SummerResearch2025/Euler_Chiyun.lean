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
def binary (a : ℕ) : Multiset ℕ := a.bitIndices.map (fun i ↦ 2 ^ i)

lemma binary_sum (a : ℕ) : (binary a).sum = a := by
  unfold binary
  rw [Multiset.sum_coe]
  rw [twoPowSum_bitIndices]

lemma binary_nodup (a : ℕ) : (binary a).Nodup := by
  unfold binary
  apply Multiset.coe_nodup.mpr
  exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) (List.Sorted.nodup (bitIndices_sorted))
  /- Suggest to add
  theorem bitIndices_nodup {n : ℕ} : n.bitIndices.Nodup := (List.Sorted.nodup (bitIndices_sorted))
  to Nat/BitIndices.lean
  -/

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
  --∑ a ∈ P.parts.toFinset, FromOddPart P a

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
  have ver_Finset := (Finset.sum_multiset_count P.parts).symm
  simpa [P.parts_sum] using ver_Finset
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

-- Highest odd factor of a natural number
def hof (b : ℕ) : ℕ := b / (ordProj[2] b)

lemma prime_factorization_self {p : ℕ} (hp : Nat.Prime p) : p.factorization p = 1 := by
  have : (p ^ 1).factorization = Finsupp.single p 1 := Prime.factorization_pow (k := 1) hp
  simp at this
  rw [this]
  simp

lemma prime_factorization_diff {p n : ℕ} (hp : Nat.Prime p) (h : p ≠ n): p.factorization n = 0 := by
  have : (p ^ 1).factorization = Finsupp.single p 1 := Prime.factorization_pow (k := 1) hp
  simp at this
  rw [this]
  exact Finsupp.single_eq_of_ne h

lemma two_pow_dvd (b : ℕ) : (ordProj[2] b) ∣ b := ordProj_dvd b 2

lemma two_pow_mul_hof_eq_self (b : ℕ) : (ordProj[2] b) * hof b = b := Nat.mul_div_cancel_left' (two_pow_dvd b)

lemma hof_two_pow_mul (x i : ℕ) : hof (2 ^ i * x) = hof (x) := by
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

lemma hof_eq_iff_odd_or_zero (a : ℕ)  : hof a = a ↔ (Odd a ∨ a = 0) := by
  unfold hof
  constructor
  · intro h
    rw [Nat.div_eq_iff_eq_mul_right (Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero)) (two_pow_dvd a)] at h
    by_cases a_zero : a = 0
    · right; exact a_zero
    · left;
      simp [a_zero] at h
      rw [← Nat.not_even_iff_odd]
      rw [not_iff_not.mpr even_iff_two_dvd]
      rw [factorization_eq_zero_iff] at h
      rcases h with (h1 | (h2 | h3))
      · contradiction
      · exact h2
      · contradiction
  · rintro (a_odd | a_zero)
    · have : a.factorization 2 = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        exact Odd.not_two_dvd_nat a_odd
      rw [this]
      simp
    · simp [a_zero]

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
    apply hof_eq_of_odd a
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

-- Mapping a part `a` of a partition `P` to the multiset consisting of `the highest odd factor of a` with multiplicity ``the highest two pwer of a`
def FromDistPart (b : ℕ) : Multiset ℕ :=
  Multiset.replicate (2 ^ (Nat.factorization b 2)) (hof b)

-- Each part in the multiset `FromDistPart` is positive
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
    apply le_of_dvd b_pos (two_pow_dvd b)

lemma FromDistPart_sum (b : ℕ) : (FromDistPart b).sum = b := by
  unfold FromDistPart
  simp only [Multiset.sum_replicate, smul_eq_mul]
  by_cases b_zero : b = 0
  · simp [hof, b_zero]
  · rw [two_pow_mul_hof_eq_self b]

-- Map from (distinct) partitions to (odd) partitions, only as a multiset : the union of `FromDistPart` of a part `a`
def FromDist_parts {n : ℕ} (Q : n.Partition) : Multiset ℕ :=
  Multiset.bind (Q.parts) (FromDistPart)

lemma FromDist_parts_pos {n : ℕ} (Q : n.Partition) {a : ℕ} : a ∈ (FromDist_parts Q) → a > 0 := by
  rintro ha
  unfold FromDist_parts at ha
  apply Multiset.mem_bind.mp at ha
  rcases ha with ⟨b, hb, ha⟩
  exact FromDistPart_pos Q b hb ha

lemma FromDist_parts_sum {n : ℕ} (Q : n.Partition) : (FromDist_parts Q).sum = n := by
  unfold FromDist_parts
  rw [Multiset.sum_bind]
  rw [(funext FromDistPart_sum)]
  rw [Multiset.map_id']
  exact Q.parts_sum

def FromDist {n : ℕ} (Q : n.Partition) (_ : Q ∈ distincts n) : n.Partition :=
  { parts := FromDist_parts Q
    parts_pos := FromDist_parts_pos Q
    parts_sum := FromDist_parts_sum Q }

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
  exact hof_odd b b_ne_zero

lemma LeftInvPart_self {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) : ∑ b ∈ (FromOddPart P a).toFinset, Multiset.count a (FromDistPart b) = Multiset.count a P.parts := by
  unfold FromDistPart
  have lem2 (b : ℕ) (hb : b ∈ (FromOddPart P a).toFinset) : Multiset.count a (Multiset.replicate (2 ^ b.factorization 2) (hof b)) = Multiset.count a (Multiset.replicate (2 ^ b.factorization 2) a) := by
      congr
      exact FromOddPart_hof P P_odd a b (Multiset.mem_toFinset.mp hb)
  rw [Finset.sum_congr rfl lem2]
  simp
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
      exact two_pow_mul_hof_eq_self b
    rw [Finset.sum_congr rfl lem1]
    rw [← FromOddPart_sum P a]
    rw [Finset.sum_multiset_count (FromOddPart P a)]
    apply Finset.sum_congr rfl
    rintro b hb
    have count_eq_one : Multiset.count b (FromOddPart P a) = 1 := by
      exact ((Multiset.nodup_iff_count_eq_one.mp (FromOddPart_nodup P a) b) (Multiset.mem_toFinset.mp hb))
    simp [count_eq_one]

lemma LeftInvPart_others {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) : ∀ b ∈ (FromOdd_parts P).toFinset, b ∉ (FromOddPart P a).toFinset → Multiset.count a (FromDistPart b) = 0 := by

  sorry

lemma LeftInv {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) :
  FromDist (FromOdd P P_odd) (InDist P P_odd) = P := by
  ext a
  simp [FromDist, FromDist_parts, FromOdd]
  simp [Multiset.count_bind]
  have hsubset : (FromOddPart P a).toFinset ⊆ (FromOdd_parts P).toFinset := by
    apply Multiset.toFinset_subset.mpr
    simp [FromOdd_parts]
    apply Multiset.subset_of_le
    by_cases ha : a ∈ P.parts
    · exact Multiset.le_bind P.parts.dedup (Multiset.mem_dedup.mpr ha)
    · simp [Multiset.count_eq_zero_of_notMem ha, FromOddPart, binary]
  rw [← Finset.sum_subset hsubset (LeftInvPart_others P P_odd a)]
  exact LeftInvPart_self P P_odd a

lemma RightInvPart_self {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
  Multiset.count b (FromOddPart (FromDist Q Q_dist) (hof b)) = 1 := by
  simp [FromOddPart]
  sorry

lemma RightInvPart_others {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
  ∀ a ∈ (FromDist_parts Q).toFinset, a ≠ hof b → Multiset.count b (FromOddPart (FromDist Q Q_dist)  a) = 0 := by sorry

lemma RightInv {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) :
  FromOdd (FromDist Q Q_dist) (InOdd Q Q_dist) = Q := by
  ext b
  simp [FromOdd, FromOdd_parts]
  simp [Multiset.count_sum']
  have Q_Nodup : Q.parts.Nodup := by
    simp [distincts] at Q_dist
    exact Q_dist
  by_cases hb : b ∈ Q.parts
  · rw [Multiset.count_eq_one_of_mem Q_Nodup hb]

  · rw [Multiset.count_eq_zero_of_notMem hb]
    have FromOdd_empty : FromOdd Q = 0 := by
      unfold FromOdd
      apply Multiset.count_eq_zero_of_notMem at hb
      simp [hb, binary]
    rw [FromOdd_empty] at hb
    contradiction

-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := Finset.card_bij' FromOdd FromDist InDist InOdd LeftInv RightInv
