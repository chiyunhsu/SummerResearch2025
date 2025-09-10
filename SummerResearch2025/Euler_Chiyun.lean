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

-- Highest odd factor of a natural number
def hof (b : ℕ) : ℕ := ordCompl[2] b

/-Suggest to add-/
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
/- -/

lemma hof_eq_iff_odd_or_zero (a : ℕ) : hof a = a ↔ (a = 0 ∨ Odd a) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_of_ordComp_eq_self a prime_two

-- Lemmas that Hanzhe uses
lemma hof_is_odd {x : ℕ} (x_ne_zero : x ≠ 0) : Odd (hof x) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_ordCompl prime_two x_ne_zero

lemma hof_ne_zero_of_ne_zero {n : ℕ} (n_ne_zero : n ≠ 0) : hof n ≠ 0 := Nat.pos_iff_ne_zero.mp (ordCompl_pos 2 n_ne_zero)

lemma hof_zero_iff_zero (n : ℕ) : n = 0 ↔ hof n = 0 := by
  constructor
  · intro n_eq_zero
    simp [n_eq_zero, hof]
  · contrapose
    exact hof_ne_zero_of_ne_zero

lemma hof_eq_of_odd {n : ℕ} (hodd : Odd n) : hof n = n := ((hof_eq_iff_odd_or_zero n).mpr (Or.inr hodd))

lemma hof_two_pow_mul (x i : ℕ) : hof (2 ^ i * x) = hof (x) := ordCompl_mul_PrimePow_eq_self x i prime_two

lemma hof_dvd (b : ℕ) : hof b ∣ b := ordCompl_dvd b 2

lemma hof_div_eq_two_pow {n : ℕ} (n_ne_zero : n ≠ 0): ∃ k : ℕ, 2 ^ k = n / hof n := by
  unfold hof
  sorry

lemma hof_mul_two_pow_eq (n : ℕ) : ∃ (k : ℕ), 2 ^ k * hof n = n := by
  exists_eq_pow_mul_and_not_dvd
  sorry

lemma hof_le (b : ℕ) : hof b ≤ b := ordCompl_le b 2

--End of Lemmas

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

-- Mapping a part `a` of a partition `P` to the multiset consisting of `the highest odd factor of a` with multiplicity ``the highest two pwer of a`
def FromDistPart (b : ℕ) : Multiset ℕ :=
  Multiset.replicate (2 ^ (Nat.factorization b 2)) (hof b)

def Same_hof {n : ℕ} (Q : n.Partition) (a : ℕ) : Multiset ℕ := (Multiset.filter (fun b ↦ (hof b = a)) Q.parts)

def Qb {n : ℕ} (Q : n.Partition) (b : ℕ) : Multiset ℕ := (Multiset.filter (fun b' ↦ (hof b' = hof b)) Q.parts)

def FromDistPart' {n : ℕ} (Q : n.Partition) (a : ℕ) : Multiset ℕ :=
--Multiset.bind (Multiset.filter (fun b ↦ (hof b = a)) P.parts) (FromDistPart)
Multiset.replicate (Multiset.map (fun b ↦ ordProj[2] b) (Same_hof Q a)).sum a

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
    apply le_of_dvd b_pos (ordProj_dvd b 2)

lemma FromDistPart'_pos {n : ℕ} (Q : n.Partition) (a : ℕ) (ha : Odd a) {a' : ℕ} :
    a' ∈ (FromDistPart' Q a) → a' > 0 := by
  rintro ha'
  apply Multiset.mem_replicate.mp at ha'
  rw [ha'.2]
  apply Nat.pos_iff_ne_zero.mpr
  intro a_eq_zero
  rw [a_eq_zero] at ha
  contradiction

lemma FromDistPart_sum (b : ℕ) : (FromDistPart b).sum = b := by
  unfold FromDistPart
  simp only [Multiset.sum_replicate, smul_eq_mul]
  by_cases b_zero : b = 0
  · simp [hof, b_zero]
  · rw [hof, ordProj_mul_ordCompl_eq_self b 2]

lemma FromDistPart'_sum {n : ℕ} (Q : n.Partition) (a : ℕ) : (FromDistPart' Q a).sum = (Same_hof Q a).sum := by
  unfold FromDistPart'
  simp only [Multiset.sum_replicate, smul_eq_mul]
  rw [← Multiset.sum_map_mul_right]
  congr
  nth_rw 2 [← Multiset.map_id (Same_hof Q a)]
  apply Multiset.map_congr rfl
  intro x hx
  simp [Same_hof] at hx
  simp [← hx.2, hof, ordProj_mul_ordCompl_eq_self]

-- Map from (distinct) partitions to (odd) partitions, only as a multiset : the union of `FromDistPart` of a part `a`
def FromDist_parts {n : ℕ} (Q : n.Partition) : Multiset ℕ :=
  Multiset.bind (Q.parts) (FromDistPart)
  --∑ b ∈ Q.parts.toFinset, (Multiset.count b Q.parts) •(FromDistPart b)

lemma Finsetsum_eq_Bind' {n : ℕ} (Q : n.Partition) :
  ∑ b ∈ Q.parts.toFinset, (Multiset.count b Q.parts) • (FromDistPart b)
  = Multiset.bind (Q.parts) (FromDistPart) := by
--  #check Multiset.count_sum
--  #check Multiset.count_sum'
  sorry

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
  exact hof_is_odd b_ne_zero

lemma LeftInvPart_self {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) : ∑ b ∈ (FromOddPart P a).toFinset,  Multiset.count a (FromDistPart b) = Multiset.count a P.parts := by
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
      exact ordProj_mul_ordCompl_eq_self b 2
    rw [Finset.sum_congr rfl lem1]
    rw [← FromOddPart_sum P a]
    rw [Finset.sum_multiset_count (FromOddPart P a)]
    apply Finset.sum_congr rfl
    rintro b hb
    have count_eq_one : Multiset.count b (FromOddPart P a) = 1 := by
      exact ((Multiset.nodup_iff_count_eq_one.mp (FromOddPart_nodup P a) b) (Multiset.mem_toFinset.mp hb))
    simp [count_eq_one]

lemma LeftInvPart_others {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) : ∀ b ∈ (FromOdd_parts P).toFinset, b ∉ (FromOddPart P a).toFinset → Multiset.count a (FromDistPart b) = 0 := by
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

lemma LeftInv {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) :
  FromDist (FromOdd P P_odd) (InDist P P_odd) = P := by
  ext a
  simp [FromDist, FromDist_parts]
  rw [← Finsetsum_eq_Bind']
  simp [Multiset.count_sum']
  have hsubset : (FromOddPart P a).toFinset ⊆ (FromOdd P P_odd).parts.toFinset := by
    apply Multiset.toFinset_subset.mpr
    simp [FromOdd, FromOdd_parts]
    apply Multiset.subset_of_le
    by_cases ha : a ∈ P.parts
    · exact Multiset.le_bind P.parts.dedup (Multiset.mem_dedup.mpr ha)
    · simp [Multiset.count_eq_zero_of_notMem ha, FromOddPart, binary]
  have lem : ∀ b ∈ (FromOdd P P_odd).parts.toFinset, Multiset.count b (FromOdd P P_odd).parts = 1 := by
    intro b hb
    rw [Multiset.mem_toFinset] at hb
    apply Multiset.nodup_iff_count_eq_one.mp
    · simpa [distincts] using (InDist P P_odd)
    · exact hb
  calc
    ∑ b ∈ (FromOdd P P_odd).parts.toFinset, Multiset.count b (FromOdd P P_odd).parts * Multiset.count a (FromDistPart b)
      = ∑ b ∈ (FromOdd P P_odd).parts.toFinset, Multiset.count a (FromDistPart b) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp [lem b hb]
    _ = Multiset.count a P.parts := ?_
  rw [← Finset.sum_subset hsubset (LeftInvPart_others P P_odd a)]
  exact LeftInvPart_self P P_odd a


lemma RightInvPart_self {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
  Multiset.count b (FromOddPart (FromDist Q Q_dist) (hof b)) = 1 := by sorry

lemma RightInvPart_others {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
  ∀ a ∈ (FromDist Q Q_dist).parts.toFinset, a ∉ ({hof b} : Finset ℕ) → Multiset.count b (FromOddPart (FromDist Q Q_dist) a) = 0 := by sorry

lemma RightInv {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) :
  FromOdd (FromDist Q Q_dist) (InOdd Q Q_dist) = Q := by
  ext b
  simp [FromOdd, FromOdd_parts]
  rw [← Finsetsum_eq_Bind]
  simp [Multiset.count_sum']

  have Q_Nodup : Q.parts.Nodup := by
    simp [distincts] at Q_dist
    exact Q_dist

  by_cases hb : b ∈ Q.parts
  · rw [Multiset.count_eq_one_of_mem Q_Nodup hb]
    have hsubset0 : (FromDistPart b) ⊆ (FromDist Q Q_dist).parts := by
      simp [FromDist]
      apply Multiset.subset_of_le
      exact Multiset.le_bind Q.parts hb

    #check Same_hof
    have hsubset' : {hof b} ⊆ (FromDist Q Q_dist).parts.toFinset := by
      sorry

    have hsubset : (∑ b' ∈ (Qb Q b).toFinset, (FromDistPart b')).toFinset ⊆ (FromDist Q Q_dist).parts.toFinset := by
      apply Multiset.toFinset_subset.mpr
      apply Multiset.subset_of_le
      unfold Finset.sum
      #check Multiset.le_sum_of_subadditive
      sorry

    rw [← Finset.sum_subset hsubset' (RightInvPart_others Q Q_dist b)]
    simp
    exact RightInvPart_self Q Q_dist b


  · rw [Multiset.count_eq_zero_of_notMem hb]
    have hsubset' : {hof b} ⊆ (FromDist Q Q_dist).parts.toFinset := by
      sorry
    rw [← Finset.sum_subset hsubset' (RightInvPart_others Q Q_dist b)]
    simp only [Finset.sum_singleton, Multiset.count_eq_zero]
    intro b_mem
    unfold FromOddPart at b_mem
    simp at b_mem
    rcases b_mem with ⟨x, hx, b_eq⟩
    unfold hof at b_eq
    have x_eq : x = ordProj[2] b := by sorry



    have lem {a : ℕ} (ha : a ∈ (FromDist Q Q_dist).parts.toFinset) : Multiset.count b (FromOddPart (FromDist Q Q_dist) a) = 0 := by
      rw [Multiset.count_eq_zero_of_notMem]
      rw [Multiset.mem_toFinset] at ha
      simp [FromDist, FromDist_parts] at ha
      --rcases ha with ⟨b', hb', a_from_b'⟩
      --have hof_b'_eq_a : hof b' = a := by
      --  unfold FromDistPart at a_from_b'
      --  rw [Multiset.mem_replicate] at a_from_b'
      --  exact a_from_b'.2.symm
      by_contra contra
      --have hof_b_eq_a : hof b = a := FromOddPart_hof (FromDist Q Q_dist) (InOdd Q Q_dist) a b contra
      simp [FromOddPart] at contra
      rcases contra with ⟨x, hx, x_mul_a_eq_b⟩
      --simp [FromDistPart] at a_from_b'
      simp [FromDist, FromDist_parts] at hx
      rw [← Finsetsum_eq_Bind'] at hx
      rw [Multiset.count_sum'] at hx
      have : ∑ b' ∈ Q.parts.toFinset, Multiset.count a (Multiset.count b' Q.parts • FromDistPart b')
      = ∑ b' ∈ Q.parts.toFinset, ordProj[2] b' := by
        calc
          ∑ b' ∈ Q.parts.toFinset, Multiset.count a (Multiset.count b' Q.parts • FromDistPart b')
       =  ∑ b' ∈ Q.parts.toFinset, Multiset.count a (FromDistPart b') := by
            apply Finset.sum_congr rfl
            intro b' hb'
            congr
            have : Multiset.count b' Q.parts = 1 := Multiset.count_eq_one_of_mem Q_Nodup (Multiset.mem_toFinset.mp hb')
            simp [this]
      _ = ∑ x ∈ Q.parts.toFinset, ordProj[2] x := by
          apply Finset.sum_congr rfl
          intro b' hb'

#check bitIndices_twoPowsum
#check Multiset.sort
lemma binary_reverse (I : Finset ℕ) : (Multiset.map (fun i ↦ 2 ^ i) I.val).sum.bitIndices = I.val := by
  let I_sort := Finset.sort (· ≤ ·) I
  have h : (List.map (fun i => 2 ^ i) I_sort).sum.bitIndices = I_sort := bitIndices_twoPowsum (Finset.sort_sorted_lt I)

  #check List.toFinset
  have h' : ((List.map (fun i => 2 ^ i) I_sort).sum.bitIndices).toFinset = I := by
    rw [h]
    exact Finset.sort_toFinset (· ≤ ·) I
  rw [← Finset.sort_toFinset (· ≤ ·) I]

#check twoPowSum_bitIndices
#check List.map_id''


-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := Finset.card_bij' FromOdd FromDist InDist InOdd LeftInv RightInv
