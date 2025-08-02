import Mathlib
/-
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Bitindices
-/

variable (n : ℕ)
variable (P : n.Partition)
#check P.parts
#check P.parts_pos
#check P.parts_sum

open Nat Partition

def binary (n : ℕ): Multiset ℕ := n.bitIndices.map fun i => 2 ^ i

lemma bitIndices_nonempty (x : ℕ) (x_neq_zero : x ≠ 0) : x.bitIndices ≠ [] := by
  intro hyp
  have x_eq_zero : x = 0 := by
    rw[← twoPowSum_bitIndices x, hyp]
    simp
  contradiction

-- Highest odd factor
#eval Nat.factorization 0 2
def hof (x : ℕ) : ℕ := x / (2 ^ (Nat.factorization x 2))
/-
def hof (x : ℕ) : ℕ :=
  if x_neq_zero : x ≠ 0 then
  x / 2 ^ (x.bitIndices[0]'
  (List.ne_nil_iff_length_pos.mp (bitIndices_nonempty x x_neq_zero)))
  else 0
-/

def ImageOfPart (n : ℕ) (P : n.Partition) (a : ℕ) : Multiset ℕ :=
  (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)
-- Maybe should have used dedup rather than toFinset

lemma ImageOfPart_pos (n : ℕ) (P : n.Partition) (a : ℕ) (ha : a ∈ P.parts) : i ∈ (ImageOfPart n P a) → i > 0 := by
  intro hi
  apply Multiset.mem_map.mp at hi
  rcases hi with ⟨y, hy, hi⟩
  have a_pos : a > 0 := P.parts_pos ha
  have y_pos : y > 0 := by
    unfold binary at hy
    apply List.mem_map.mp at hy
    rcases hy with ⟨b, hb, hy⟩
    rw [← hy]
    apply Nat.pow_pos
    simp
  rw[← hi]
  exact Nat.mul_pos y_pos a_pos

-- Map from odd partitions to partitions
def FromOdd_parts (n : ℕ) (P : n.Partition) : Multiset ℕ :=
   ∑ a ∈ P.parts.toFinset, ImageOfPart n P a

lemma FromOdd_parts_pos (n : ℕ) (P : n.Partition) : i ∈ (FromOdd_parts n P) → i > 0 := by
  rintro hi
  unfold FromOdd_parts at hi
  apply Multiset.mem_sum.mp at hi
  rcases hi with ⟨a, ha, hi⟩
  exact ImageOfPart_pos n P a (Multiset.mem_toFinset.mp ha) hi

lemma mul_comm_sum (s : Multiset ℕ) (a : ℕ) : (Multiset.map (fun x ↦ x * a) s).sum = s.sum * a:= by
  simp [Multiset.sum_map_mul_right]

lemma parts_sum (n : ℕ) (P : n.Partition) : ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a = n := by
  calc
  ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a
    = ∑ a ∈ P.parts.toFinset, (P.parts.count a) • a
    := by simp [nsmul_eq_mul]
  _ = (Multiset.map (fun x ↦ x) P.parts).sum
    := by rw [←Finset.sum_multiset_map_count]
  _ = P.parts.sum := by simp
  _ = n := by rw [P.parts_sum]

lemma FromOdd_parts_sum (n : ℕ) (P : n.Partition) : (FromOdd_parts n P).sum = n := by
  nth_rewrite 2 [←parts_sum n P]
  unfold FromOdd_parts ImageOfPart
  rw [Multiset.sum_sum]
  congr
  ext
  rw [mul_comm_sum]
  unfold binary
  congr
  rw [Multiset.sum_coe]
  rw [twoPowSum_bitIndices]

def FromOdd (n : ℕ) (P : n.Partition) : n.Partition :=
{parts := FromOdd_parts n P,
 parts_pos := FromOdd_parts_pos n P,
 parts_sum := FromOdd_parts_sum n P}

-- Map from distinct partitions to partitions
def FromDist_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (distincts n)): Multiset ℕ :=
   ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)

lemma ImageOfPart_nodup (n : ℕ) (P : n.Partition) : ∀ a ∈ P.parts.dedup, (ImageOfPart n P a).Nodup := by
  rintro a a_in_parts
  apply Multiset.Nodup.map
  -- fun y => y * a is injective
  · rintro y1 y2 heq
    dsimp at heq
    have a_nonzero : a ≠ 0 := by
      apply Nat.pos_iff_ne_zero.mp
      apply P.parts_pos
      apply Multiset.mem_toFinset.mp a_in_parts
    exact (Nat.mul_left_inj a_nonzero).mp heq
  -- binary has no duplicates
  · unfold binary
    apply Multiset.coe_nodup.mpr
    exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) (List.Sorted.nodup (bitIndices_sorted))
    /- Suggest to add
    theorem bitIndices_nodup {n : ℕ} : n.bitIndices.Nodup := List.Sorted.nodup (bitIndices_sorted)
    to Nat/BitIndices.lean
    -/

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

lemma two_pow_dvd (x : ℕ) (x_ne_zero : x ≠ 0): 2 ^ (x.factorization 2) ∣ x := by
  have two_pow_ne_zero : 2 ^ (x.factorization 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  apply (factorization_le_iff_dvd two_pow_ne_zero x_ne_zero).mp
  simp only [Nat.factorization_pow]
  intro p
  by_cases two : 2 = p
  · simp [← two]
    rw [prime_factorization_self prime_two]
    simp
  · simp
    rw [prime_factorization_diff prime_two two]
    simp

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
    _ = (2 ^ i  / 2 ^ i) * (x / (2 ^ (x.factorization 2))) := Nat.mul_div_mul_comm (dvd_refl _) (two_pow_dvd x xzero)
    _ = x / (2 ^ (x.factorization 2)) := by simp

lemma hof_eq_of_odd (a : ℕ) (a_odd : Odd a) : hof a = a := by
  unfold hof
  have : a.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact Odd.not_two_dvd_nat a_odd
  rw [this]
  simp

lemma ImageOfPart_hof (n : ℕ) (P : n.Partition) (P_odd : P ∈ (odds n)) (a : ℕ) (ha : a ∈ P.parts) : ∀ x ∈ ImageOfPart n P a, hof x = a := by
  rintro x hx
  apply Multiset.mem_map.mp at hx
  rcases hx with ⟨y, hy, hx⟩
  unfold binary at hy
  simp at hy
  rcases hy with ⟨i, hi, hy⟩
  rw [← hx, ← hy, hof_mul_two_pow a i]
  apply hof_eq_of_odd a
  apply Nat.not_even_iff_odd.mp
  exact (Finset.mem_filter.mp P_odd).2 a ha

lemma ImageOfPart_disjoint (n : ℕ) (P : n.Partition) (P_odd : P ∈ (odds n)) :
  ∀ a ∈ P.parts.dedup, ∀ b ∈ P.parts.dedup, a ≠ b → Disjoint (ImageOfPart n P a) (ImageOfPart n P b) := by
  rintro a ha b hb hneqab
  apply Multiset.disjoint_iff_ne.mpr
  rintro x hx y hy heqxy
  have heqab : a = b := by
    calc
    a = hof x := (ImageOfPart_hof n P P_odd a (Multiset.mem_dedup.mp ha) x hx).symm
    _ = hof y := by rw [heqxy]
    _ = b := ImageOfPart_hof n P P_odd b (Multiset.mem_dedup.mp hb) y hy
  contradiction


lemma InDist (n : ℕ) (P : n.Partition) (P_odd : P ∈ (odds n)) : FromOdd n P ∈ (distincts n) := by
  unfold distincts
  simp
  unfold FromOdd
  simp
  unfold FromOdd_parts
  have Finsetsum_eq_Bind: ∑ a ∈ P.parts.toFinset, ImageOfPart n P a =  Multiset.bind P.parts.dedup (ImageOfPart n P) := by
    rfl
  rw [Finsetsum_eq_Bind]
  apply Multiset.nodup_bind.mpr
  constructor
  · exact ImageOfPart_nodup n P
  · unfold Multiset.Pairwise
    let PListPart := Multiset.sort (· ≤ ·) P.parts.dedup
    have PListPart_nodup : PListPart.Nodup := by
      apply Multiset.coe_nodup.mp
      rw [Multiset.sort_eq]
      apply Multiset.nodup_dedup
    use PListPart
    constructor
    rw [Multiset.sort_eq]
    apply (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint (f := ImageOfPart n P) PListPart_nodup).mp
    rw [List.coe_toFinset]
    intro a ha b hb hneq
    simp only [Set.mem_setOf_eq] at ha hb
    unfold PListPart at ha hb
    rw [Multiset.mem_sort] at ha hb
    dsimp[Function.onFun]
    exact ImageOfPart_disjoint n P P_odd a ha b hb hneq

-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := card_bij' (FromOdd n) (FromDist n) (InDist n) (InOdd n) RightInv LeftInv
