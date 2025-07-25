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
open Finset

def binary (n : ℕ): Multiset ℕ := n.bitIndices.map fun i => 2 ^ i

-- Map from odd partitions to partitions
def FromOdd_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (odds n)): Multiset ℕ :=
   ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)

lemma FromOdd_parts_pos (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)) : i ∈ (FromOdd_parts n P hP) → i > 0 := by
  rintro hi
  unfold FromOdd_parts at hi
  apply Multiset.mem_sum.mp at hi
  rcases hi with ⟨a, ha, hi⟩
  apply Multiset.mem_map.mp at hi
  rcases hi with ⟨y, hy, hi⟩
  have a_pos : a > 0 := by
    apply P.parts_pos
    exact Multiset.mem_toFinset.mp ha
  have y_pos : y > 0 := by
    unfold binary at hy
    apply List.mem_map.mp at hy
    rcases hy with ⟨b, hb, hy⟩
    rw [← hy]
    apply Nat.pow_pos
    simp
  rw[← hi]
  exact Nat.mul_pos y_pos a_pos

lemma mul_comm_sum (s : Multiset ℕ) (a : ℕ) : (Multiset.map (fun x ↦  x * a) s).sum = s.sum * a:= by
  rw [Multiset.sum_map_mul_right]
  simp

lemma parts_sum (n : ℕ) (P : n.Partition) : ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a = n := by
  calc
  ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a
    = ∑ a ∈ P.parts.toFinset, (P.parts.count a) • a
    := by simp [nsmul_eq_mul]
  _ = (Multiset.map (fun x ↦ x) P.parts).sum
    := by rw [←Finset.sum_multiset_map_count]
  _ = P.parts.sum := by simp
  _ = n := by rw [P.parts_sum]

lemma FromOdd_parts_sum (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)) : (FromOdd_parts n P hP).sum = n := by
  nth_rewrite 2 [←parts_sum n P]
  unfold FromOdd_parts
  rw [Multiset.sum_sum]
  congr
  ext
  rw [mul_comm_sum]
  unfold binary
  congr
  rw [Multiset.sum_coe]
  rw [twoPowSum_bitIndices]

def FromOdd (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)): n.Partition :=
{parts := FromOdd_parts n P hP,
 parts_pos := FromOdd_parts_pos n P hP,
 parts_sum := FromOdd_parts_sum n P hP}

-- Map from distinct partitions to partitions
def FromDist_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (distincts n)): Multiset ℕ :=
   ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)

-- Image of FromOdd is in distinct partitions
lemma InDist (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)) : FromOdd n P hP ∈ (distincts n) := by
  unfold distincts
  simp
  unfold FromOdd
  simp
  unfold FromOdd_parts
  #check Multiset.nodup_bind



#check distincts n

#check Multiset.sum_join
#check twoPowSum_bitIndices
--(List.map (fun i => 2 ^ i) n.bitIndices).sum = n

#check ofSums
#check ofMultiset
#check (Multiset.count 1 P.parts)
#check Multiset
#check Multiset.toFinset
#check Multiset.smul_sum


-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := card_bij' (FromOdd n) (FromDist n) (InDist n) (InOdd n) RightInv LeftInv
