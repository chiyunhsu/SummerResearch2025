import Mathlib
/-
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Bitindices
-/

variable (n : ℕ)

open Nat Partition

theorem EulerIdentity : (odds n).card = (distincts n).card := by
  sorry

-- Prove cardinality of two sets are the same by establishing a bijection

open Finset
#check card_bij'

variable (P : n.Partition)
#check P.parts
#check P.parts_pos
#check P.parts_sum

#check Multiset.toFinset_sum_count_nsmul_eq

variable (a : ℕ) (h : a ∈ P.parts)
-- α, β are both the type n.Partition
-- s is the set of odd partitions of n
-- t is the set of distinct partitions of n

def binary (n : ℕ): Multiset ℕ := n.bitIndices.map fun i => 2 ^ i

def FromOdd (n : ℕ) : ∀ P ∈ (odds n), Multiset ℕ :=
  fun P hP => ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ a * y)

lemma mul_comm_sum (s : Multiset ℕ) (a : ℕ) : (Multiset.map (fun x ↦ a * x) s).sum = a * s.sum := by
  rw [Multiset.sum_map_mul_left]
  simp

lemma lemma3 (n : ℕ) (P : n.Partition) : n = ∑ a ∈ P.parts.toFinset, a * (P.parts.count a) := by
  sorry

lemma FromOddisPartition (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)) :
  (FromOdd n P hP).sum = n := by
  nth_rewrite 2 [lemma3 n P]
  unfold FromOdd
  rw [Multiset.sum_sum]
  congr
  ext
  rw [mul_comm_sum]
  unfold binary
  congr
  rw [Multiset.sum_coe]
  rw [twoPowSum_bitIndices]


#check Multiset.sum_join
#check twoPowSum_bitIndices
--(List.map (fun i => 2 ^ i) n.bitIndices).sum = n

#check ofSums
#check ofMultiset
#check (Multiset.count 1 P.parts)
#check Multiset
#check Multiset.toFinset
