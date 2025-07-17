import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Multiset.Count

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

variable (a : ℕ) (h : a ∈ P.parts)
def da : List ℕ := digits 2 a

-- α, β are both the type n.Partition
-- s is the set of odd partitions of n
-- t is the set of distinct partitions of n

def Fun : ℕ → ℕ :=
  fun n =>
    let m := 0
    m + n
#eval Fun 5

def Fun2 : ℕ → ℕ :=
  fun n =>
    (List.range n).foldl (fun m i => m + i) 0
/-
def Fun3 : ℕ → ℕ :=
  fun n =>
    let m := 0
    for i in [0:n] do
      m := m + i
    m
-/

def oddtodistinct : ∀ P ∈ (odds n), n.Partition :=
  fun P hP => let Q := Multiset.empty ℕ
    for a ∈ Multiset.toFinset P.parts do
      let MultOfa := (Multiset.count a P.parts)
      let BinaryMultOfa := digits 2 MultOfa
      let Length := BinaryMultOfa.length
      for i in [0:Length] do
        Q = Q + a * 2^i * BinaryMultOfa[i]
    ofMultiset Q

/-
def oddtodistinct : ∀ P ∈ (odds n), n.Partition :=
  fun P hP => let Q := Multiset.empty ℕ
    for a ∈ Multiset.toFinset P.parts do
      let MultOfa := (Multiset.count a P.parts)
      let BinaryMultOfa := digits 2 MultOfa
      let Length := BinaryMultOfa.length
      for i in [0:Length] do
        Q = Q + a * 2^i * BinaryMultOfa[i]
    ofMultiset Q
-/

-- MultOfa := (Multiset.count a P.parts) is the number of a in P.parts
-- BinaryMultOfa := digits 2 Ma is the binary representation of the count. It is a list.
-- Want to create a multiset consisting of a*2^i*BinaryMulOfa[i]
-- Then use ofMultiset to create a partition from the multiset
#eval digits 2 4
#check ofMultiset
#check (Multiset.count 1 P.parts)
#check Multiset
#check Multiset.toFinset

def AddaToMultiset (a : ℕ) (BinaryMultOfa : List ℕ) (M : Multiset ℕ): Multiset ℕ :=
  entries.foldl (fun acc (n, k) => addMultiplicity acc n k) ∅


#check oddtodistinct




theorem Bijection :
