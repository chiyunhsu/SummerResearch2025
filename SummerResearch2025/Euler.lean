import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Finset.Card
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

-- α, β are both the type n.Partition
-- s is the set of odd partitions of n
-- t is the set of distinct partitions of n

def oddtodistinct : ∀ P ∈ (odds n), n.Partition :=
  fun P hP =>


#check ofMultiset
#check (Multiset.count 1 P.parts)
#check Multiset


#check oddtodistinct




theorem Bijection :
