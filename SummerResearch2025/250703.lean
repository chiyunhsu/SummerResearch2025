import Mathlib

-- a partition is a multiset of positive integers summing to n
def isPartition(n : ℕ) (s : Multiset ℕ) : Prop :=
 (∀ x ∈ s, 0 < x) ∧ s.sum = n

-- partition into distinct parts
def isDistinctPartition (n : ℕ) (s : Multiset ℕ) : Prop :=
 isPartition n s ∧ s.Nodup


--partition into odd parts
def isOddPartition(n : ℕ) (s : Multiset ℕ) : Prop :=
 isPartition

def OddPartition (n : ℕ) : Set (Multiset ℕ) :=
  { s | isOddPartition n s }

def DistinctPartition (n : ℕ) : Set (Multiset ℕ) :=
  { s | isDistinctPartition n s }

def OddToDistinct (n : ℕ) : OddPartition n → DistinctPartition n :=
