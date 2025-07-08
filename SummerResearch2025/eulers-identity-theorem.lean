import Mathlib
namespace List
-- a partition is a multiset of positive integers summing to n
def isPartition(n : ℕ) (s : Multiset ℕ) : Prop :=
  (∀ x ∈ s, 0 < x) ∧ s.sum = n

--partition into distinct parts
def isDistinctPartition (n : ℕ) (s : Multiset ℕ) : Prop :=
  isPartition n s ∧ s.Nodup


def largestOddFactor : ℕ → ℕ
  | 0     => 0
  | n@(k+1)   =>
  if n % 2 = 1 then n
  else largestOddFactor (n / 2)

#eval largestOddFactor 20

def expandPart (n : ℕ) : Multiset ℕ :=
  let o := largestOddFactor n
  if o = 0 then {n} -- 0 case shouldn't happen
  else Multiset.replicate (n / o) o

#eval expandPart 89

def expandeven (s: Multiset ℕ): Multiset ℕ :=
  s.bind (λ n => expandPart n)

#eval expandeven {1, 12 , 9}

def isOddPartition (n : ℕ) (s : Multiset ℕ) : Prop :=
  (s.sum = n) ∧ (∀ x ∈ s, x % 2 = 1)

def OddPartition (n : ℕ) : Set (Multiset ℕ) :=
  { s | isOddPartition n s }

def DistinctPartition (n : ℕ) : Set (Multiset ℕ) :=
  { s | isDistinctPartition n s }
