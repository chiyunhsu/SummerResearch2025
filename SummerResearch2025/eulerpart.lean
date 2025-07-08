import mathlib
import Mathlib.Data.Multiset.Basic

structure partition{n:ℕ} where
  parts     : Multiset ℕ
  sums      : parts.sum = n

structure OP (n : ℕ) where
  odd_parts           : Multiset ℕ
  sums                : odd_parts.sum = n
  odd                 : ∀ x ∈ odd_parts, x % 2 = 1
  dop                 : Multiset ℕ
  dop_dis             : dop.Nodup
  dis:           ∀ x∈ dop, x∈ dop →  x ∈ odd_parts
                  ∧  (∀x ∈odd_parts,x ∈ odd_parts → x∈ dop)
structure DistinctPartition (n : ℕ) where
  dis_parts       : Multiset ℕ
  sums            : dis_parts.sum = n
  dis             : dis_parts.Nodup
structure binary (n : ℕ) where
  twos            : Multiset ℕ
  unique          : twos.Nodup
  force_twos      : ∀ x ∈ twos, ∃ k : ℕ, 2 ^ k = x
  sums            : twos.sum = n
--rather than sturcture, use something resursive
-- def binary2 (binary: binary):Prop:=by
--   sorry
/-- `bits n` returns a list of Bools which correspond to the binary representation of n, where
    the head of the list represents the least significant bit -/
def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH
  --didn't find a index thingy in list but can
  --concat and length so its find to define
def binaryDecompose (x m : ℕ) : List ℕ :=
  let bits := Nat.binaryDigits m
def OddToDistinct (n : ℕ) : OP n → DistinctPartition n:= by
  intro h
  refine{
    dis_parts := h.dop.bind (fun y ↦
        (binary (h.odd_parts.count y)).twos).map fun z ↦ z * y,
        --want y -> {z1*y, z2*y,z3*y } z1=2^i1, z2=2^i2
        --3+3+3+3+3
        --3 -> {1* 3, 4 * 3}
    sums      := ?_
    dis       := ?_
  }
