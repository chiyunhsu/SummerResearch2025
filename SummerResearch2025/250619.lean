import Mathlib

-- Lagrange's Theorem
example {G : Type*} [Group G] (H : Subgroup G) : H.index * Nat.card H = Nat.card G := by --H.index_mul_card
  sorry

-- Hanzhe's reference on the proof of Lagrange's Theorem: https://www.stolaf.edu/people/humke/COURSES/AASyllabus/LaGrange.pdf
-- Where `H.index` is defined in Mathlib: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/GroupTheory/Index.lean
