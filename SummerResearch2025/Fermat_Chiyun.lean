import Mathlib

variable (p q : ℕ+)

#check Nat.sq_sub_sq p q

structure PrimPyTriple where
  x : ℕ+
  y : ℕ+
  z : ℕ+
  coprime : Int.gcd (Int.gcd x y) z = 1
  Py : x^2 + y^2 = z^2

structure GoodParam where
  p : ℕ+
  q : ℕ+
  big : p > q
  coprime : Int.gcd p q = 1
  parity : (p.val % 2 = 0 ∧ q.val % 2 = 1) ∨ (p.val % 2 = 1 ∧ q.val % 2 = 0)
