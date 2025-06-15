/-
You can write comments of multiple lines by starting with `/-` and ending with `-/`.
-/

-- You can write single line comments by starting with `--`.
-- Import Mathlib to use the Lean math library.
import Mathlib

-- The `example` keyword is used to create a goal that we want to prove.
--  `a b c : ℝ` declares three variables `a`, `b`, and `c` of type `ℝ` (the real numbers). Enter ℝ by `slash R space`
-- The goal is to prove that `a * b * c = b * (a * c)`. When there is no parenthesis, Lean assumes the default order of operations, so `a * b * c` is interpreted as `(a * b) * c`.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
-- The rewrite tactic `rw [h]` is used to rewrite the goal using an equality `h : x = y` by replacing x by y.
-- To replace y by x, use `rw [← h]`.
-- `mul_comm` is a lemma that states that multiplication is commutative, i.e., `∀ a b, a * b = b * a`.
-- `mul_comm a b` further specifies the variables `a` and `b`, and becomes the statement `a * b = b * a`.
  rw [← mul_comm b a]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
-- The `sorry` tactic is used to indicate that the proof is incomplete or that you are not sure how to proceed. It can be used as a placeholder.
-- sorry
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]
