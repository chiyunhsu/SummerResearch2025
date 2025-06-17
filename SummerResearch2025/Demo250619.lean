import Mathlib

variable {α : Type*} (P : α → Prop) (Q R S: Prop)


-- `¬`: negation
-- When there are two contradictory hypotheses, such as `Q` and `¬ Q`, the tactic `contradiction` is used to resolve the goal.
example (h: ¬ Q) : Q → R := by
  intro hQ
  contradiction

-- Use `intro h` to introduce the hypothesis `h: P`. Then the goal becomes `False`.
example (h : Q → R) (hnR : ¬ R) : ¬ Q := by
  intro hQ
  have hR : R := h hQ
  contradiction


-- `∧`: and, conjunction
-- Use `constructor` to split the goal into two subgoals: `Q` and `R`.
example (hQ : Q) (hR: R) : Q ∧ R := by -- ⟨hQ, hR⟩
  constructor
  exact hQ
  exact hR

-- Use `h.1` and `h.2` to refer to the left and right conjuncts of the conjunction.
example (h : Q ∧ R) : Q := by
  exact h.1
--exact h.left

-- `∨`: (inclusive) or, disjunction
--  Use `left` or `right` to choose which disjunct to prove. Then the goal becomes `Q` or `R`.
example (hQ : Q) : Q ∨ R := by
  left
  exact hQ

-- Use `rcases h with h1 | h2` to destruct the disjunction. Then you can use `h1 : Q` or `h2 : R` to refer to the left or right disjunct.
example (h : Q ∨ R) (hQ : ¬ R) : Q := by
  rcases h with h1 | h2
  · exact h1
  · contradiction


--De Morgan's laws:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x
  intro h'
  apply h
  use x
--push_neg at h
--exact h

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro h'
  rcases h' with ⟨x, hx⟩
  apply h x
  exact hx
--push_neg
--exact h

-- `by_contra` is a tactic that allows you to prove a goal by contradiction.
-- It assumes the negation of the goal and tries to derive a contradiction.
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x
--push_neg at h
--exact h

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, hx⟩
  apply hx
  exact h' x
--push_neg
--exact h
