import Mathlib

-- P is a quantifier, Q and R are propositions
variable {α : Type*} (P : α → Prop) (Q R: Prop)

-- Forward reasoning for Modus Ponens
example (h : Q → R) (hQ : Q) : R := by
-- The `exact` tactic is used when the goal is already an hypothesis or a theoroem.
-- `h hQ` means putting `hQ : Q` into the arrow `h : Q → R`,
  exact h hQ
-- Instead of using `exact`, we can also simply write `example (h : Q → R) (hQ : Q) : R := h hQ`, removing the `by` and `exact` to mean `h hQ` is the proof of the example.

--Backward reasoning for Modus Ponens
example (h : Q → R) (hQ : Q) : R := by
-- The `apply` tactic is used to apply a hypothesis or a theorem to the current goal, making the hypotheses the new goal.
  apply h
-- The `exact` tactic is used when the goal is already an hypothesis or a theoroem.
  exact hQ

example (x : α) (h : ∀ x, P x) : P x := by
  exact h x

example (x : α) (h : P x) : ∃ x, P x := by
  use x







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
