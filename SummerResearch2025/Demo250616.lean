import Mathlib

-- P is a predicate, Q, R and S are propositions
variable {α : Type*} (P : α → Prop) (Q R S: Prop)

-- Forward reasoning
--Modus Ponens
example (h : Q → R) (hQ : Q) : R := by
-- The `exact` tactic is used when the goal is already an hypothesis or a theoroem.
-- `h hQ` means putting `hQ : Q` into the arrow `h : Q → R`,
  exact h hQ
-- Instead of using `exact`, we can also simply write `example (h : Q → R) (hQ : Q) : R := h hQ`, removing the `by` and `exact` to mean `h hQ` is the proof of the example.

-- Backward reasoning
-- Modus Ponens
example (h : Q → R) (hQ : Q) : R := by
-- The `apply` tactic is used to apply a hypothesis or a theorem to the current goal, making the hypotheses the new goal.
  apply h
-- The `exact` tactic is used when the goal is already an hypothesis or a theoroem.
  exact hQ

-- Forward reasoning
-- `have` is used to introduce an intermeidate step
example (h1 : Q → R) (h2 : R → S)(hQ : Q) : S := by
  have hR : R := by
    apply h1
    exact hQ
  apply h2
  exact hR

-- Backward reasoning
example (h1 : Q → R) (h2 : R → S)(hQ : Q) : S := by
  apply h2
  apply h1
  exact hQ

-- Universal Quantifier : using universal statements
example (x : α) (h : ∀ y, P y) : P x := by
  exact h x
  --apply h

-- Existential Quantifier : proving existential statments -- Use the tactic `use`
example (x : α) (h : P x) : ∃ y, P y := by
  use x

-- Exercise
example (x : α) (h : ∀ y, P y → Q) (hx : P x) : Q := by
  sorry

-- Proving implication
-- Use the tactic `intro` to introduce the hypothesis
example (h1 : Q → R) (h2 : R → S) : Q → S := by
  intro h
  apply h2
  apply h1
  exact h

-- Universal Quantifier : proving universal statements.
-- Use the tactic `intro` to introduce a variable
example (h : ∀ y, Q → P y) (hQ : Q): ∀ y, P y := by
  intro y
  apply h y
  exact hQ

-- Existential Quantifier : using existential statments
-- Use the tactic `rcases` to destruct the existential quantifier
example (h : ∃ y, P y) (h' : ∀ y, P y → Q) : Q := by
  rcases h with ⟨y, hy⟩
  exact h' y hy
