import Mathlib

-- Lagrange's Theorem
example {G : Type*} [Group G] (H : Subgroup G) : H.index * Nat.card H = Nat.card G := H.index_mul_card

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/GroupTheory/Index.lean
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/GroupTheory/Coset/Basic.lean


variable {G G' : Type*} [Group G] [Group G'] (H K L : Subgroup G)

variable [Group α] {s t: Subgroup α}

noncomputable def index : ℕ :=
  Nat.card (G ⧸ H)

noncomputable def relindex : ℕ :=
  (H.subgroupOf K).index

noncomputable def quotientEquivProdOfLE (h_le : s ≤ t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t := by
  sorry

theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Cardinal.toNat_congr QuotientGroup.quotientBot.toEquiv

theorem relindex_bot_left : (⊥ : Subgroup G).relindex H = Nat.card H := by
  sorry

-- Lagrange's Theorem
theorem relindex_mul_index (h : H ≤ K) : H.relindex K * K.index = H.index :=
  ((mul_comm _ _).trans (Cardinal.toNat_mul _ _).symm).trans
    (congr_arg Cardinal.toNat (Equiv.cardinal_eq (quotientEquivProdOfLE h))).symm


theorem card_mul_index : Nat.card H * H.index = Nat.card G := by
  rw [← relindex_bot_left, ← index_bot]
  exact relindex_mul_index bot_le

theorem index_mul_card : H.index * Nat.card H = Nat.card G := by
  rw [mul_comm, card_mul_index]
