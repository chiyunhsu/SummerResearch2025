/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic.ApplyFun

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : Partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## TODO

Link this to Young diagrams.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/

assert_not_exists Field

open Multiset
-- open RingTheory.UniqueFactorizationDomain
namespace Nat

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext]
structure Partition (n : ℕ) where
  /-- positive integers summing to `n` -/
  parts : Multiset ℕ
  /-- proof that the `parts` are positive -/
  parts_pos : ∀ {i}, i ∈ parts → 0 < i
  /-- proof that the `parts` sum to `n` -/
  parts_sum : parts.sum = n
deriving DecidableEq

namespace Partition

@[deprecated "Partition now derives an instance of DecidableEq." (since := "2024-12-28")]
instance decidableEqPartition {n : ℕ} : DecidableEq (Partition n) :=
  fun _ _ => decidable_of_iff' _ Partition.ext_iff

/-- A composition induces a partition (just convert the list to a multiset). -/
@[simps]
def ofComposition (n : ℕ) (c : Composition n) : Partition n where
  parts := c.blocks
  parts_pos hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.sum_coe, c.blocks_sum]

theorem ofComposition_surj {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext rfl⟩

-- The argument `n` is kept explicit here since it is useful in tactic mode proofs to generate the
-- proof obligation `l.sum = n`.
/-- Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
@[simps]
def ofSums (n : ℕ) (l : Multiset ℕ) (hl : l.sum = n) : Partition n where
  parts := l.filter (· ≠ 0)
  parts_pos hi := (of_mem_filter hi).bot_lt
  parts_sum := by
    have lz : (l.filter (· = 0)).sum = 0 := by simp [sum_eq_zero_iff]
    rwa [← filter_add_not (· = 0) l, sum_add, lz, zero_add] at hl

/-- A `Multiset ℕ` induces a partition on its sum. -/
@[simps!]
def ofMultiset (l : Multiset ℕ) : Partition l.sum := ofSums _ l rfl

/-- An element `s` of `Sym σ n` induces a partition given by its multiplicities. -/
def ofSym {n : ℕ} {σ : Type*} (s : Sym σ n) [DecidableEq σ] : n.Partition where
  parts := s.1.dedup.map s.1.count
  parts_pos := by simp [Multiset.count_pos]
  parts_sum := by
    change ∑ a ∈ s.1.toFinset, count a s.1 = n
    rw [toFinset_sum_count_eq]
    exact s.2

variable {n : ℕ} {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]

@[simp] lemma ofSym_map (e : σ ≃ τ) (s : Sym σ n) :
    ofSym (s.map e) = ofSym s := by
  simp only [ofSym, Sym.val_eq_coe, Sym.coe_map, mk.injEq]
  rw [Multiset.dedup_map_of_injective e.injective]
  simp only [map_map, Function.comp_apply]
  congr; funext i
  rw [← Multiset.count_map_eq_count' e _ e.injective]

/-- An equivalence between `σ` and `τ` induces an equivalence between the subtypes of `Sym σ n` and
`Sym τ n` corresponding to a given partition. -/
def ofSymShapeEquiv (μ : Partition n) (e : σ ≃ τ) :
    {x : Sym σ n // ofSym x = μ} ≃ {x : Sym τ n // ofSym x = μ} where
  toFun := fun x => ⟨Sym.equivCongr e x, by simp [ofSym_map, x.2]⟩
  invFun := fun x => ⟨Sym.equivCongr e.symm x, by simp [ofSym_map, x.2]⟩
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The partition of exactly one part. -/
def indiscrete (n : ℕ) : Partition n := ofSums n {n} rfl

instance {n : ℕ} : Inhabited (Partition n) := ⟨indiscrete n⟩

@[simp] lemma indiscrete_parts {n : ℕ} (hn : n ≠ 0) : (indiscrete n).parts = {n} := by
  simp [indiscrete, filter_eq_self, hn]

@[simp] lemma partition_zero_parts (p : Partition 0) : p.parts = 0 :=
  eq_zero_of_forall_notMem fun _ h => (p.parts_pos h).ne' <| sum_eq_zero_iff.1 p.parts_sum _ h

instance UniquePartitionZero : Unique (Partition 0) where
  uniq _ := Partition.ext <| by simp

@[simp] lemma partition_one_parts (p : Partition 1) : p.parts = {1} := by
  have h : p.parts = replicate (card p.parts) 1 := eq_replicate_card.2 fun x hx =>
    ((le_sum_of_mem hx).trans_eq p.parts_sum).antisymm (p.parts_pos hx)
  have h' : card p.parts = 1 := by simpa using (congrArg sum h.symm).trans p.parts_sum
  rw [h, h', replicate_one]

instance UniquePartitionOne : Unique (Partition 1) where
  uniq _ := Partition.ext <| by simp

@[simp] lemma ofSym_one (s : Sym σ 1) : ofSym s = indiscrete 1 := by
  ext; simp

/-- The number of times a positive integer `i` appears in the partition `ofSums n l hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `Partition.non_zero` combined with `Multiset.count_eq_zero_of_notMem` gives that
this is `0` instead.)
-/
theorem count_ofSums_of_ne_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi

theorem count_ofSums_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) :
    (ofSums n l hl).parts.count 0 = 0 :=
  count_filter_of_neg fun h => h rfl

/-- Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
instance (n : ℕ) : Fintype (Partition n) :=
  Fintype.ofSurjective (ofComposition n) ofComposition_surj

/-- The finset of those partitions in which every part is odd. -/
def odds (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => ∀ i ∈ c.parts, ¬Even i

/-- The finset of those partitions in which each part is used at most once. -/
def distincts (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => c.parts.Nodup

/-- The finset of those partitions in which every part is odd and used at most once. -/
def oddDistincts (n : ℕ) : Finset (Partition n) :=
  odds n ∩ distincts n


def highest_odd_factor : ℕ → ℕ
| 0       => 0
| n@(k+1) =>
  if n % 2 = 1 then n
  else highest_odd_factor (n / 2)

lemma n_non0_hof_non0 (n:ℕ) (hn_nonzero:n ≠ 0): highest_odd_factor n ≠ 0:=by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
  contradiction
  | succ n =>
    unfold highest_odd_factor
    by_cases c: n.succ % 2 =1
    simp[c]

    simp[c]

    have temp: (n.succ / 2) < n + 1 := by omega
    have temp2: (n.succ / 2) ≠ 0 := by omega
    exact ih (n.succ / 2) temp temp2

lemma hof_zero_iff_n_zero :n = 0 ↔ highest_odd_factor n = 0:=by
  constructor
  intro h
  rw[h]
  simp[highest_odd_factor]
  contrapose
  exact n_non0_hof_non0 (n:= n)

lemma n_non0_hof_odd (hn_nonzero:n ≠ 0): highest_odd_factor n % 2 = 1 :=by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
  contradiction
  | succ n' =>
    unfold highest_odd_factor
    by_cases c: n'.succ % 2 =1
    simp[c]
    simp[c]
    have temp: (n'.succ / 2) < (n' + 1) := by omega
    have temp2: (n'.succ / 2) ≠ 0 := by omega
    apply ih (n'.succ / 2) temp temp2

lemma hof_non0_n_odd: n%2 =1 → highest_odd_factor n ≠ 0:=by
  intro h
  rw[Nat.mod_def] at h
  have temp: n = 1 + 2 *(n/2) :=by omega
  have temp2 : 1 + 2 *(n/2) ≠ 0 :=by omega
  rw[temp]
  apply hof_zero_iff_n_zero.not.1
  exact temp2
lemma hof_even_is_0(n:ℕ)(h: highest_odd_factor n % 2 = 0): (highest_odd_factor n = 0 ):=by
  by_cases c: n = 0
  rw[c]
  simp[highest_odd_factor]
  apply hof_zero_iff_n_zero.not.1 at c
  false_or_by_contra
  have temp: n ≠ 0 := by
    exact hof_zero_iff_n_zero.not.2 c
  have temp2: highest_odd_factor n % 2 = 1:= by
    exact n_non0_hof_odd (hn_nonzero:=temp)
  rw[h] at temp2
  contradiction
lemma n_sub_n_zero(n:ℕ) : n - n = 0 :=by omega
lemma hof_divides (n:ℕ): highest_odd_factor n ∣ n:= by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
  simp[highest_odd_factor]
  | succ n' =>
  simp[ highest_odd_factor]
  by_cases case1: (n'.succ) % 2 = 1
  simp[case1]
  simp[case1]
  have temp: (n'.succ / 2) < n' + 1 := by omega
  have temp2: highest_odd_factor ((n'.succ) / 2) ∣( (n'.succ)/2):=by
    apply ih (n'.succ / 2) temp
  have case2 : 2 ∣ n'.succ:= by
    simp[Bool.not_eq] at case1
    exact Nat.dvd_of_mod_eq_zero (H:= case1)
  have temp3: (n'.succ / 2) ∣ n'.succ :=by
    exact Nat.div_dvd_of_dvd (h := case2)
  exact Nat.dvd_trans (h₁:=temp2) (h₂:=temp3)

def dto(n:ℕ): distincts n → odds n:=by
  intro distinct
  rcases distinct with ⟨p,p_distinct⟩
  let odd := (p.parts).bind fun y ↦
  Multiset.ofList (List.replicate
          (y/(highest_odd_factor y)) (highest_odd_factor y))
  refine{
    val:=by
      refine{
        parts:=by
          exact odd
        parts_pos:=by
          intro all pos
          unfold odd at pos
          simp at pos
          rcases pos with ⟨w,h⟩
          apply Nat.pos_iff_ne_zero.2
          rw[h.2.2]
          exact h.2.1.1
        parts_sum:=by
          unfold odd
          simp
          have temp2: ∀ x ∈ p.parts, x / highest_odd_factor x * highest_odd_factor x = x:=by
            intro x hx
            have temp := by
              exact hof_divides x
            exact Nat.div_mul_cancel temp
          have map_simp : p.parts.map (fun x => x / highest_odd_factor x * highest_odd_factor x) = p.parts.map (fun x => x) := by
            apply Multiset.map_congr
            rfl
            exact temp2
          rw[map_simp]
          simp
          exact p.parts_sum
      }
    property := by
      unfold odds
      simp
      unfold odd
      simp?
      intro n1 n2 hmem hn2non0 hn2rfl hn2eqn1
      rw[hn2eqn1]
      unfold Odd
      by_cases case1: (highest_odd_factor n2) % 2 = 0
      apply hof_even_is_0 at case1
      contradiction
      simp at case1
      simp[Nat.mod_def] at case1
      have : highest_odd_factor n2 = 2 * (highest_odd_factor n2 / 2) + 1 := by omega
      use highest_odd_factor n2 / 2
  }
end Partition

end Nat

open Nat Partition

variable {n : ℕ} {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
