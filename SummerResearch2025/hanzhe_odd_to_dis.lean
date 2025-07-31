import Mathlib
/-
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Bitindices
-/

variable (n : ℕ)
variable (P : n.Partition)
#check P.parts
#check P.parts_pos
#check P.parts_sum

open Nat Partition
open Multiset
open Finset

def binary (n : ℕ): Multiset ℕ := n.bitIndices.map fun i => 2 ^ i

-- Map from odd partitions to partitions
def FromOdd_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (odds n)): Multiset ℕ :=
   ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)
-- Maybe should have used dedup rather than toFinset

lemma FromOdd_parts_pos (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)) : i ∈ (FromOdd_parts n P hP) → i > 0 := by
  rintro hi
  unfold FromOdd_parts at hi
  apply Multiset.mem_sum.mp at hi
  rcases hi with ⟨a, ha, hi⟩
  apply Multiset.mem_map.mp at hi
  rcases hi with ⟨y, hy, hi⟩
  have a_pos : a > 0 := by
    apply P.parts_pos
    exact Multiset.mem_toFinset.mp ha
  have y_pos : y > 0 := by
    unfold binary at hy
    apply List.mem_map.mp at hy
    rcases hy with ⟨b, hb, hy⟩
    rw [← hy]
    apply Nat.pow_pos
    simp
  rw[← hi]
  exact Nat.mul_pos y_pos a_pos

lemma mul_comm_sum (s : Multiset ℕ) (a : ℕ) : (Multiset.map (fun x ↦  x * a) s).sum = s.sum * a:= by
  rw [Multiset.sum_map_mul_right]
  simp

lemma parts_sum (n : ℕ) (P : n.Partition) : ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a = n := by
  calc
  ∑ a ∈ P.parts.toFinset, (P.parts.count a) * a
    = ∑ a ∈ P.parts.toFinset, (P.parts.count a) • a
    := by simp [nsmul_eq_mul]
  _ = (Multiset.map (fun x ↦ x) P.parts).sum
    := by rw [←Finset.sum_multiset_map_count]
  _ = P.parts.sum := by simp
  _ = n := by rw [P.parts_sum]

lemma FromOdd_parts_sum (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)) : (FromOdd_parts n P hP).sum = n := by
  nth_rewrite 2 [←parts_sum n P]
  unfold FromOdd_parts
  rw [Multiset.sum_sum]
  congr
  ext
  rw [mul_comm_sum]
  unfold binary
  congr
  rw [Multiset.sum_coe]
  rw [twoPowSum_bitIndices]

def highest_odd_factor : ℕ → ℕ
| 0       => 0
| n@(k+1) =>
  if n % 2 = 1 then n
  else highest_odd_factor (n / 2)

def FromOdd (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)): n.Partition :=
{parts := FromOdd_parts n P hP,
 parts_pos := FromOdd_parts_pos n P hP,
 parts_sum := FromOdd_parts_sum n P hP}

-- Map from distinct partitions to partitions
def FromDist_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (distincts n)): Multiset ℕ :=
   ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)
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

-- Image of FromOdd is in distinct partitions
/- Recall definition of FromOdd_parts
def FromOdd_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (odds n)): Multiset ℕ :=
   ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)
-/

lemma InDist (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)) : FromOdd n P hP ∈ (distincts n) := by
  let img: Partition n := (FromOdd n P hP)
  unfold distincts
  simp
  unfold FromOdd
  simp
  unfold FromOdd_parts
  have Finsetsum_eq_Bind: ∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a) =  Multiset.bind P.parts.toFinset.val (fun a ↦
    (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)) := by
    rfl
  rw [Finsetsum_eq_Bind]
  --P.parts.toFinset.val.bind is the pullback
  apply Multiset.nodup_bind.mpr

  constructor

  · rintro a a_in_parts
    apply Multiset.Nodup.map
    -- fun y => y * a is injective

    · rintro y1 y2 heq
      dsimp at heq
      have a_nonzero : a ≠ 0 := by
        apply Nat.pos_iff_ne_zero.mp
        apply P.parts_pos
        apply Multiset.mem_toFinset.mp a_in_parts
      exact (Nat.mul_left_inj a_nonzero).mp heq

    -- binary has no duplicates
    · unfold binary
      apply Multiset.coe_nodup.mpr
      exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) (List.Sorted.nodup (bitIndices_sorted))
      /- Suggest to add
      theorem bitIndices_nodup {n : ℕ} : n.bitIndices.Nodup := List.Sorted.nodup (bitIndices_sorted)
      to Nat/BitIndices.lean
      -/
  -- pairwise disjoint

  ·

    unfold Multiset.Pairwise
    use P.parts.toFinset.val.toList
    have temp:P.parts.toFinset.val.toList.Nodup:=by
      sorry
    simp[Multiset.coe_toList]
    let f : ℕ → Multiset ℕ :=  (fun a ↦(binary (Multiset.count a P.parts)).map (fun y ↦ y * a))

    apply(List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
        (l:= P.parts.dedup.toList)
        (f:= f)
        (hn:= temp)
      ).1
    simp only [List.coe_toFinset, Multiset.mem_toList, mem_dedup]

    intro n1 hn1mem n2 hn2m2m hn1nen2

    dsimp[Function.onFun]

    dsimp[Disjoint]

    have hof_same_one_image: ∀ x ∈ f n1, highest_odd_factor x = n1:=by
      intro x hmem
      unfold f at hmem
      have hof_iva_under_mul_2(x:ℕ): highest_odd_factor x = highest_odd_factor (x * 2):=by
        -- unfold highest_odd_factor
        induction x using Nat.strongRec with
        | _ x ih =>

          -- 0-case is immediate.
          cases x with
          | zero =>

          sorry
          | succ x' =>

          unfold highest_odd_factor


          by_cases c: x'.succ % 2 = 1
          have c': ((x'.succ)*2) % 2 ≠ 1 :=by sorry
          simp[c]
          simp[c']
          conv_rhs =>
            -- congr
            simp[c']

            -- rw[←highest_odd_factor]


          --dummyline
          simp[c']






      unfold highest_odd_factor



#check Multiset.sort

-- If A is a Finset, it consists of a multiset A.val and a proposition A.nodup that A has no duplicates.


-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
-- theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := card_bij' (FromOdd n) (FromDist n) (InDist n) (InOdd n) RightInv LeftInv
