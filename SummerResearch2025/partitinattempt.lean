import Mathlib
open Nat Partition
open Nat
open RingTheory
#eval Nat.bodd 2
#eval Nat.primeFactors 16

def highest_odd_factor : ℕ → ℕ
| 0       => 0
| n@(k+1) =>
  if n % 2 = 1 then n
  else highest_odd_factor (n / 2)
--maybe include the fact that the above line is still divisible


-- termination_by n => n
-- decreasing_by
--   simp_wf
--   rename_i h1 h2
--   rw[h1]
--   let a := k+1
--   have p: 2 > 1 := by
--     simp
--   have r: a≤ a :=by
--     rfl
--   exact lt_div
--     (a:=a)
--     (b:=a)
--     (c:=2)
--     (h_lt_1:= p)
--     (h_le:=r)

--Nat.dvd_iff_mod_eq_zero
-- #eval highest_odd_factor 444
-- #eval (highest_odd_factor 444).factorization 4


lemma hof_divides (n:ℕ): highest_odd_factor n ∣ n:= by
  --we know n/2 divides n,maybe look at cases
  --also posible to just define hof with 2^ power of something rather than resursion
  -- rw[Nat.dvd_iff_mod_eq_zero]
  -- simp[Nat.mod_def]
  -- by_cases odd: highest_odd_factor n % 2 = 0
  -- omega

  rw [dvd_def]

  -- by_cases hn0: n ≠ 0
  use n.factorization 2

  rw[←Nat.primeFactorsList_count_eq]

  unfold primeFactorsList

  unfold minFac
  simp


  dsimp[List.count]

  -- omega

  -- unfold highest_odd_factor
-- lemma n_div2_nonzero (n:ℕ) (hn_nonzero:n ≠ 0)
lemma hof_non_zero (n:ℕ) (hn_nonzero:n ≠ 0): highest_odd_factor n ≠ 0:=by
--if n is nonzero hof is odd
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
  contradiction
  | succ n' =>
    unfold highest_odd_factor
    by_cases c: n'.succ % 2 =1
    simp[c]
    simp[c]
    have temp: (n'.succ / 2) < n' + 1 := by omega
    have temp2: (n'.succ / 2) ≠ 0 := by omega
    exact ih (n'.succ / 2) temp temp2
lemma hof_non_zero2 (n:ℕ):n ≠ 0↔ highest_odd_factor n ≠ 0:=by
  constructor
  sorry
-- lemma contra_hof_non_zero(n:ℕ)(h:highest_odd_factor n = 0): n = 0:= by
--   exact
lemma hof_even_is_0(n:ℕ)(h: highest_odd_factor n % 2 = 0): (highest_odd_factor n = 0 ):=by
  --:highest_odd_factor n % 2 = 0 → hof = 0 → n = 0
  -- constructor
  -- swap

  -- intro h
  -- rw[h]

  -- intro h

  by_cases c: n = 0
  rw[c]
  simp[highest_odd_factor]

  by_contra

  apply hof_non_zero at c

  -- sorry


  -- rw[hof_non_zero] at c




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
          #check h.2.1.1
          #check h.2.2
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
      trace_state
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
