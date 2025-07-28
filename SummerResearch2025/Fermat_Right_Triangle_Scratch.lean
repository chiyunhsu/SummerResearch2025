import Mathlib

def isPrimitivePythagoreanTriple (x y z : ℤ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ Int.gcd (Int.gcd x y) z = 1 ∧ x^2 + y^2 = z^2

def areaIsSquare (x y : ℤ) : Prop :=
  ∃ a : ℕ, x * y = 2 * a^2

def goodParam (p q : ℤ) : Prop :=
  0 < q ∧ p > q ∧ Int.gcd p q = 1 ∧ ( (p % 2 = 0 ∧ q % 2 = 1) ∨ (p % 2 = 1 ∧ q % 2 = 0) )

lemma opp_parity_odd_diff {p q : ℤ}
    (h : goodParam p q) :
    (p - q) % 2 = 1 := by
  rcases h.right.right.right with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · -- Case: p even, q odd
    have : (p - q) % 2 = (0 - 1) % 2 := by rw [←hp, ←hq]; norm_num
    exact this
  · -- Case: p odd, q even
    have : (p - q) % 2 = (1 - 0) % 2 := by rw [←hp, ←hq]; norm_num
    exact this

lemma opp_parity_odd_sum {p q : ℤ}
    (h : goodParam p q) :
    (p + q) % 2 = 1 := by
  rcases h.right.right.right with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · -- Case: p even, q odd
    have : (p + q) % 2 = (0 + 1) % 2 := by rw [←hp, ←hq]; norm_num
    exact this
  · -- Case: p odd, q even
    have : (p + q) % 2 = (1 + 0) % 2 := by rw [←hp, ←hq]; norm_num
    exact this

def genTriple (p q : ℤ) : ℤ × ℤ × ℤ :=
  let x := 2 * p * q
  let y := p^2 - q^2
  let z := p^2 + q^2
  (x, y, z)

def hasSquareArea (p q : ℤ) : Prop :=
  ∃ a : ℕ, p * q * (p^2 - q^2) = a^2

def isSquare (n : ℤ) : Prop :=
  ∃ k : ℤ, k^2 = n

def productOfCoprimeFactorsIsSquare (p q : ℤ) : Prop :=
  isSquare (p * q * (p + q) * (p - q))
-- x = 2pq, y = p^2 - q^2
-- xy/2 = 2pq(p^2-q^2)/2 = pq(p^2-q^2) = pq(p+q)(p-q)
lemma square_area_implies_product_square {p q : ℤ} (h : hasSquareArea p q) : isSquare (p * q * (p + q) * (p - q)) :=
  by
  rcases h with ⟨a, ha⟩
  use a
  rw [← ha]
  -- Goal: p * q * (p^2 - q^2) = p * q * ((p + q) * (p - q))
  -- Now manually rewrite p^2 - q^2 to (p + q) * (p - q)
  calc
    p * q * (p^2 - q^2)
        = p * q * ((p + q) * (p - q)) := by
          -- expand p^2 as p * p and q^2 as q * q, then regroup
          ring
    _ = p * q * (p + q) * (p - q) := by ring

-- Switch to IsCoprime type and back to gcd = 1
lemma coprime_mul {a b c : ℤ} (hab : Int.gcd a b = 1) (hac : Int.gcd a c = 1) : Int.gcd a (b * c) = 1 := by
  have hab' := Int.isCoprime_iff_gcd_eq_one.mpr hab
  have hac' := Int.isCoprime_iff_gcd_eq_one.mpr hac
  have habc := IsCoprime.mul_right hab' hac'
  exact Int.isCoprime_iff_gcd_eq_one.mp habc

lemma odd_coprime_two {a : ℤ} (h : a % 2 = 1) : Int.gcd a 2 = 1 := by
  let g : ℕ := Int.gcd a 2

  have div_two : g ∣ 2 := Int.gcd_dvd_natAbs_right a 2
  have g_eq : g = 1 ∨ g = 2 := (Nat.dvd_prime Nat.prime_two).1 div_two

  cases g_eq with
  | inl hg => exact hg
  | inr hg =>
    -- g = 2 ⇒ ↑g = 2 ⇒ ↑g ∣ a ⇒ 2 ∣ a
    have gcd_dvd : ↑g ∣ a := Int.gcd_dvd_left a 2
    rw [hg] at gcd_dvd  -- now gcd_dvd : 2 ∣ a
    have : a % 2 = 0 := by
      apply Dvd.dvd.modEq_zero_int
      exact gcd_dvd
    rw [this] at h
    contradiction

-- pick a prime, if a power of it divides u * v, the power must be even
-- find a way to search and run through all the primes that divide?

-- look at:
-- https://github.com/leanprover-community/mathlib4/blob/d19cd93f3db24ca3a2ab957c266dd7e1ce2110fa/Mathlib/RingTheory/Int/Basic.lean#L47-L57

theorem coe_gcd (i j : ℤ) : ↑(Int.gcd i j) = GCDMonoid.gcd i j :=
  rfl

theorem sq_of_gcd_eq_one {a b c : ℤ} (h : Int.gcd a b = 1) (heq : a * b = c ^ 2) :
    ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2 := by
  have h' : IsUnit (GCDMonoid.gcd a b) := by
    rw [← coe_gcd, h, Int.ofNat_one]
    exact isUnit_one
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h' heq
  use d
  rw [← hu]
  rcases Int.units_eq_one_or u with hu' | hu' <;>
    · rw [hu']
      simp

lemma coprime_square_product {a b : ℤ}
    (hcoprime : Int.gcd a b = 1)
    (hsquare : isSquare (a * b))
    (hpos : a > 0 ∧ b > 0) :
    isSquare a ∧ isSquare b := by

  obtain ⟨c, hc⟩ := hsquare

  have ha := sq_of_gcd_eq_one hcoprime hc.symm
  have hb := sq_of_gcd_eq_one (Int.gcd_comm b a ▸ hcoprime) (by rw [mul_comm, hc])

  obtain ⟨a0, ha0 | ha0⟩ := ha
  obtain ⟨b0, hb0 | hb0⟩ := hb

  -- Case 1: a = a0^2, b = b0^2
  · constructor
    · use a0.natAbs
      rw [ha0]
      rw [← Int.natAbs_of_nonneg (sq_nonneg a0)]
      rw [Int.natAbs_pow]
      norm_cast

    · use b0.natAbs
      rw [hb0]
      rw [← Int.natAbs_of_nonneg (sq_nonneg b0)]
      rw [Int.natAbs_pow]
      norm_cast

  -- Case 2: a = a0^2, b = -b0^2
  · exfalso
    have b_pos := hpos.right
    rw [hb0] at b_pos
    -- Split cases on sign of b0:
    cases Int.le_total 0 b0 with
    | inl hpos_b0 =>
      have square_nonneg : 0 ≤ b0 * b0 := Int.mul_nonneg hpos_b0 hpos_b0
      linarith
    | inr hneg_b0 =>
      have square_nonneg : 0 ≤ (-b0) * (-b0) := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hneg_b0) (Int.neg_nonneg_of_nonpos hneg_b0)
      -- b0^2 = (-b0)^2
      rw [← Int.mul_neg_one] at square_nonneg
      linarith

  -- Case 3: a = -a0^2
  · exfalso
    have a_pos := hpos.left
    rw [ha0] at a_pos
    -- Split cases on sign of a0:
    cases Int.le_total 0 a0 with
    | inl hpos_a0 =>
      have square_nonneg : 0 ≤ a0 * a0 := Int.mul_nonneg hpos_a0 hpos_a0
      linarith
    | inr hneg_a0 =>
      have square_nonneg : 0 ≤ (-a0) * (-a0) := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hneg_a0) (Int.neg_nonneg_of_nonpos hneg_a0)
      -- a0^2 = (-a0)^2
      rw [← Int.mul_neg_one] at square_nonneg
      linarith


lemma coprime_linear_factors {p q : ℤ} (hgood : goodParam p q) (hsq : isSquare (p * q * (p + q) * (p - q))) :
  isSquare p ∧ isSquare q ∧ isSquare (p + q) ∧ isSquare (p - q) := by
  -- Convert from type IsCoprime p q to gcd p q = 1
  have hcoprime_pq := hgood.right.right.left

  -- If gcd(a, b) = 1 and a, b, a + b, a - b all are pairwise coprime,
  -- then any square divisible by their product implies each is a square

  -- Prove all gcds are 1
  have hcoprime_p_sum : Int.gcd p (p + q) = 1 := by
    rw [add_comm, Int.gcd_add_self_right]
    exact hcoprime_pq

  have hcoprime_q_sum : Int.gcd q (p + q) = 1 := by
    rw [Int.gcd_comm, Int.gcd_add_self_left]
    exact hcoprime_pq

  have hcoprime_p_diff : Int.gcd p (p - q) = 1 := by
    rw [Int.gcd_comm, Int.gcd_self_sub_left, Int.gcd_comm]
    exact hcoprime_pq

  have hcoprime_q_diff : Int.gcd q (p - q) = 1 := by
    rw [Int.gcd_sub_self_right, Int.gcd_comm]
    exact hcoprime_pq

  have h_coprime_diff_sum : Int.gcd (p - q) (p + q) = 1 := by
    rw [← Int.gcd_add_self_right (p - q) (p + q), add_assoc p q (p-q), add_sub_cancel, ← two_mul p]
    -- becomes gcd(p - q, 2 * p)
    have h_parity : (p - q) % 2 = 1 := opp_parity_odd_diff hgood
    have hcoprime_2 : Int.gcd (p - q) 2 = 1 := by
      rw[odd_coprime_two]
      exact h_parity
    have hcoprime_p : Int.gcd (p - q) p = 1 := by
      rw [Int.gcd_comm]
      exact hcoprime_p_diff
    exact coprime_mul hcoprime_2 hcoprime_p

  -- Now apply coprime_square_product to the product split by taking the right-most part out

  /-
  coprime_square_product needs:
  hcoprime a b
  hsquare a * b
  hpos a > 0 ∧ b > 0
  -/

  let rest1 := p * q * (p + q)

  have hcoprime1 : Int.gcd (p - q) rest1 = 1 := by
    apply coprime_mul
    · apply coprime_mul
      · -- gcd(p - q, p)
        rw [Int.gcd_comm]
        exact hcoprime_p_diff
      · -- gcd(p - q, q)
        rw [Int.gcd_comm]
        exact hcoprime_q_diff
    · -- gcd(p - q, p + q)
      exact h_coprime_diff_sum

  -- hgood.1 : q > 0
  -- hgood.2.1 : p > q

  have pos_q : q > 0 := by
    apply hgood.1

  have pos_p : p > 0 :=
    lt_trans pos_q hgood.2.1

  have pos_rest1 : rest1 > 0 :=
    mul_pos (mul_pos pos_p pos_q) (add_pos pos_p pos_q)

  have pos_diff : p - q > 0 :=
    sub_pos_of_lt hgood.2.1

  have htotal_square : isSquare ((p - q) * rest1) := by
    rw [mul_comm]
    exact hsq

  have ⟨hsq_diff, hsq_rest1⟩ := coprime_square_product hcoprime1 htotal_square ⟨pos_diff, pos_rest1⟩

  let rest2 := p * q

  have hcoprime2 : Int.gcd (p + q) rest2 = 1 := by
    apply coprime_mul
    rw [Int.gcd_comm]
    exact hcoprime_p_sum
    rw [Int.gcd_comm]
    exact hcoprime_q_sum

  have pos_rest2 : rest2 > 0 :=
    mul_pos pos_p pos_q

  have pos_sum : p + q > 0 :=
    add_pos pos_p pos_q

  have htotal_square1 : isSquare ((p + q) * rest2) := by
    rw [mul_comm]
    exact hsq_rest1

  have ⟨hsq_sum, hsq_rest2⟩ := coprime_square_product hcoprime2 htotal_square1 ⟨pos_sum, pos_rest2⟩

  have hpq_square : isSquare (p * q) := by
    exact hsq_rest2

  have ⟨hsq_p, hsq_q⟩ := coprime_square_product hcoprime_pq hpq_square ⟨pos_p, pos_q⟩

  exact ⟨hsq_p, hsq_q, hsq_sum, hsq_diff⟩

lemma goodParam_squares {p q : ℤ} (hgood : goodParam p q)
    (hsq : isSquare (p * q * (p + q) * (p - q))) :
    ∃ r s : ℤ, r^2 = p + q ∧ s^2 = p - q := by
  obtain ⟨hsq_p, hsq_q, hsq_sum, hsq_diff⟩ :=
    coprime_linear_factors hgood hsq

  obtain ⟨r, hr⟩ := hsq_sum
  obtain ⟨s, hs⟩ := hsq_diff

  exact ⟨r, s, hr, hs⟩

lemma odd_rs {p q r s : ℤ}
    (hgood : goodParam p q)
    (hr : r^2 = p + q)
    (hs : s^2 = p - q) :
    r % 2 = 1 ∧ s % 2 = 1 := by

  have h_sum_mod : r ^ 2 % 2 = 1 := by
    rw [hr]
    exact opp_parity_odd_sum hgood

  have h_diff_mod : s ^ 2 % 2 = 1 := by
    rw [hs]
    exact opp_parity_odd_diff hgood

  -- split r % 2 into 0 or 1
  have r_mod_cases := Int.emod_two_eq_zero_or_one r
  have s_mod_cases := Int.emod_two_eq_zero_or_one s

  rcases r_mod_cases with (r_even | r_odd)
  · -- Case r % 2 = 0
    -- Then r = 2k ⇒ r² = 4k² ≡ 0 mod 2
    have h_even_contra : r ^ 2 % 2 = 0 := by
      obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp r_even
      rw [hk, sq]
      simp [mul_assoc]

    rw [h_even_contra] at h_sum_mod
    norm_num at h_sum_mod

  rcases s_mod_cases with (s_even | s_odd)
  · -- Case s % 2 = 0
    -- Then s = 2k ⇒ s² = 4k² ≡ 0 mod 2
    have h_even_contra : s ^ 2 % 2 = 0 := by
      obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp s_even
      rw [hk, sq]
      simp [mul_assoc]

    rw [h_even_contra] at h_diff_mod
    norm_num at h_diff_mod

  -- only remaining case
  exact ⟨r_odd, s_odd⟩

-- r + s is even
-- r - s is even
-- one of r + s and r - s is divisible by 4
lemma even_mod_four {r s : ℤ}
    (hr : r % 2 = 1)
    (hs : s % 2 = 1) :
    (r + s) % 2 = 0 ∧ (r - s) % 2 = 0 ∧ ((r + s) % 4 = 0 ∨ (r - s) % 4 = 0) := by
  constructor
  · -- (r + s) % 2 = 0
    have : (r + s) % 2 = (1 + 1) % 2 := by rw [←hr, ←hs]; norm_num
    exact this
  constructor
  · -- (r - s) % 2 = 0
    have : (r - s) % 2 = (1 - 1) % 2 := by rw [←hr, ←hs]; norm_num
    exact this
  sorry
