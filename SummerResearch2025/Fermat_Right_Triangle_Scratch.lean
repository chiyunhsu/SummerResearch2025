import Mathlib

def isPrimitivePythagoreanTriple (x y z : ℤ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ Int.gcd (Int.gcd x y) z = 1 ∧ x^2 + y^2 = z^2

def areaIsSquare (x y : ℤ) : Prop :=
  ∃ a : ℕ, x * y = 2 * a^2

def goodParam (p q : ℤ) : Prop :=
  0 < q ∧ q < p ∧ Int.gcd p q = 1 ∧ ( (p % 2 = 0 ∧ q % 2 = 1) ∨ (p % 2 = 1 ∧ q % 2 = 0) )

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

def genTriple (p q : ℤ) : ℤ × ℤ × ℤ :=
  let x := 2 * p * q
  let y := p^2 - q^2
  let z := p^2 + q^2
  (x, y, z)

def hasSquareArea (p q : ℤ) : Prop :=
  ∃ a : ℕ, p * q * (p^2 - q^2) = a^2

def isSquare (n : ℤ) : Prop :=
  ∃ k : ℕ, k^2 = n

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

-- lemma: if a*b is square with a, b coprime, then a and b are squares
-- square: exponent of each prime is even in factorization
-- coprime: if nonzero exponent of prime in one number, other number's prime must have zero exponent
-- factorization was very difficult, was not able to make progress
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

  -- Case 3: a = -a0^2, b = b0^2
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

  -- Now apply coprime_square_product to the product split as (p * q) * ((p + q) * (p - q))

  sorry
