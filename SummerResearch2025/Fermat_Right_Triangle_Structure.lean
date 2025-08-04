import Mathlib

variable (p q : ℕ)

#check Nat.sq_sub_sq p q

def isSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, k ^ 2 = n

structure GoodParam where
  p : ℕ
  q : ℕ
  big : p > q
  coprime : Nat.gcd p q = 1
  parity : (Even p ∧ Odd q) ∨ (Odd p ∧ Even q)

-- x, y, z, coprime, py (latter two lemmas)
structure PyTriple where
  -- gp : GoodParam
  x : ℕ
  y : ℕ
  z : ℕ
  coprime : Nat.gcd x y = 1 ∧ Nat.gcd x z = 1 ∧ Nat.gcd y z = 1
  py : x^2 + y^2 = z^2

-- then function from gp to pt

-- 2pq and p^2 - q^2
-- d | 2, p, q

lemma odd_coprime_two {a : ℕ} (h : Odd a) : Nat.gcd a 2 = 1 := by
  let g : ℕ := Int.gcd a 2

  have div_two : g ∣ 2 := Int.gcd_dvd_natAbs_right a 2
  have g_eq : g = 1 ∨ g = 2 := (Nat.dvd_prime Nat.prime_two).1 div_two

  cases g_eq with
  | inl hg => exact hg
  | inr hg =>
    -- g = 2 ⇒ ↑g = 2 ⇒ ↑g ∣ a ⇒ 2 ∣ a
    have gcd_dvd : ↑g ∣ a := Nat.gcd_dvd_left a 2
    rw [hg] at gcd_dvd  -- now gcd_dvd : 2 ∣ a
    rw [← even_iff_two_dvd] at gcd_dvd
    rw [Nat.odd_iff_not_even] at gcd_dvd
    contradiction

lemma ParamCoprime (gp : GoodParam) (x y z : ℕ)
    (hx : x = 2 * gp.p * gp.q)
    (hy : y = gp.p ^ 2 - gp.q ^ 2)
    (hz : z = gp.p ^ 2 + gp.q ^ 2) :
    Nat.gcd x y = 1 ∧ Nat.gcd x z = 1 ∧ Nat.gcd y z = 1 := by

  -- Extract p and q
  let p := gp.p
  let q := gp.q

  rw [hx, hy, hz]
  rw [Nat.sq_sub_sq]

  have hcop : Nat.gcd p q = 1 := gp.coprime
  have hparity := gp.parity

  have gcd_xy : Nat.gcd (2 * p * q) (p ^ 2 - q ^ 2) = 1 := by
    sorry

  have gcd_xz : Nat.gcd (2 * p * q) (p ^ 2 + q ^ 2) = 1 := by
    sorry

  have gcd_yz : Nat.gcd (p ^ 2 - q ^ 2) (p ^ 2 + q ^ 2) = 1 := by
    sorry

  sorry
  -- Apply the assumptions to finish
  exact ⟨gcd_xy, gcd_xz, gcd_yz⟩


/-
lemma ParamCoprime (gp : GoodParam) (x y z : ℕ)
    (hx : x = 2 * gp.p * gp.q)
    (hy : y = gp.p ^ 2 - gp.q ^ 2)
    (hz : z = gp.p ^ 2 + gp.q ^ 2) :
    Nat.gcd (Nat.gcd x y) z = 1 := by
  -- Assume for contradiction that there is a prime dividing all three

  -- let d be a common divisor
  let d := Nat.gcd (Nat.gcd x y) z
  by_contra hcontra

  have hd_z : d ∣ z := Nat.gcd_dvd_right (Nat.gcd x y) z
  -- exists prime p
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hcontra
  have hp_z : p ∣ z := Nat.dvd_trans hp_dvd hd_z
-/

lemma ParamPy (gp : GoodParam) (x y z : ℕ)
    (hx : x = 2 * gp.p * gp.q) (hy : y = gp.p ^ 2 - gp.q ^ 2) (hz : z = gp.p ^ 2 + gp.q ^ 2) :
    x^2 + y^2 = z^2 :=
  sorry

def ParamToTriple (gp : GoodParam) : PyTriple :=
{
  x := 2 * gp.p * gp.q,
  y := gp.p ^ 2 - gp.q ^ 2,
  z := gp.p ^ 2 + gp.q ^ 2,
  coprime := sorry -- lemma to prove
  py := sorry -- lemma to prove
}

lemma opp_parity_odd_sum (gp : GoodParam) :
    Odd (gp.p + gp.q) := by
  rcases gp.parity with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · -- Case: p even, q odd
    rw [add_comm]
    apply Odd.add_even hq hp
  · -- Case: p odd, q even
    apply Odd.add_even hp hq

lemma opp_parity_odd_diff (gp : GoodParam) :
    Odd (gp.p - gp.q) := by
  rcases gp.parity with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · -- Case: p even, q odd
    apply Nat.Even.sub_odd (le_of_lt gp.big) hp hq
  · -- Case: p odd, q even
    apply Nat.Odd.sub_even (le_of_lt gp.big) hp hq

/-
lemma parameter_area (pt : PyTriple) :
    pt.area = pt.gp.p * pt.gp.q * (pt.gp.p + pt.gp.q) * (pt.gp.p - pt.gp.q) := by
  sorry
-/

lemma coprime_mul {a b c : ℕ} (hab : Nat.gcd a b = 1) (hac : Nat.gcd a c = 1) :
    Nat.gcd a (b * c) = 1 := by
  rw [Nat.Coprime.gcd_mul_right_cancel_right]
  exact hab
  exact Nat.Coprime.symmetric (Nat.coprime_iff_gcd_eq_one.mp hac)

lemma odd_coprime_two {a : ℕ} (ha_odd : Odd a) : Nat.gcd a 2 = 1 := by
  let g := Nat.gcd a 2

  have div_two : g ∣ 2 := Nat.gcd_dvd_right a 2
  have g_eq : g = 1 ∨ g = 2 := (Nat.dvd_prime Nat.prime_two).mp div_two

  cases g_eq with
  | inl hg => exact hg
  | inr hg =>
    -- If g = 2, then 2 ∣ a, contradicting Odd a
    have ha_even : 2 ∣ a := by
      rw [← hg]
      exact Nat.gcd_dvd_left a 2
    rw [← even_iff_two_dvd] at ha_even
    rw [← Nat.not_even_iff_odd] at ha_odd
    contradiction

theorem coe_gcd (i j : ℕ) : (Nat.gcd i j) = GCDMonoid.gcd i j :=
  rfl


/-
theorem sq_of_gcd_eq_one {a b c : ℕ} (h : Nat.gcd a b = 1) (heq : a * b = c ^ 2) :
    ∃ a0 : ℕ, a = a0 ^ 2 := by
  -- Convert gcd to IsUnit assumption
  have h_unit : IsUnit (gcd a b) := by
    rw [← coe_gcd, h]
    exact isUnit_one

  -- Use multiplicative square decomposition result
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h_unit heq

  -- `u` is a unit in ℕ, which must be 1
  have : (u : ℕ) = 1 := Nat.units_eq_one u
  -- So u = 1 in Units ℕ
  have u_eq : u = 1 := Units.ext this

  -- Finish the proof
  use d
  rw [← hu, u_eq, one_mul]


-- gcd(a, b) = 1
-- gcd(a, c) = 1
-/
