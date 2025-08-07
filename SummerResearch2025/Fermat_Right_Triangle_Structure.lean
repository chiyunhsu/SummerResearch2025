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
  coprime : Nat.gcd x y = 1
  py : x^2 + y^2 = z^2

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
    -- put the not at the beginning
    rw [← Nat.not_odd_iff_even] at gcd_dvd
    contradiction

lemma odd_square {a : ℕ} (ha : Odd a) : Odd (a ^ 2) := by
  exact ha.pow

lemma even_square {a : ℕ} (ha : Even a) : Even (a ^ 2) := by
  apply (Nat.even_pow' (n := 2) (by decide)).mpr
  exact ha

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

lemma coprime_mul {a b c : ℕ} (hab : Nat.gcd a b = 1) (hac : Nat.gcd a c = 1) :
    Nat.gcd a (b * c) = 1 := by
  rw [Nat.Coprime.gcd_mul_right_cancel_right]
  exact hab
  exact Nat.Coprime.symmetric (Nat.coprime_iff_gcd_eq_one.mp hac)

theorem coe_gcd (i j : ℕ) : (Nat.gcd i j) = GCDMonoid.gcd i j :=
  rfl

theorem sq_of_gcd_eq_one {a b c : ℕ} (h : Nat.gcd a b = 1) (heq : a * b = c ^ 2) :
    ∃ a0 : ℕ, a = a0 ^ 2 := by
  -- Convert gcd to IsUnit assumption
  have h_unit : IsUnit (gcd a b) := by
    rw [← coe_gcd, h]
    exact isUnit_one

  -- Use multiplicative square decomposition result
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h_unit heq

  -- `u` is a unit in ℕ, which must be 1
  have : u = 1 := Nat.units_eq_one u

  -- So ↑u = 1
  have u_eq : (u : ℕ) = 1 := by rw [this, Units.val_one]

  -- Finish the proof
  use d
  rw [← hu, u_eq, mul_one]

lemma coprime_p_sum (gp : GoodParam) : Nat.gcd gp.p (gp.p + gp.q) = 1 := by
  rw [add_comm, Nat.gcd_add_self_right]
  exact gp.coprime

lemma coprime_p_diff (gp : GoodParam) : Nat.gcd gp.p (gp.p - gp.q) = 1 := by
  rw [Nat.gcd_comm, Nat.gcd_self_sub_left (Nat.le_of_lt gp.big), Nat.gcd_comm]
  exact gp.coprime

lemma coprime_q_sum (gp : GoodParam) : Nat.gcd gp.q (gp.p + gp.q) = 1 := by
  rw [Nat.gcd_comm, Nat.gcd_add_self_left]
  exact gp.coprime

lemma coprime_q_diff (gp : GoodParam) : Nat.gcd gp.q (gp.p - gp.q) = 1 := by
    rw [Nat.gcd_sub_self_right (Nat.le_of_lt gp.big), Nat.gcd_comm]
    exact gp.coprime

lemma coprime_diff_sum (gp : GoodParam) : Nat.gcd (gp.p - gp.q) (gp.p + gp.q) = 1 := by
  let p := gp.p
  let q := gp.q

  have hpbig : q ≤ p := by
    exact Nat.le_of_lt gp.big

  rw [← Nat.gcd_add_self_right (p - q) (p + q), add_comm, tsub_add_eq_add_tsub hpbig, ← add_assoc p p q, add_tsub_cancel_right, ← two_mul]
  have h_parity : Odd (p - q) := opp_parity_odd_diff gp
  have hcoprime_2 : Nat.gcd (p - q) 2 = 1 := by
    rw[odd_coprime_two]
    exact h_parity
  have hcoprime_p : Nat.gcd (p - q) p = 1 := by
    rw [Nat.gcd_comm]
    exact coprime_p_diff gp
  exact coprime_mul hcoprime_2 hcoprime_p


lemma ParamCoprime (gp : GoodParam) (x y : ℕ)
    (hx : x = 2 * gp.p * gp.q)
    (hy : y = gp.p ^ 2 - gp.q ^ 2):
    Nat.gcd x y = 1 := by

  let p := gp.p
  let q := gp.q

  rw [hx, hy]

  have hcop : Nat.gcd p q = 1 := gp.coprime
  have hparity := gp.parity

  have gcd_xy : Nat.gcd (2 * p * q) (p ^ 2 - q ^ 2) = 1 := by

    have hqsmall : q ^ 2 ≤ p ^ 2 := by
      apply (Nat.pow_le_pow_iff_left (a := q) (b := p) (n := 2) (by decide)).mpr
      exact Nat.le_of_lt gp.big

    have hodd : Odd (p ^ 2 - q ^ 2) := by
      rcases hparity with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · -- Even p, Odd q
        exact Nat.Even.sub_odd hqsmall (even_square hp) (odd_square hq)
      · -- Odd p, Even q
        exact Nat.Odd.sub_even hqsmall (odd_square hp) (even_square hq)

    have gcd_p : Nat.gcd (p ^ 2 - q ^ 2) p = 1 := by
      rw [Nat.sq_sub_sq, Nat.gcd_comm]
      apply coprime_mul
      · exact coprime_p_sum gp
      · exact coprime_p_diff gp

    have gcd_q : Nat.gcd (p ^ 2 - q ^ 2) q = 1 := by
      rw [Nat.sq_sub_sq, Nat.gcd_comm]
      apply coprime_mul
      · exact coprime_q_sum gp
      · exact coprime_q_diff gp

    have gcd_2 : Nat.gcd (p ^ 2 - q ^ 2) 2 = 1 := by
      apply odd_coprime_two
      exact hodd

    rw [Nat.gcd_comm]
    apply coprime_mul
    apply coprime_mul
    exact gcd_2
    exact gcd_p
    exact gcd_q

  exact gcd_xy


lemma ParamPy (gp : GoodParam) (x y z : ℕ)
    (hx : x = 2 * gp.p * gp.q) (hy : y = gp.p ^ 2 - gp.q ^ 2) (hz : z = gp.p ^ 2 + gp.q ^ 2) :
    x^2 + y^2 = z^2 := by
  rw [hx, hy, hz, Nat.sq_sub_sq]
  apply Int.natCast_inj.mp
  simp[Int.natCast_sub (le_of_lt gp.big)]
  ring

def ParamToTriple (gp : GoodParam) : PyTriple :=
{
  x := 2 * gp.p * gp.q,
  y := gp.p ^ 2 - gp.q ^ 2,
  z := gp.p ^ 2 + gp.q ^ 2,
  coprime := sorry -- lemma to prove
  py := sorry -- lemma to prove
}
