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
  positive : q > 0

-- x, y, z, parity, coprime, py
structure PyTriple where
  x : ℕ
  y : ℕ
  z : ℕ
  parity : Even x
  coprime : Nat.gcd x y = 1
  py : x^2 + y^2 = z^2
  nonzero : x > 0

def Area (P : PyTriple) : ℕ :=
  P.x * P.y / 2


lemma odd_square {a : ℕ} (ha : Odd a) : Odd (a ^ 2) := by
  exact ha.pow

lemma even_square {a : ℕ} (ha : Even a) : Even (a ^ 2) := by
  apply (Nat.even_pow' (n := 2) (by decide)).mpr
  exact ha


theorem coprime_yz (P : PyTriple) : Nat.gcd P.y P.z = 1 := by
  by_contra h
  let hcoprime := P.coprime

  -- Extract prime divisor p dividing gcd P.y P.z
  obtain ⟨p, hp_prime, p_dvd_y, p_dvd_z⟩ := Nat.Prime.not_coprime_iff_dvd.mp h

  -- p divides P.y and P.z ⇒ p divides P.z ^ 2 and P.y ^ 2
  have p_dvd_z_sq : p ∣ P.z ^ 2 := dvd_pow p_dvd_z two_ne_zero
  have p_dvd_y_sq : p ∣ P.y ^ 2 := dvd_pow p_dvd_y two_ne_zero

  -- Since P.x ^ 2 + P.y ^ 2 = P.z ^ 2, rearranged: P.x ^ 2 = P.z ^ 2 - P.y ^ 2
  have p_dvd_x_sq : p ∣ P.x ^ 2 := by
    -- From P.x ^ 2 + P.y ^ 2 = P.z ^ 2, rewrite to P.x ^ 2 = P.z ^ 2 - P.y ^ 2
    have hpy := P.py
    have hrearrange : P.x ^ 2 = P.z ^ 2 - P.y ^ 2 := by
      rw [← hpy, Nat.add_sub_cancel]
    rw [hrearrange]
    apply Nat.dvd_sub p_dvd_z_sq p_dvd_y_sq

  -- p divides P.x ^ 2 ⇒ p divides P.x (since p is prime)
  have p_dvd_x : p ∣ P.x := Nat.Prime.dvd_of_dvd_pow hp_prime p_dvd_x_sq
  -- So p divides both x and y
  have p_dvd_gcd : p ∣ Nat.gcd P.x P.y := Nat.dvd_gcd p_dvd_x p_dvd_y
  -- But gcd x y = 1, so p divides 1 ⇒ p = 1 contradiction
  rw [hcoprime] at p_dvd_gcd
  have : p = 1 := Nat.dvd_one.mp p_dvd_gcd
  exact hp_prime.ne_one this


lemma yodd (P : PyTriple) : Odd P.y := by
  by_contra hyeven
  rw [Nat.not_odd_iff_even] at hyeven
  have hxeven := P.parity
  have hcoprime := P.coprime
  apply Even.two_dvd at hxeven
  apply Even.two_dvd at hyeven
  have two_dvd_gcd : 2 ∣ Nat.gcd P.x P.y := Nat.dvd_gcd hxeven hyeven
  rw [hcoprime] at two_dvd_gcd
  contradiction

lemma zodd (P : PyTriple) : Odd P.z := by
  have hx_even : Even (P.x ^ 2) := even_square P.parity
  have hy_odd  : Odd  (P.y ^ 2) := odd_square (yodd P)
  -- even + odd = odd
  have hsum : Odd (P.x ^ 2 + P.y ^ 2) :=
    Even.add_odd hx_even hy_odd
  rw [P.py] at hsum
  -- Odd z² to Odd z?
  have hsq : isSquare (P.z ^ 2) := by
    use P.z
  by_contra hcontra
  rw [Nat.not_odd_iff_even] at hcontra
  apply even_square at hcontra
  rw[← Nat.not_odd_iff_even] at hcontra
  contradiction


lemma zbig (P : PyTriple) : P.y < P.z := by
  have h : P.x ^ 2 + P.y ^ 2 = P.z ^ 2 := P.py
  -- Since x² ≥ 0, we know z² ≥ y²
  have hle : P.y ^ 2 ≤ P.z ^ 2 := by
    rw [← h]
    exact Nat.le_add_left (P.y ^ 2) (P.x ^ 2)
  -- Now use the square root monotonicity to conclude z ≥ y
  have hle' : P.y ≤ P.z := by
    rw [← Nat.pow_le_pow_iff_left two_ne_zero]
    exact hle
  -- Equality would force x = 0
  have hrearrange : P.x ^ 2 = P.z ^ 2 - P.y ^ 2 := by
      rw [← P.py, Nat.add_sub_cancel]
  have hne : P.y ≠ P.z := by
    intro heq
    have hx0 : P.x = 0 := by
      rw [heq] at hrearrange
      simp at hrearrange
      exact hrearrange
    have hxne0 : P.x ≠ 0 := ne_of_gt P.nonzero
    contradiction
  rw[lt_iff_le_and_ne]
  constructor
  exact hle'
  exact hne


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


theorem coprime_mul {a b c : ℕ} (hab : Nat.gcd a b = 1) (hac : Nat.gcd a c = 1) :
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


lemma ParamParity (gp : GoodParam) : Even (2 * gp.p * gp.q) := by
  use gp.p * gp.q
  ring


lemma ParamCoprime (gp : GoodParam) :
  --  (x y : ℕ)
  --  (hx : x = 2 * gp.p * gp.q)
  --  (hy : y = gp.p ^ 2 - gp.q ^ 2):
  --  Nat.gcd x y = 1 := by
    Nat.gcd (2 * gp.p * gp.q) (gp.p ^ 2 - gp.q ^ 2) = 1 := by

  let p := gp.p
  let q := gp.q

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


lemma ParamPy (gp : GoodParam) :
    --(x y z : ℕ)
    --(hx : x = 2 * gp.p * gp.q) (hy : y = gp.p ^ 2 - gp.q ^ 2) (hz : z = gp.p ^ 2 + gp.q ^ 2) :
    --x^2 + y^2 = z^2 := by
    (2 * gp.p * gp.q) ^ 2 + (gp.p ^ 2 - gp.q ^ 2) ^ 2 = (gp.p ^ 2 + gp.q ^ 2) ^ 2 := by

  rw [Nat.sq_sub_sq]
  apply Int.natCast_inj.mp
  simp[Int.natCast_sub (le_of_lt gp.big)]
  ring


lemma ParamNonzero (gp : GoodParam) :
    2 * gp.p * gp.q > 0 := by
  rw [mul_assoc]
  have qpos : gp.q > 0 := gp.positive
  have ppos : gp.p > 0 := by
    have pbig: gp.p > gp.q := gp.big
    exact gt_trans pbig qpos
  have pqpos : gp.p * gp.q > 0 := by
    exact mul_pos ppos qpos
  exact mul_pos zero_lt_two pqpos


def ParamToTriple (gp : GoodParam) : PyTriple :=
{
  x := 2 * gp.p * gp.q,
  y := gp.p ^ 2 - gp.q ^ 2,
  z := gp.p ^ 2 + gp.q ^ 2,
  parity := ParamParity gp,
  coprime := ParamCoprime gp,
  py := ParamPy gp
  nonzero := ParamNonzero gp
}


theorem PyTripleToParam (P : PyTriple) : ∃ gp : GoodParam, P = ParamToTriple gp := by
  -- from x even, want to get x = 2*k, rewrite in terms of k

  obtain ⟨k, hk⟩ := P.parity
  rw[← two_mul] at hk

  have hpy : P.x^2 + P.y^2 = P.z^2 := P.py
  rw [hk] at hpy

  have hsq_diff : (P.z + P.y) * (P.z - P.y) = 4 * k ^ 2 := by
    rw [← Nat.sq_sub_sq, ← hpy, Nat.add_sub_cancel, pow_two, mul_assoc, mul_comm 2 k, mul_comm k, mul_comm k, mul_assoc, ← pow_two k, ← mul_assoc]
    norm_num

  have hy : Odd P.y := yodd P

  have hz : Odd P.z := zodd P

  have h_even_sum : Even (P.z + P.y) := Odd.add_odd hz hy
  have h_even_diff : Even (P.z - P.y) := Nat.Odd.sub_odd hz hy

  -- use theorem coprime_yz (P : PyTriple) : Nat.gcd P.y P.z = 1
  -- gcd (P.z + P.y) (P.z - P.y) = 2

  have hdiv2_sum : 2 ∣ (P.z + P.y) := by
    apply Even.two_dvd
    exact h_even_sum
  have hdiv2_diff : 2 ∣ (P.z - P.y) := by
    apply Even.two_dvd
    exact h_even_diff

  -- Let a = (P.z + P.y), b = (P.z - P.y)
  set a := (P.z + P.y) with ha
  set b := (P.z - P.y) with hb

  have hab : a * b = 4 * k ^ 2 := hsq_diff

  -- gcd x y = 1, gcd y z = 1
  -- want to claim gcd (P.z + P.y) (P.z - P.y) ∣ 2
  -- by parity, claim gcd = 2?

  have two_gcd : Nat.gcd a b = 2 := by
    have gcd_xy : Nat.gcd P.x P.y = 1 := P.coprime
    have gcd_yz : Nat.gcd P.y P.z = 1 := coprime_yz P

    let d : ℕ := Nat.gcd a b

    have gcd_dvd_a : d ∣ a := Nat.gcd_dvd_left a b
    have gcd_dvd_b : d ∣ b := Nat.gcd_dvd_right a b

    have gcd_dvd_sum : d ∣ a + b := Nat.dvd_add gcd_dvd_a gcd_dvd_b
    have gcd_dvd_diff : d ∣ a - b := Nat.dvd_sub gcd_dvd_a gcd_dvd_b

    rw [ha, hb] at gcd_dvd_sum
    nth_rewrite 2 [add_comm] at gcd_dvd_sum
    rw [add_assoc, add_comm, add_assoc, add_comm, Nat.sub_add_cancel (le_of_lt (zbig P)), ← two_mul P.z] at gcd_dvd_sum

    rw [ha, hb, add_comm] at gcd_dvd_diff
    -- simp [le_of_lt (zbig P)] at gcd_dvd_diff

    #check Nat.sub_sub_self

    -- d ∣ 2y, d ∣ 2z
    -- dvd_gcd: d ∣ gcd 2y 2z,
    -- gcd_mul_left gcd mx, my = m * gcd x, y
    -- coprime yz

    sorry

  -- u = (z + y)/2
  -- v = (z - y)/2
  -- isSquare u, v since they will be (p^2, q^2) since u * v = k ^ 2 and gcd u v = 1
  -- set parameters p, q where p = max(p, q)

  sorry

theorem FermatTriangle (P : PyTriple) : ¬ isSquare (Area P) := by
  rintro ⟨k, hk⟩
  sorry
