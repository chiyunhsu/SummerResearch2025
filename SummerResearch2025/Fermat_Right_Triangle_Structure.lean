import Mathlib

variable (p q : ℕ)

#check Nat.sq_sub_sq p q

def isSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, k ^ 2 = n

structure GoodParam where
  p : ℕ
  q : ℕ
  pbig : q < p
  coprime : Nat.gcd p q = 1
  parity : (Even p ∧ Odd q) ∨ (Odd p ∧ Even q)
  positive : 0 < q

-- x, y, z, parity, coprime, py
@[ext] structure PyTriple where
  x : ℕ
  y : ℕ
  z : ℕ
  parity : Even x
  coprime : Nat.gcd x y = 1
  py : x^2 + y^2 = z^2
  nonzero : 0 < x

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

lemma ypos (P : PyTriple) : 0 < P.y := by
  by_contra h
  push_neg at h
  -- h : P.y ≤ 0
  have hy0 : P.y = 0 := Nat.eq_zero_of_le_zero h
  -- rewrite P.y to 0 in the Odd hypothesis
  have hyodd : Odd P.y := yodd P
  rw [hy0] at hyodd
  -- now yodd P : Odd 0
  exact Nat.not_odd_zero hyodd

lemma zpos (P : PyTriple) : 0 < P.z := by
  have x2_pos : 0 < P.x ^ 2 := sq_pos_of_pos P.nonzero
  have sum_pos : 0 < P.x ^ 2 + P.y ^ 2 := by
    rw [Nat.add_pos_iff_pos_or_pos]
    left
    exact x2_pos
  -- z^2 = x^2 + y^2
  rw [P.py] at sum_pos
  -- now sum_pos : 0 < P.z ^ 2
  obtain hpos | hzero := Nat.pow_pos_iff.mp sum_pos
  · exact hpos
  · exfalso
    norm_num at hzero


lemma yz_2big (P : PyTriple) : 2 ≤ P.z - P.y := by
  have hy_lt_z := zbig P
  have hpos : 0 < P.z - P.y := Nat.sub_pos_of_lt hy_lt_z
  have hyodd := yodd P
  have hzodd := zodd P
  have heven : Even (P.z - P.y) := Nat.Odd.sub_odd hzodd hyodd
  obtain ⟨k, hk⟩ := heven
  rw [hk] at hpos ⊢  -- rewrite P.z - P.y = 2 * k
  cases k with
  | zero => simp at hpos -- contradiction, since 0 < 0
  | succ k' =>
    have h : 2 ≤ (k' + 1) * 2 := Nat.le_mul_of_pos_left 2 (Nat.succ_pos k')
    rw [mul_comm, two_mul] at h
    exact h


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
    apply Nat.Even.sub_odd (le_of_lt gp.pbig) hp hq
  · -- Case: p odd, q even
    apply Nat.Odd.sub_even (le_of_lt gp.pbig) hp hq


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
  rw [Nat.gcd_comm, Nat.gcd_self_sub_left (Nat.le_of_lt gp.pbig), Nat.gcd_comm]
  exact gp.coprime

lemma coprime_q_sum (gp : GoodParam) : Nat.gcd gp.q (gp.p + gp.q) = 1 := by
  rw [Nat.gcd_comm, Nat.gcd_add_self_left]
  exact gp.coprime

lemma coprime_q_diff (gp : GoodParam) : Nat.gcd gp.q (gp.p - gp.q) = 1 := by
    rw [Nat.gcd_sub_self_right (Nat.le_of_lt gp.pbig), Nat.gcd_comm]
    exact gp.coprime

lemma coprime_diff_sum (gp : GoodParam) : Nat.gcd (gp.p - gp.q) (gp.p + gp.q) = 1 := by
  let p := gp.p
  let q := gp.q

  have hpbig : q ≤ p := Nat.le_of_lt gp.pbig

  rw [← Nat.gcd_add_self_right (p - q) (p + q), add_comm, tsub_add_eq_add_tsub hpbig, ← add_assoc p p q, add_tsub_cancel_right, ← two_mul]
  have h_parity : Odd (p - q) := opp_parity_odd_diff gp
  have hcoprime_2 : Nat.gcd (p - q) 2 = 1 := by
    rw[odd_coprime_two]
    exact h_parity
  have hcoprime_p : Nat.gcd (p - q) p = 1 := by
    rw [Nat.gcd_comm]
    exact coprime_p_diff gp
  exact coprime_mul hcoprime_2 hcoprime_p

lemma coprime_square_product {a b : ℕ}
    (hcoprime : Nat.gcd a b = 1)
    (hsquare : isSquare (a * b)):
    isSquare a ∧ isSquare b := by

  obtain ⟨c, hc⟩ := hsquare

  have ha := sq_of_gcd_eq_one hcoprime hc.symm
  have hb := sq_of_gcd_eq_one (Nat.gcd_comm b a ▸ hcoprime) (by rw [mul_comm, hc])

  obtain ⟨a0, ha0⟩ := ha
  obtain ⟨b0, hb0⟩ := hb

  constructor
  · use a0
    exact ha0.symm
  · use b0
    exact hb0.symm


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
      exact Nat.le_of_lt gp.pbig

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
  simp[Int.natCast_sub (le_of_lt gp.pbig)]
  ring


lemma ParamNonzero (gp : GoodParam) :
    0 < 2 * gp.p * gp.q := by
  rw [mul_assoc]
  have qpos : 0 < gp.q := gp.positive
  have ppos : 0 < gp.p := by
    have pbig: gp.q < gp.p := gp.pbig
    exact gt_trans pbig qpos
  have pqpos : 0 < gp.p * gp.q := by
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

    have gcd_rw : P.z + P.y - (P.z - P.y) = 2*P.y := by
      have hcancel : P.z - (P.z - P.y) = P.y := by
        exact Nat.sub_sub_self (le_of_lt (zbig P))
      rw [add_comm, Nat.add_sub_assoc (Nat.sub_le P.z P.y), hcancel, two_mul]

    rw [ha, hb, gcd_rw] at gcd_dvd_diff
    -- d ∣ 2y, d ∣ 2z
    -- dvd_gcd: d ∣ gcd 2y 2z
    have hdvd_gcd : d ∣ (Nat.gcd (2 * P.y) (2 * P.z)) := Nat.dvd_gcd gcd_dvd_diff gcd_dvd_sum
    -- gcd_mul_left gcd mx, my = m * gcd x, y
    rw[Nat.gcd_mul_left] at hdvd_gcd
    -- coprime yz
    rw [coprime_yz P] at hdvd_gcd
    simp at hdvd_gcd

    have two_div : 2 ∣ d := Nat.dvd_gcd hdiv2_sum hdiv2_diff
    exact Nat.dvd_antisymm hdvd_gcd two_div

  set u := (P.z + P.y) / 2 with hu
  set v := (P.z - P.y) / 2 with hv

  have hau : 2 * u = a := by
    rw [hu, ← ha, mul_comm]
    exact Nat.div_mul_cancel hdiv2_sum
  have hbv : 2 * v = b := by
    rw [hv, ← hb, mul_comm]
    exact Nat.div_mul_cancel hdiv2_diff

  have huv : 4 * u * v = 4 * k ^ 2 := by
    rw [hu, hv, ←ha, ←hb, ←hab]
    -- goal: 4 * (a/2) * (b/2) = a*b
    calc
      4 * (a / 2) * (b / 2)
        = (2 * (a / 2)) * (2 * (b / 2)) := by ring
      _ = a * (2 * (b / 2))             := by rw [Nat.mul_div_cancel' hdiv2_sum]
      _ = a * b                         := by rw [Nat.mul_div_cancel' hdiv2_diff]

  rw [mul_assoc] at huv
  rw [Nat.mul_right_inj four_ne_zero] at huv

  have gcd_uv_one : Nat.gcd u v = 1 := by
    have hab_gcd : Nat.gcd a b = 2 := two_gcd
    rw [← hau, ← hbv] at hab_gcd
    rw[Nat.gcd_mul_left] at hab_gcd
    simp at hab_gcd
    exact hab_gcd

  -- isSquare u, v
  have uv_square : isSquare u ∧ isSquare v := by
    exact coprime_square_product gcd_uv_one ⟨k, huv.symm⟩

  -- (p'^2 = u, q'^2 = v)
  obtain ⟨p', hp'⟩ := uv_square.1
  obtain ⟨q', hq'⟩ := uv_square.2

  -- set params and prove max(p, q) = p

  have pq_big : q' < p' := by
    -- p'^2 = u = (P.z + P.y)/2
    -- q'^2 = v = (P.z - P.y)/2
    have h1 : p'^2 = (P.z + P.y)/2 := by rw [hp', hu]
    have h2 : q'^2 = (P.z - P.y)/2 := by rw [hq', hv]

    have abig : b < a := by
      rw [ha, hb]
      have partial_diff : P.z - P.y < P.z := by
        exact Nat.sub_lt (zpos P) (ypos P)
      have add_sum_eq : P.z + P.y - P.y = P.z := by
        simp
      have partial_sum : P.z < P.z + P.y := by
        nth_rewrite 1 [← add_sum_eq]
        have sum_pos : 0 < P.z + P.y := by
          rw [Nat.add_pos_iff_pos_or_pos]
          left
          exact zpos P
        exact Nat.sub_lt (sum_pos) (ypos P)
      exact lt_trans partial_diff partial_sum

    rw [← ha] at h1
    rw [← hb] at h2
    have sq_ineq : q' ^ 2 < p' ^ 2 := by
      rw [h1, h2]
      apply (Nat.div_lt_div_right two_ne_zero hdiv2_diff hdiv2_sum).mpr
      exact abig
    apply (Nat.pow_lt_pow_iff_left two_ne_zero).mp
    exact sq_ineq

  have pq_coprime : Nat.gcd p' q' = 1 := by
    rw [← Int.gcd_natCast_natCast, Int.isCoprime_iff_gcd_eq_one.symm, Nat.isCoprime_iff_coprime]
    have p2q2_coprime : (p' ^ 2).Coprime (q' ^ 2) := by
      rw [hp', hq']
      exact gcd_uv_one
    rw [← Nat.coprime_pow_left_iff zero_lt_two, ← Nat.coprime_pow_right_iff zero_lt_two]
    exact p2q2_coprime

  have pq_parity : (Even p' ∧ Odd q') ∨ (Odd p' ∧ Even q') := by
    -- case 1: rule out both even
    by_cases hp : Even p'
    · by_cases hq : Even q'
      · -- both even ⇒ gcd(p',q') ≥ 2, contradiction
        have : 2 ∣ Nat.gcd p' q' := Nat.dvd_gcd (Even.two_dvd hp) (Even.two_dvd hq)
        rw [pq_coprime] at this
        contradiction
      · -- p' even, q' odd
        rw [Nat.not_even_iff_odd] at hq
        exact Or.inl ⟨hp, hq⟩
    · -- p' odd
      by_cases hq : Even q'
      · -- p' odd, q' even
        rw [Nat.not_even_iff_odd] at hp
        exact Or.inr ⟨hp, hq⟩
      · -- both odd ⇒ contradiction because z odd
        have hu' : p' ^ 2 = u := hp'
        have hv' : q' ^ 2 = v := hq'
        rw [Nat.not_even_iff_odd] at hp
        rw [Nat.not_even_iff_odd] at hq
        have hup : Odd u := by rw [← hu']; exact odd_square hp
        have hvp : Odd v := by rw [← hv']; exact odd_square hq
        have uv_even : Even (u + v) := Odd.add_odd hup hvp
        -- but u+v = z
        have uv_sum : u + v = P.z := by
          rw [hu, hv]
          rw [← Nat.add_div_of_dvd_left]
          nth_rewrite 2 [add_comm]
          rw [add_assoc, add_comm, add_assoc, add_comm, Nat.sub_add_cancel (le_of_lt (zbig P)), ← two_mul P.z]
          simp
          exact hdiv2_diff
        have z_even : Even P.z := by
          rw [← uv_sum]
          exact uv_even
        have z_odd : Odd P.z := zodd P
        rw [← Nat.not_even_iff_odd] at z_odd
        contradiction

  have pq_positive : 0 < q' := by
    have hv' : q'^2 = v := hq'
    have v_pos : 0 < v := by
      rw [hv]
      exact Nat.div_pos (yz_2big P) zero_lt_two
    rw [← hv'] at v_pos
    rw [Nat.pow_pos_iff] at v_pos
    cases v_pos with
    | inl hv => exact hv
    | inr hv =>
      contradiction

  let gp' : GoodParam :=
  { p := p'
  , q := q'
  , pbig := pq_big
  , coprime := pq_coprime
  , parity := pq_parity
  , positive := pq_positive }

  refine ⟨gp', ?_⟩

  have gp_x : P.x = 2 * gp'.p * gp'.q := by
    rw [← sq_eq_sq₀, Nat.mul_pow, Nat.mul_pow, hp', hq']
    rw [mul_assoc, huv, ← Nat.mul_pow, sq_eq_sq₀, hk]

    exact Nat.zero_le P.x

    rw [← hk]
    exact Nat.zero_le P.x

    exact Nat.zero_le P.x

    have p_pos : 0 < gp'.p := by
      exact lt_trans pq_positive pq_big

    have ge_two : 2 ≤ 2 * gp'.p * gp'.q := by

      have ge_two_1 : 2 ≤ 2 * gp'.p := by
        exact Nat.le_mul_of_pos_right 2 p_pos

      have ge_two_2 : 2 * gp'.p ≤ 2 * gp'.p * gp'.q := by
        exact Nat.le_mul_of_pos_right (2 * gp'.p) pq_positive

      exact le_trans ge_two_1 ge_two_2

    exact le_trans zero_le_two ge_two

  have gp_y : P.y = gp'.p ^ 2 - gp'.q ^ 2 := by
    rw [hp', hq', hu, hv, ← ha, ← hb]
    have htwice : P.y = (a - b)/2 := by
      rw [ha, hb]

      have gcd_rw : P.z + P.y - (P.z - P.y) = 2*P.y := by
        have hcancel : P.z - (P.z - P.y) = P.y := by
          exact Nat.sub_sub_self (le_of_lt (zbig P))
        rw [add_comm, Nat.add_sub_assoc (Nat.sub_le P.z P.y), hcancel, two_mul]

      rw [gcd_rw]
      norm_num
    rw [htwice]

    obtain ⟨a', ha'⟩ := hdiv2_sum
    obtain ⟨b', hb'⟩ := hdiv2_diff

    rw [ha', hb']
    rw [← Nat.mul_sub_left_distrib 2]
    norm_num

  have gp_z : P.z = gp'.p ^ 2 + gp'.q ^ 2 := by
    rw [hp', hq', hu, hv, ← ha, ← hb]
    have htwice : P.z = (a + b)/2 := by
      rw [ha, hb]
      nth_rewrite 2 [add_comm]
      rw [add_assoc, add_comm, add_assoc, add_comm, Nat.sub_add_cancel (le_of_lt (zbig P)), ← two_mul P.z]
      norm_num
    rw [htwice]

    obtain ⟨a', ha'⟩ := hdiv2_sum
    obtain ⟨b', hb'⟩ := hdiv2_diff

    rw [ha', hb']
    rw [← Nat.mul_add 2]
    norm_num

  apply PyTriple.ext
  exact gp_x
  exact gp_y
  exact gp_z

theorem FermatTriangle (P : PyTriple) : ¬ isSquare (Area P) := by
  rintro ⟨k, hk⟩
  sorry
