import Mathlib

variable (p q : ℕ)

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


lemma rw_py (P : PyTriple) : P.x ^ 2 = P.z ^ 2 - P.y ^ 2 := by
  rw [← P.py, Nat.add_sub_cancel]


lemma coprime_yz (P : PyTriple) : Nat.gcd P.y P.z = 1 := by
  by_contra h

  obtain ⟨p, hp_prime, p_dvd_y, p_dvd_z⟩ := Nat.Prime.not_coprime_iff_dvd.mp h

  have p_dvd_x_sq : p ∣ P.x ^ 2 := by
    rw [rw_py]
    apply Nat.dvd_sub (dvd_pow p_dvd_z two_ne_zero) (dvd_pow p_dvd_y two_ne_zero)

  have p_dvd_gcd : p ∣ Nat.gcd P.x P.y := Nat.dvd_gcd (Nat.Prime.dvd_of_dvd_pow hp_prime p_dvd_x_sq) p_dvd_y
  rw [P.coprime] at p_dvd_gcd
  exact hp_prime.ne_one (Nat.dvd_one.mp p_dvd_gcd)


lemma yodd (P : PyTriple) : Odd P.y := by
  by_contra hyeven
  rw [Nat.not_odd_iff_even] at hyeven
  let hxeven := P.parity
  let hcoprime := P.coprime
  apply Even.two_dvd at hxeven
  apply Even.two_dvd at hyeven
  have : 2 ∣ Nat.gcd P.x P.y := Nat.dvd_gcd hxeven hyeven
  rw [hcoprime] at this
  contradiction


lemma zodd (P : PyTriple) : Odd P.z := by
  have hsum := Even.add_odd (even_square P.parity) (odd_square (yodd P))
  rw [P.py] at hsum
  by_contra hcontra
  rw [Nat.not_odd_iff_even] at hcontra
  apply even_square at hcontra
  rw[← Nat.not_odd_iff_even] at hcontra
  contradiction


lemma ysq_le_zsq (P : PyTriple) : P.y ^ 2 ≤ P.z ^ 2 := by
  rw [← P.py]
  exact Nat.le_add_left (P.y ^ 2) (P.x ^ 2)


lemma y_le_z (P : PyTriple) : P.y ≤ P.z := by
  rw [← Nat.pow_le_pow_iff_left two_ne_zero]
  exact ysq_le_zsq P


lemma y_ne_z (P : PyTriple) : P.y ≠ P.z := by
  intro heq
  let hpy := P.py
  have hx0 : P.x = 0 := by
    rw [heq] at hpy
    simp at hpy
    exact hpy
  have hxne0 := ne_of_gt P.nonzero
  contradiction


lemma zbig (P : PyTriple) : P.y < P.z := by
  rw[lt_iff_le_and_ne]
  constructor
  exact y_le_z P
  exact y_ne_z P


lemma ypos (P : PyTriple) : 0 < P.y := by
  by_contra h
  push_neg at h
  have hy0 : P.y = 0 := Nat.eq_zero_of_le_zero h
  let hyodd := yodd P
  rw [hy0] at hyodd
  exact Nat.not_odd_zero hyodd


lemma x2_pos (P : PyTriple) : 0 < P.x ^ 2 := sq_pos_of_pos P.nonzero


lemma py_pos (P : PyTriple) : 0 < P.x ^ 2 + P.y ^ 2 := by
  rw [Nat.add_pos_iff_pos_or_pos]
  left
  exact x2_pos P


lemma zpos (P : PyTriple) : 0 < P.z := by
  let py_pos := py_pos P
  rw [P.py] at py_pos
  obtain hpos | hzero := Nat.pow_pos_iff.mp py_pos
  · exact hpos
  · exfalso
    norm_num at hzero


lemma yz_2big (P : PyTriple) : 2 ≤ P.z - P.y := by
  let hpos : 0 < P.z - P.y := Nat.sub_pos_of_lt (zbig P)
  let heven : Even (P.z - P.y) := Nat.Odd.sub_odd (zodd P) (yodd P)
  obtain ⟨k, hk⟩ := heven
  rw [hk] at hpos ⊢  -- rewrite P.z - P.y = 2 * k
  cases k with
  | zero => simp at hpos -- contradiction, 0 < 0
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
    rw [hg] at gcd_dvd
    rw [← even_iff_two_dvd] at gcd_dvd
    rw [← Nat.not_odd_iff_even] at gcd_dvd
    contradiction


lemma opp_parity_odd_sum (gp : GoodParam) : Odd (gp.p + gp.q) := by
  rcases gp.parity with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · -- Case: p even, q odd
    rw [add_comm]
    apply Odd.add_even hq hp
  · -- Case: p odd, q even
    apply Odd.add_even hp hq


lemma opp_parity_odd_diff (gp : GoodParam) : Odd (gp.p - gp.q) := by
  rcases gp.parity with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · -- Case: p even, q odd
    apply Nat.Even.sub_odd (le_of_lt gp.pbig) hp hq
  · -- Case: p odd, q even
    apply Nat.Odd.sub_even (le_of_lt gp.pbig) hp hq


theorem coprime_mul {a b c : ℕ} (hab : Nat.gcd a b = 1) (hac : Nat.gcd a c = 1) : Nat.gcd a (b * c) = 1 := by
  rw [Nat.Coprime.gcd_mul_right_cancel_right]
  exact hab
  exact Nat.Coprime.symmetric (Nat.coprime_iff_gcd_eq_one.mp hac)


theorem coe_gcd (i j : ℕ) : (Nat.gcd i j) = GCDMonoid.gcd i j := rfl


theorem sq_of_gcd_eq_one {a b c : ℕ} (h : Nat.gcd a b = 1) (heq : a * b = c ^ 2) :
    ∃ a0 : ℕ, a = a0 ^ 2 := by

  have h_unit : IsUnit (gcd a b) := by
    rw [← coe_gcd, h]
    exact isUnit_one

  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h_unit heq
  have : u = 1 := Nat.units_eq_one u
  let u_eq : (u : ℕ) = 1 := by rw [this, Units.val_one]
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

  rw [← Nat.gcd_add_self_right (p - q) (p + q), add_comm, tsub_add_eq_add_tsub (Nat.le_of_lt gp.pbig), ← add_assoc p p q, add_tsub_cancel_right, ← two_mul]

  have hcoprime_2 : Nat.gcd (p - q) 2 = 1 := by
    rw[odd_coprime_two]
    exact opp_parity_odd_diff gp

  have hcoprime_p : Nat.gcd (p - q) p = 1 := by
    rw [Nat.gcd_comm]
    exact coprime_p_diff gp

  exact coprime_mul hcoprime_2 hcoprime_p

lemma coprime_square_product {a b : ℕ}
    (hcoprime : Nat.gcd a b = 1)
    (hsquare : IsSquare (a * b)):
    IsSquare a ∧ IsSquare b := by

  obtain ⟨c, hc⟩ := hsquare
  rw [← pow_two] at hc

  have ha := sq_of_gcd_eq_one hcoprime hc
  have hb := sq_of_gcd_eq_one (Nat.gcd_comm b a ▸ hcoprime) (by rw [mul_comm, hc])

  obtain ⟨a0, ha0⟩ := ha
  obtain ⟨b0, hb0⟩ := hb

  constructor
  · use a0
    rwa [← pow_two]
  · use b0
    rwa [← pow_two]

lemma coprime_linear_factors (gp : GoodParam) :
    (Nat.gcd gp.p gp.q = 1) ∧
    (Nat.gcd gp.p (gp.p + gp.q) = 1) ∧
    (Nat.gcd gp.p (gp.p - gp.q) = 1) ∧
    (Nat.gcd gp.q (gp.p + gp.q) = 1) ∧
    (Nat.gcd gp.q (gp.p - gp.q) = 1) ∧
    (Nat.gcd (gp.p - gp.q) (gp.p + gp.q) = 1) := by

  exact ⟨gp.coprime, coprime_p_sum gp, coprime_p_diff gp, coprime_q_sum gp, coprime_q_diff gp, coprime_diff_sum gp⟩


lemma lt_sqs_param (gp : GoodParam) : gp.q ^ 2 ≤ gp.p ^ 2 := by
  apply (Nat.pow_le_pow_iff_left (a := gp.q) (b := gp.p) (n := 2) (by decide)).mpr
  exact Nat.le_of_lt gp.pbig


lemma ParamParity (gp : GoodParam) : Even (2 * gp.p * gp.q) := by
  use gp.p * gp.q
  ring


lemma ParamCoprime (gp : GoodParam) : Nat.gcd (2 * gp.p * gp.q) (gp.p ^ 2 - gp.q ^ 2) = 1 := by
  let p := gp.p
  let q := gp.q

  have hodd : Odd (p ^ 2 - q ^ 2) := by
    rcases gp.parity with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · -- Even p, Odd q
      exact Nat.Even.sub_odd (lt_sqs_param gp) (even_square hp) (odd_square hq)
    · -- Odd p, Even q
      exact Nat.Odd.sub_even (lt_sqs_param gp) (odd_square hp) (even_square hq)

  have gcd_p : Nat.gcd (p ^ 2 - q ^ 2) p = 1 := by
    rw [Nat.sq_sub_sq, Nat.gcd_comm]
    exact coprime_mul (coprime_p_sum gp) (coprime_p_diff gp)

  have gcd_q : Nat.gcd (p ^ 2 - q ^ 2) q = 1 := by
    rw [Nat.sq_sub_sq, Nat.gcd_comm]
    exact coprime_mul (coprime_q_sum gp) (coprime_q_diff gp)

  have gcd_2 : Nat.gcd (p ^ 2 - q ^ 2) 2 = 1 := odd_coprime_two hodd

  rw [Nat.gcd_comm]
  exact coprime_mul (coprime_mul gcd_2 gcd_p) gcd_q

lemma ParamPy (gp : GoodParam) : (2 * gp.p * gp.q) ^ 2 + (gp.p ^ 2 - gp.q ^ 2) ^ 2 = (gp.p ^ 2 + gp.q ^ 2) ^ 2 := by
  rw [Nat.sq_sub_sq]
  apply Int.natCast_inj.mp
  simp [Int.natCast_sub (le_of_lt gp.pbig)]
  ring


lemma ParamNonzero (gp : GoodParam) : 0 < 2 * gp.p * gp.q := by
  rw [mul_assoc]
  exact mul_pos zero_lt_two (mul_pos (gt_trans gp.pbig gp.positive) gp.positive)


lemma Nat_sqs_sum {r s : ℕ} (hr : r > s) : (r + s) ^ 2 + (r - s) ^ 2 = 2 * r ^ 2 + 2 * s ^ 2 := by
  apply Int.natCast_inj.mp
  simp [Int.natCast_sub (le_of_lt hr)]
  rw [add_comm, sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg, add_sq, add_comm]
  ring


lemma or_div {a b c : ℕ} (h : a ∣ b ∨ a ∣ c) : a ∣ (b * c) := by
  rcases h with h1 | h2
  · exact Nat.dvd_mul_right_of_dvd h1 c
  · exact Nat.dvd_mul_left_of_dvd h2 b


lemma sum_diff_double {a b : ℕ} (h : b < a) : a + b - (a - b) = 2 * b := by
  rw [add_comm, Nat.add_sub_assoc (Nat.sub_le a b), Nat.sub_sub_self (le_of_lt h), two_mul]


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
  obtain ⟨k, hk⟩ := P.parity
  rw[← two_mul] at hk

  let hpy := P.py
  rw [hk] at hpy

  have hsq_diff : (P.z + P.y) * (P.z - P.y) = 4 * k ^ 2 := by
    rw [← Nat.sq_sub_sq, ← hpy, Nat.add_sub_cancel, pow_two, mul_assoc, mul_comm 2 k, mul_comm k, mul_comm k, mul_assoc, ← pow_two k, ← mul_assoc]
    norm_num

  let h_even_sum : Even (P.z + P.y) := Odd.add_odd (zodd P) (yodd P)
  let h_even_diff : Even (P.z - P.y) := Nat.Odd.sub_odd (zodd P) (yodd P)

  let hdiv2_sum : 2 ∣ (P.z + P.y) := Even.two_dvd h_even_sum
  let hdiv2_diff : 2 ∣ (P.z - P.y) := Even.two_dvd h_even_diff

  set a := (P.z + P.y) with ha
  set b := (P.z - P.y) with hb

  let hab := hsq_diff

  have two_gcd : Nat.gcd a b = 2 := by
    let d : ℕ := Nat.gcd a b

    let gcd_dvd_sum : d ∣ a + b := Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    let gcd_dvd_diff : d ∣ a - b := Nat.dvd_sub (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)

    rw [ha, hb] at gcd_dvd_sum
    nth_rewrite 2 [add_comm] at gcd_dvd_sum
    rw [add_assoc, add_comm, add_assoc, add_comm, Nat.sub_add_cancel (le_of_lt (zbig P)), ← two_mul P.z] at gcd_dvd_sum

    rw [ha, hb, sum_diff_double (zbig P)] at gcd_dvd_diff

    let hdvd_gcd : d ∣ (Nat.gcd (2 * P.y) (2 * P.z)) := Nat.dvd_gcd gcd_dvd_diff gcd_dvd_sum
    rw [Nat.gcd_mul_left] at hdvd_gcd
    rw [coprime_yz P] at hdvd_gcd
    simp at hdvd_gcd

    exact Nat.dvd_antisymm hdvd_gcd (Nat.dvd_gcd hdiv2_sum hdiv2_diff)

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
    calc
      4 * (a / 2) * (b / 2)
        = (2 * (a / 2)) * (2 * (b / 2)) := by ring
      _ = a * (2 * (b / 2))             := by rw [Nat.mul_div_cancel' hdiv2_sum]
      _ = a * b                         := by rw [Nat.mul_div_cancel' hdiv2_diff]

  rw [mul_assoc] at huv
  rw [Nat.mul_right_inj four_ne_zero] at huv

  have gcd_uv_one : Nat.gcd u v = 1 := by
    rw [← hau, ← hbv] at two_gcd
    rw[Nat.gcd_mul_left] at two_gcd
    simp at two_gcd
    exact two_gcd

  have uv_square : IsSquare u ∧ IsSquare v := by
    rw [pow_two] at huv
    exact coprime_square_product gcd_uv_one ⟨k, huv⟩

  obtain ⟨p', hp'⟩ := uv_square.1
  obtain ⟨q', hq'⟩ := uv_square.2
  rw [← pow_two] at hp' hq'
  symm at hp' hq'

  have pq_big : q' < p' := by
    have h1 : p'^2 = (P.z + P.y)/2 := by rw [hp', hu]
    have h2 : q'^2 = (P.z - P.y)/2 := by rw [hq', hv]

    have abig : b < a := by
      rw [ha, hb]
      have add_sum_eq : P.z + P.y - P.y = P.z := by
        simp
      have partial_sum : P.z < P.z + P.y := by
        nth_rewrite 1 [← add_sum_eq]
        have sum_pos : 0 < P.z + P.y := by
          rw [Nat.add_pos_iff_pos_or_pos]
          left
          exact zpos P
        exact Nat.sub_lt (sum_pos) (ypos P)
      exact lt_trans (Nat.sub_lt (zpos P) (ypos P)) partial_sum

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

    have p_pos : 0 < gp'.p := lt_trans pq_positive pq_big

    have ge_two : 2 ≤ 2 * gp'.p * gp'.q := by

      have ge_two_1 : 2 ≤ 2 * gp'.p := Nat.le_mul_of_pos_right 2 p_pos

      have ge_two_2 : 2 * gp'.p ≤ 2 * gp'.p * gp'.q := Nat.le_mul_of_pos_right (2 * gp'.p) pq_positive

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

def Fermat (n : ℕ) : Prop := (∃ (P : PyTriple), n = Area P) → ¬ IsSquare n
noncomputable instance : DecidablePred Fermat := Classical.decPred _

lemma Fermat_area_expand (gp : GoodParam) :
  Area (ParamToTriple gp) = gp.p * gp.q * (gp.p + gp.q) * (gp.p - gp.q) := by
  -- unfold Area and ParamToTriple
  simp only [Area, ParamToTriple]
  nth_rewrite 3 [mul_assoc]
  nth_rewrite 4 [mul_comm]
  rw [← Nat.sq_sub_sq]
  ring_nf
  norm_num


lemma Fermat_p_square (P : PyTriple) (gp : GoodParam) (h : P = ParamToTriple gp)
    (hArea : IsSquare (Area P)) : IsSquare gp.p ∧ IsSquare gp.q ∧ IsSquare (gp.p + gp.q) ∧ IsSquare (gp.p - gp.q) := by
  rw [h] at hArea
  rw [Fermat_area_expand] at hArea
  rcases hArea with ⟨k, hk⟩
  have hsq : IsSquare (gp.p * gp.q * (gp.p + gp.q) * (gp.p - gp.q)) := by
    use k
  have hcoprime1 : Nat.gcd (gp.p - gp.q) (gp.p * gp.q * (gp.p + gp.q)) = 1 := by
    apply coprime_mul
    · apply coprime_mul
      · -- gcd(p - q, p)
        rw [Nat.gcd_comm]
        apply coprime_p_diff
      · -- gcd(p - q, q)
        rw [Nat.gcd_comm]
        apply coprime_q_diff
    · -- gcd(p - q, p + q)
      apply coprime_diff_sum

  have htotal_square : IsSquare ((gp.p - gp.q) * (gp.p * gp.q * (gp.p + gp.q))) := by
    rw [mul_comm]
    exact hsq

  have ⟨hsq_diff, hsq_rest1⟩ := coprime_square_product hcoprime1 htotal_square

  have hcoprime2 : Nat.gcd (gp.p + gp.q) (gp.p * gp.q) = 1 := by
    apply coprime_mul
    rw [Nat.gcd_comm]
    apply coprime_p_sum
    rw [Nat.gcd_comm]
    apply coprime_q_sum

  have htotal_square1 : IsSquare ((gp.p + gp.q) * (gp.p * gp.q)) := by
    rw [mul_comm]
    exact hsq_rest1

  have ⟨hsq_sum, hsq_rest2⟩ := coprime_square_product hcoprime2 htotal_square1

  have ⟨hsq_p, hsq_q⟩ := coprime_square_product gp.coprime hsq_rest2

  exact ⟨hsq_p, hsq_q, hsq_sum, hsq_diff⟩


theorem FermatTriangle
--(P : PyTriple) : ¬ IsSquare (Area P) := by
: ∀ (n : ℕ), Fermat n := by
  by_contra contra
  push_neg at contra
  let n := Nat.find contra
  have sq_n : ¬Fermat n := Nat.find_spec contra
  have min_n : ∀ {m : ℕ}, m < n → Fermat m := by
    intro m hm
    have := Nat.find_min contra hm
    simp at this
    exact this

  simp [Fermat] at sq_n
  rcases sq_n with ⟨⟨P, hP⟩, k, hk⟩
  rw [hP] at hk
  rcases PyTripleToParam P with ⟨gp, hgp⟩

  have h_area : Area P = gp.p * gp.q * (gp.p + gp.q) * (gp.p - gp.q) := by
    rw [hgp]             -- rewrite P as ParamToTriple gp
    exact Fermat_area_expand gp

  have sq_area : IsSquare (Area P) := by
    use k

  rcases Fermat_p_square P gp hgp sq_area with ⟨hsqp, hsqq, ⟨r, hr⟩, ⟨s, hs⟩⟩
  rcases hsqq with ⟨q0, hq0⟩
  rw [← pow_two] at hr hs hq0
  symm at hr hs hq0

  have odd_r2 : Odd (r^2) := by
    rw [hr]
    exact opp_parity_odd_sum gp

  have odd_s2 : Odd (s^2) := by
    rw [hs]
    exact opp_parity_odd_diff gp

  have odd_r : Odd r := by
    by_contra hr_even
    -- Then r = 2 * m for some m
    rw [Nat.not_odd_iff_even] at hr_even
    have hr2_even : Even (r^2) := even_square hr_even
    have hr2_odd := odd_r2
    rw [← Nat.not_even_iff_odd] at odd_r2
    contradiction

  have odd_s : Odd s := by
    by_contra hs_even
    -- Then s = 2 * m for some m
    rw [Nat.not_odd_iff_even] at hs_even
    have hs2_even : Even (s^2) := even_square hs_even
    have hs2_odd := odd_s2
    rw [← Nat.not_even_iff_odd] at odd_s2
    contradiction

  have rbig : r > s := by
    by_contra h
    push_neg at h
    rw [← sq_le_sq₀ (zero_le r) (zero_le s)] at h
    rw [hr, hs] at h
    have h' : gp.p + gp.q > gp.p - gp.q := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_add_of_pos_right _ gp.positive)
    exact Nat.not_le_of_gt h' h

  have even_rs_sum : Even (r + s) := Odd.add_odd odd_r odd_s
  have even_rs_diff : Even (r - s) := Nat.Odd.sub_odd odd_r odd_s

  have div2_sum : 2 ∣ (r + s) := Even.two_dvd even_rs_sum
  have div2_diff : 2 ∣ (r - s) := Even.two_dvd even_rs_diff

  -- one of r+s or r-s is divisible by 4
  have div4 : 4 ∣ (r + s) ∨ 4 ∣ (r - s) := by

    by_cases hdiff : 4 ∣ (r - s)
    · exact Or.inr hdiff
    · left
      apply Nat.dvd_of_mod_eq_zero
      have mod2 : (r - s) % 2 = 0 := Nat.mod_eq_zero_of_dvd div2_diff
      have mod4 : (r - s) % 4 ≠ 0 := by
        intro h
        have := Nat.dvd_of_mod_eq_zero h
        contradiction

      have diffmod4 : (r - s) % 4 = 2 := by
        have diff_even : Even (r - s) := Nat.Odd.sub_odd odd_r odd_s
        rcases diff_even with ⟨k, hk⟩
        rw [hk]
        by_cases hk : Even k
        · rcases hk with ⟨m, rfl⟩
          omega
        · rw [Nat.not_even_iff_odd] at hk
          rcases hk with ⟨m, rfl⟩
          calc
          (2 * m + 1 + (2 * m + 1)) % 4 = (4 * m + 2) % 4 := by congr 1; ring
          _ = 2 := by norm_num
      have smod4 : 2 * s % 4 = 2 := by
        rcases odd_s with ⟨k, rfl⟩
        calc
        (2 * (2 * k + 1)) % 4 = (4 * k + 2) % 4 := by congr 1; ring
        _ = 2 := by norm_num
      calc
        (r + s) % 4
          = ((r - s) + 2 * s) % 4 := by
          congr 1
          apply Int.natCast_inj.mp
          simp[Int.natCast_sub (le_of_lt rbig)]
          ring
        _ = ((r - s) % 4 + (2 * s) % 4) % 4 := by rw [Nat.add_mod]
        _ = (2 + 2) % 4 := by rw [diffmod4, smod4]
        _ = 0 := by norm_num

  have qdvdby2 : 2 ∣ gp.q := by
    have : 4 ∣ (r + s) * (r - s) := or_div div4
    rw [← Nat.sq_sub_sq] at this
    simp [hr, hs] at this
    rw [Nat.sub_add_comm (Nat.sub_le gp.p gp.q), Nat.sub_sub_self (le_of_lt gp.pbig), ← two_mul] at this
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) this

  have q0dvdby2 : 2 ∣ q0 := by
    rw [← hq0] at qdvdby2
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two qdvdby2

  have qdvdby4 : 4 ∣ gp.q := by
    rw [← hq0]
    rw [(by norm_num : 4 = 2 ^ 2), Nat.pow_dvd_pow_iff two_ne_zero]
    exact q0dvdby2

  set u := (r + s) / 2 with hu
  set v := (r - s) / 2 with hv

  -- u = (r+s)/2, v = (r-s)/2, one of which is even
  have div2 : 2 ∣ u ∨ 2 ∣ v := by
    rcases div4 with div_sum | div_diff
    · left
      apply Nat.dvd_div_of_mul_dvd
      exact div_sum
    · right
      apply Nat.dvd_div_of_mul_dvd
      exact div_diff

  have even_u_or_v : Even u ∨ Even v :=
    div2.elim (fun hu => Or.inl (even_iff_two_dvd.mpr hu)) (fun hv => Or.inr (even_iff_two_dvd.mpr hv))

  have four_dvd_diff_sq :  4 ∣ (r - s) ^ 2 := by
    show 2 ^ 2 ∣ (r - s) ^ 2
    rw [Nat.pow_dvd_pow_iff]
    exact div2_diff
    norm_num

  have uv_sq : IsSquare (u ^ 2 + v ^ 2) := by
    rw [hu, hv]
    rw [Nat.div_pow div2_sum, Nat.div_pow div2_diff]
    rw [← Nat.add_mul_div_left _ _ (by norm_num : 0 < 4)]
    norm_num
    rw [Nat.mul_div_cancel_left' four_dvd_diff_sq]
    rw [Nat_sqs_sum rbig]
    have :  2 ^ 2 ∣ (r - s) ^ 2 := by
      rw [Nat.pow_dvd_pow_iff]
      exact div2_diff
      norm_num
    rw [← Nat.left_distrib, mul_comm]
    rw [hr, hs]
    rw [add_assoc]
    rw [Nat.add_sub_of_le (le_of_lt gp.pbig), ← two_mul, mul_comm, ← mul_assoc]
    norm_num
    exact hsqp

  rcases uv_sq with ⟨w, uv_py'⟩
  rw [← pow_two] at uv_py'

  have uv_py : u ^ 2 + v ^ 2 = w ^ 2 := uv_py'
  have vu_py : v ^ 2 + u ^ 2 = w ^ 2 := by
    rw [add_comm]
    exact uv_py

  have p_rs : 2 * gp.p = r^2 + s^2 := by
        rw [hr, hs]
        rw [add_add_tsub_cancel (le_of_lt gp.pbig), ← two_mul]

  have uv_coprime : Nat.gcd u v = 1 := by
    have hp : gp.p = u^2 + v^2 := by

      have double_sqs : r^2 + s^2 = 2 * (u^2 + v^2) := by
        rw [← p_rs]
        rw [hu, hv]
        rw [Nat.div_pow div2_sum, Nat.div_pow div2_diff]
        rw [← Nat.add_mul_div_left _ _ (by norm_num : 0 < 4)]
        norm_num
        rw [Nat.mul_div_cancel_left' four_dvd_diff_sq]
        rw [Nat_sqs_sum rbig]
        rw [← Nat.left_distrib, mul_comm]
        rw [hr, hs]
        rw [add_assoc]
        rw [Nat.add_sub_of_le (le_of_lt gp.pbig), ← two_mul, mul_comm, ← mul_assoc]
        norm_num

      have hp_double : 2 * gp.p = 2 * (u^2 + v^2) := by
        rw [p_rs, double_sqs]

      simp at hp_double
      exact hp_double

    have hq : gp.q = 2 * u * v := by

      have q_rs : 2 * gp.q = r^2 - s^2 := by
        rw [hr, hs]
        rw [Nat.add_sub_sub_cancel (le_of_lt gp.pbig), ← two_mul]

      have four_product : r^2 - s^2 = 4*u*v := by
        rw [← q_rs]
        rw [hu, hv]
        rw [mul_assoc]
        nth_rewrite 2 [mul_comm]
        rw [← Nat.mul_div_mul_comm]
        nth_rewrite 2 [mul_comm]
        norm_num
        rw [Nat.mul_div_cancel_left']
        rw [← Nat.sq_sub_sq]
        rw [← q_rs]
        exact or_div div4
        exact div2_sum
        exact div2_diff

      have hq_double : 2 * gp.q = 2 * (2 * u * v) := by
        rw [q_rs, four_product]
        ring_nf

      simp at hq_double
      exact hq_double

    set d1 := Nat.gcd u v with hd1

    have divp : d1 ∣ gp.p := by
      rw [hp]
      have dvd_u2 : d1 ∣ u ^ 2 := dvd_pow (Nat.gcd_dvd_left u v) two_ne_zero
      have dvd_v2 : d1 ∣ v ^ 2 := dvd_pow (Nat.gcd_dvd_right u v) two_ne_zero
      exact Nat.dvd_add dvd_u2 dvd_v2

    have divq : d1 ∣ gp.q := by
      rw [hq]
      rw [mul_comm]
      have dvd_v : d1 ∣ v := Nat.gcd_dvd_right u v
      exact Nat.dvd_mul_right_of_dvd dvd_v (2 * u)

    have cop_pq : Nat.gcd gp.p gp.q = 1 := gp.coprime

    have d1_div : d1 ∣ Nat.gcd gp.p gp.q := by
      exact Nat.dvd_gcd divp divq

    rw [cop_pq] at d1_div
    rw [Nat.dvd_one] at d1_div
    exact d1_div

  have vu_coprime : Nat.gcd v u = 1 := by
    rw [Nat.gcd_comm]
    exact uv_coprime

  have u_nonzero : 0 < u := by
    rw [Nat.div_pos_iff]
    constructor; exact Nat.two_pos
    obtain ⟨r', hr'⟩ := odd_r
    obtain ⟨s', hs'⟩ := odd_s
    rw [hr', hs']
    linarith

  have v_nonzero : 0 < v := by
    rw [Nat.div_pos_iff]
    constructor; exact Nat.two_pos
    obtain ⟨k, hk⟩ := even_rs_diff

    by_cases k_zero : k = 0
    · simp [k_zero] at hk
      have diff_ne_zero : r - s ≠ 0 := by
        rw [← Nat.pos_iff_ne_zero]
        exact Nat.sub_pos_of_lt rbig
      contradiction
    · rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at k_zero
      rw [hk]
      exact Nat.add_le_add k_zero k_zero

  set m := u * v / 2 with hm

  have m_area_PyTriple : ∃ (P' : PyTriple), m = Area P' := by
    rcases even_u_or_v with u_even | v_even
    · use PyTriple.mk u v w u_even uv_coprime uv_py u_nonzero
      simp [Area, m, u, v]
    · use PyTriple.mk v u w v_even vu_coprime vu_py v_nonzero
      simp [Area, m, u, v]
      rw [Nat.mul_comm]

  have m_eq_p_div_4 : m = (gp.q) / 4 := by
    simp [hm, hu, hv]
    rw [Nat.div_mul_div_comm (Even.two_dvd even_rs_sum) (Even.two_dvd even_rs_diff)]
    rw [← Nat.sq_sub_sq, hr, hs]
    rw [← (Nat.Simproc.add_sub_le _ (le_of_lt gp.pbig))]
    ring_nf
    rw [add_comm, Nat.add_sub_cancel]
    rw [mul_comm, Nat.mul_div_assoc _ qdvdby4]
    rw [mul_comm, Nat.mul_div_assoc _ (dvd_refl 2)]
    norm_num

  have sq_m : IsSquare m := by
    rw [m_eq_p_div_4, ← hq0]
    use q0 / 2
    rw [pow_two]
    rw [← Nat.mul_div_mul_comm q0dvdby2 q0dvdby2, ← pow_two]

  have m_small : m < n := by
    have pge1: 1 ≤ gp.p := by
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
      exact lt_trans gp.positive gp.pbig
    have sum_ge1 : 1 ≤ gp.p + gp.q := by
      exact Nat.add_le_add pge1 (Nat.zero_le gp.q)
    have diff_ge1 : 1 ≤ gp.p - gp.q := by
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
      rw [tsub_pos_iff_lt]
      exact gp.pbig
    rw [hP, h_area, m_eq_p_div_4]
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)]
    rw [mul_comm gp.p gp.q]
    nth_rw 1 [← mul_one gp.q]; apply Nat.mul_lt_mul_of_le_of_lt _ (by norm_num : 1 < 4)
    · rw [Nat.pos_iff_ne_zero]
      apply Nat.mul_ne_zero _ (Nat.one_le_iff_ne_zero.mp diff_ge1)
      apply Nat.mul_ne_zero _ (Nat.one_le_iff_ne_zero.mp sum_ge1)
      exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp gp.positive) (Nat.one_le_iff_ne_zero.mp pge1)
    · nth_rw 1 [← mul_one gp.q]; apply Nat.mul_le_mul _ diff_ge1
      nth_rw 1 [← mul_one gp.q]; apply Nat.mul_le_mul _ sum_ge1
      nth_rw 1 [← mul_one gp.q]; apply Nat.mul_le_mul _ pge1
      exact le_rfl

  have nonsq_m : ¬ IsSquare m := by
    unfold Fermat at min_n
    exact min_n m_small m_area_PyTriple

  contradiction
