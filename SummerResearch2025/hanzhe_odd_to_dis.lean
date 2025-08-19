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
#check Finset.single_le_sum

lemma odd_is_odd(n:ℕ)(hodd: Odd n) : n % 2 = 1 := by
  unfold Odd at hodd
  rw[ Nat.mod_def]
  rcases hodd with ⟨q,hq⟩
  omega

def binary (n : ℕ): Multiset ℕ := n.bitIndices.map fun i => 2 ^ i

lemma two_pow_in_binary: x ∈ binary n → ∃  (a : ℕ), x = 2 ^ a := by
  intro ha
  unfold binary at ha
  simp[List.mem_map] at ha
  rcases ha with ⟨wit, hwit1, hwit2⟩
  use wit
  exact hwit2.symm

lemma two_pow_in_binary2(a:ℕ)(ha:a∈ binary n): ∃k,a = (2 ^k):=by
  unfold binary at ha
  simp[List.mem_map] at ha
  rcases ha with ⟨wit,hwit1,hwit2⟩
  use wit
  exact hwit2.symm

-- lemma pow_mem_binary (k : ℕ) :  2 ^ k ∈ binary (2 ^ k) ∧  Multiset.count (2 ^ k) (binary (2 ^ k)) = 1 := by
--   -- `bitIndices` of `2 ^ k` is the singleton `[k]`
--   have hidx : (2 ^ k).bitIndices = [k] := by
--     exact Nat.bitIndices_two_pow k
--   -- after `map (fun i ↦ 2^i)` that becomes a singleton multiset
--   have hb : binary (2 ^ k) = {2 ^ k} := by
--     unfold binary; simpa [hidx] using rfl
--   -- membership and count are now immediate
--   have : 2 ^ k ∈ ({2 ^ k} : Multiset ℕ) := by simp
--   have : (2 ^ k ∈ binary (2 ^ k))
--         ∧ Multiset.count (2 ^ k) (binary (2 ^ k)) = 1 := by
--     simpa [hb] using
--       And.intro (by simpa using this) (by simp [hb])
--   exact this

lemma binary_mem_le: 2 ^ i ∈ binary a → 2 ^ i ≤ a := by
  intro h
  unfold binary at h
  simp[List.mem_map] at h
  exact Nat.two_pow_le_of_mem_bitIndices h

-- lemma pow_mem_binary_bit {n k : ℕ} (hbit : n.testBit k = true) : 2 ^ k ∈ binary n ∧ Multiset.count (2 ^ k) (binary n) = 1 := by
--   constructor
--   simp [binary, List.mem_map, hbit]
--   sorry
--   simp [binary, hbit]
--   simp [List.mem_map, Nat.pow_right_injective (le_refl 2)]
--   sorry

lemma mem_binary_iff {k i : ℕ} : (2 ^ i) ∈ binary k ↔ k.testBit i := by
  constructor
  simp [binary, List.mem_map]
  sorry
  sorry
lemma exists_pow_of_mem_binary {k w : ℕ} :
  w ∈ binary k → ∃ i, w = 2 ^ i ∧ k.testBit i := by sorry

lemma binary_nodup : (binary n).Nodup := by
  unfold binary
  sorry

lemma binary_sum (n : ℕ) : (binary n).sum = n := by
  unfold binary
  apply Nat.twoPowSum_bitIndices

def highest_odd_factor : ℕ → ℕ
| 0       => 0
| n@(k+1) =>
  if n % 2 = 1 then n
  else highest_odd_factor (n / 2)

lemma hof_is_odd {n:ℕ} (hn_nonzero: n ≠ 0) : highest_odd_factor n % 2 = 1 := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
    contradiction
  | succ n' =>
    simp[highest_odd_factor]
    by_cases c: (n' + 1) % 2 = 1
    simp[c]
    simp[c]
    have nsuccle: (n' + 1) / 2 < n' + 1 := by omega
    have nsuccnonzero: (n' + 1) / 2 ≠ 0 := by omega
    rcases ih ((n' + 1) / 2) nsuccle nsuccnonzero with h
    exact h

lemma n_non0_hof_non0 {n:ℕ} (hn_nonzero:n ≠ 0): highest_odd_factor n ≠ 0:=by
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

lemma hof_zero_iff_n_zero{n:ℕ} :n = 0 ↔ highest_odd_factor n = 0:=by
  constructor
  intro h
  rw[h]
  simp[highest_odd_factor]
  contrapose
  exact n_non0_hof_non0 (n:= n)

lemma hof_odd_eq_itself{n:ℕ}(hodd:n % 2 = 1):n = highest_odd_factor n :=by
  induction' n using Nat.strong_induction_on with n in'
  cases n with
  | zero    =>
  simp[highest_odd_factor]
  | succ n' =>
  unfold highest_odd_factor
  simp[hodd]

lemma hof_same_under_mul_2{x:ℕ}: highest_odd_factor x = highest_odd_factor (x * 2):=by
  induction' x using Nat.strong_induction_on with x ix
  cases x with
  | zero    =>
  simp[highest_odd_factor]
  | succ x' =>
  cases h : ((x' + 1) * 2) with
  | zero =>
    contradiction
  | succ k =>
    simp [h, highest_odd_factor]
    have k_even: (k + 1) % 2 = 0 := by omega
    have temp: (k.succ)/2 = (x'.succ):=by omega
    by_cases c: x'.succ % 2 = 1
    · simp[c,k_even,temp]
      exact hof_odd_eq_itself (hodd:=c)
    · simp[c,k_even,temp]
      conv_rhs=>
        simp[highest_odd_factor]
        simp[c]

lemma hof_same_undermul_2{n:ℕ}: highest_odd_factor n = highest_odd_factor (n * 2^ x):=by
  induction' x using Nat.strong_induction_on with x ix
  cases x with
  | zero    =>
  simp[highest_odd_factor]
  | succ x' =>
  by_cases c: x' = 0
  ·
    simp[c]
    exact hof_same_under_mul_2
  · have temp: highest_odd_factor (n * 2 ^ (x' + 1)) = highest_odd_factor (n * 2 ^ (x')):=by
      simp[Nat.two_pow_succ]
      simp[←two_mul]
      simp[mul_left_comm n 2 (2 ^ x')]
      simp[mul_comm 2 (n * 2 ^ x')]
      exact hof_same_under_mul_2.symm
    simp[temp]
    apply ix
    simp

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

lemma hof_non0_n_odd: n % 2 =1 → highest_odd_factor n ≠ 0:=by
  intro h
  rw[Nat.mod_def] at h
  have temp: n = 1 + 2 *(n/2) :=by omega
  have temp2 : 1 + 2 *(n/2) ≠ 0 :=by omega
  rw[temp]
  apply (hof_zero_iff_n_zero).not.1
  exact temp2

lemma hof_even_is_0 (n:ℕ)(h: (highest_odd_factor n) % 2 = 0): highest_odd_factor n = 0 :=by
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

lemma hof_divid_n_2tosomepow{n:ℕ}(hn_nonzero:n ≠ 0): ∃ k:ℕ, 2^k = n / highest_odd_factor n := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
    contradiction
  | succ n' =>
    unfold highest_odd_factor
    by_cases c: n'.succ % 2 =1
    · simp[c]
    · simp[c]
      have nsucc_div_2:  n'+1 = (n'+1) / 2 + (n'+1) / 2 := by omega
      -- rw[nsucc_div_2]
      nth_rewrite 1 [nsucc_div_2]
      rw[Nat.add_div_of_dvd_right]
      have ih_le: (n'.succ / 2) < n' + 1 := by omega
      have ih_nonzero: (n'.succ / 2) ≠ 0 := by omega
      rcases ih (n'.succ / 2) ih_le ih_nonzero with ⟨m, hm⟩
      rw[←hm]
      rw[←Nat.two_pow_succ]
      use m + 1
      exact hof_divides ((n'+1)/2)

lemma two_pow_mul_is_hof {n:ℕ}(hxodd: x % 2 = 1): 2^k * x = n → highest_odd_factor n = x := by
  intro h
  rw [Nat.mul_comm] at h
  rw[←h]
  conv_rhs =>
    rw [hof_odd_eq_itself (n:=x) (hodd := hxodd)]
  rw [←hof_same_undermul_2 (x:=k)]

lemma hof_mul_2tosomepow_eq_n{n:ℕ}: ∃ k:ℕ, 2^k * highest_odd_factor n = n  := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
    use 0
    simp[highest_odd_factor]
  | succ n' =>
  unfold highest_odd_factor
  by_cases c: n'.succ % 2 = 1
  simp[c]
  simp[c]
  have hle: ((n' + 1) / 2) < n' + 1 := by omega
  rcases ih (m:= (n' + 1) / 2) hle with ⟨k, hk⟩
  use k + 1
  simp[pow_succ, Nat.mul_comm (n:=2 ^ k) (m:= 2), Nat.mul_assoc,hk,]
  apply Nat.mul_div_cancel_left'
  simp[Nat.mod_def] at c
  omega

lemma hof_mul_2tosomepow_eq_n_unique{n:ℕ} (hn_nonzero: n ≠ 0): ∃! k:ℕ, 2^k * highest_odd_factor n = n := by
  rcases hof_mul_2tosomepow_eq_n (n:=n) with ⟨k,hk⟩
  have highest_odd_factor_nonzero: highest_odd_factor n ≠ 0 := by
    apply n_non0_hof_non0
    exact hn_nonzero
  use k
  constructor
  · exact hk
  · intro k' hk'
    have h: 2 ^ k * highest_odd_factor n = 2 ^ k' * highest_odd_factor n := by rw [hk, hk']
    have hpow: 2 ^ k = 2 ^ k' := by exact (Nat.mul_left_inj (ha:=highest_odd_factor_nonzero)).1 h
    simp [Nat.pow_right_injective (le_refl 2)] at hpow
    exact hpow.symm

lemma hof_mul_pow_two_unique (hodd : (highest_odd_factor a) % 2 = 1) :  ∀ b, highest_odd_factor b = highest_odd_factor a ↔ ∃! t, b = highest_odd_factor a * 2^t := by
  intro b
  constructor
  intro hb
  constructor
  constructor
  sorry
  sorry
  sorry
  sorry

lemma hof_le_n{n:ℕ}: highest_odd_factor n ≤ n := by sorry

def FromOdd_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (odds n)): Multiset ℕ :=
∑ a ∈ P.parts.toFinset, (binary (Multiset.count a P.parts)).map (fun y ↦ y * a)

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

def FromOdd (n : ℕ) (P : n.Partition) (hP : P ∈ (odds n)): n.Partition :=
{parts := FromOdd_parts n P hP,
 parts_pos := FromOdd_parts_pos n P hP,
 parts_sum := FromOdd_parts_sum n P hP}

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
      apply Finset.nodup_toList
    simp[Multiset.coe_toList]
    let f : ℕ → Multiset ℕ :=  (fun a ↦(binary (Multiset.count a P.parts)).map (fun y ↦ y * a))
    apply(List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
        (l:= P.parts.dedup.toList)
        (f:= f)
        (hn:= temp)
      ).1
    simp only [List.coe_toFinset, Multiset.mem_toList, mem_dedup]
    intro n1 hn1mem n2 hn2mem hn1nen2
    have n_odd(n:ℕ)(hnmem:n∈ P.parts): n%2 = 1:=by
      simp at hnmem
      unfold odds at hP
      simp at hP
      specialize hP n
      simp[hnmem] at hP
      have alg_temp: 2 * (n / 2) + 1 = n := by exact Nat.two_mul_div_two_add_one_of_odd hP
      have alg_tempsymm:  n = 2 * (n / 2) + 1:= by omega
      have alg_temp2 : n - 2* ( n / 2) = 1 := by exact Nat.sub_eq_of_eq_add' (a := n) (b:= 2* ( n / 2)) (c:= 1) alg_tempsymm
      simp[Nat.mod_def]
      exact alg_temp2
    have hof_same_one_image(n:ℕ)(hnmem:n∈P.parts)(hnodd:n%2 = 1): ∀ x ∈ f n, highest_odd_factor x = n:= by
      intro x hmem
      unfold f at hmem
      unfold binary at hmem
      let t := (Multiset.count n1 P.parts)
      simp[t] at hmem
      rcases hmem with⟨witness,wmem,hmem⟩
      simp[←hmem]
      have n1_odd_hof_inv: n = highest_odd_factor n:=by
        apply hof_odd_eq_itself
        exact hnodd
      rw[mul_comm]
      conv_rhs =>
        rw[n1_odd_hof_inv]
      symm
      exact hof_same_undermul_2
    have img_ofa_hof_notb(a:ℕ)(hamem:a∈P.parts)(b:ℕ)(hbmem:b∈P.parts)(habne:b≠a):
    ∀ x ∈ f a, highest_odd_factor x ≠ b:=by
      intro x xmem
      by_contra contra
      have hof_a: highest_odd_factor x = a := by
        specialize hof_same_one_image a hamem (n_odd a hamem) x
        exact hof_same_one_image xmem
      simp[contra] at hof_a
      exact habne hof_a
    have subset_ofimg_same_hof(n:ℕ)(hnmem:n∈P.parts)(sub:Multiset ℕ)(hsub:sub≤(f n)):
      ∀ x ∈ sub, highest_odd_factor x = n := by
      intro x xmem
      have hsub' :sub ⊆ f n := by
        exact Multiset.subset_of_le hsub
      have temp: x ∈ f n:=by
        exact Multiset.mem_of_subset (h:= hsub') xmem
      specialize hof_same_one_image n hnmem (n_odd n hnmem) x temp
      exact hof_same_one_image
    simp[Disjoint]
    intro s1 s1_infn1 s1_infn2
    by_contra contra
    rcases Multiset.exists_mem_of_ne_zero contra with ⟨x, hx⟩
    have x_hof_n1: highest_odd_factor x = n1 :=by
      specialize subset_ofimg_same_hof n1 hn1mem s1 s1_infn1 x hx
      exact subset_ofimg_same_hof
    have x_hof_n2: highest_odd_factor x = n2 :=by
      specialize subset_ofimg_same_hof n2 hn2mem s1 s1_infn2 x hx
      exact subset_ofimg_same_hof
    have false: n1 = n2 := by
      rw [x_hof_n1] at x_hof_n2
      exact x_hof_n2
    exact hn1nen2 false

def FromDis_parts (n : ℕ) (P : n.Partition) (_ : P ∈ (distincts n)): Multiset ℕ :=
(P.parts).bind fun y ↦ Multiset.ofList (List.replicate (y/(highest_odd_factor y)) (highest_odd_factor y))

lemma FromDis_parts_pos (n : ℕ) (P : n.Partition) (hP : P ∈ (distincts n)) : i ∈ (FromDis_parts n P hP) → i > 0 := by
  rintro mem
  unfold FromDis_parts at mem
  simp at mem
  rcases mem with ⟨witness,wit_mem⟩
  apply Nat.pos_iff_ne_zero.2
  rw[wit_mem.2.2]
  exact wit_mem.2.1.1

lemma FromDis_parts_sum (n : ℕ) (P : n.Partition) (hP : P ∈ (distincts n)) : (FromDis_parts n P hP).sum = n := by
  unfold FromDis_parts
  simp
  have temp2: ∀ x ∈ P.parts, x / highest_odd_factor x * highest_odd_factor x = x:=by
    intro x hx
    have temp := by
      exact hof_divides x
    exact Nat.div_mul_cancel temp
  have map_simp : P.parts.map (fun x => x / highest_odd_factor x * highest_odd_factor x) = P.parts.map (fun x => x) := by
    apply Multiset.map_congr
    rfl
    exact temp2
  rw[map_simp]
  simp
  exact P.parts_sum

def FromDis (n : ℕ) (P : n.Partition) (hP : P ∈ (distincts n)): n.Partition :=
{parts := FromDis_parts n P hP,
 parts_pos := FromDis_parts_pos n P hP,
 parts_sum := FromDis_parts_sum n P hP}

lemma InOdd (n : ℕ) (P : n.Partition) (hP : P ∈ (distincts n)) : (FromDis n P hP) ∈ (odds n) := by
  unfold FromDis odds
  unfold FromDis_parts
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



--   rw[Function.Bijective]
--   constructor
--   apply Function.HasLeftInverse.injective
--   simp[Function.HasLeftInverse]
--   use otd n
--   unfold Function.LeftInverse
--   unfold dto otd
--   unfold FromDis FromDis_parts FromOdd FromOdd_parts
--   simp only [Subtype.forall, Subtype.mk.injEq]
--   intro p1 h1distinct
--   ext1
--   simp?
--    -- have hf_singleton {y' : ℕ}(hodd : Odd y') (hpos : 0 < y'):
--   -- f y' = ({y'} : Multiset ℕ) := by
--   --   rw [hf]
--   --   have temp: y' % 2 = 1 := by
--   --     apply odd_is_odd
--   --     exact hodd
--   --   simp?
--   --   have temp2: y' / highest_odd_factor y' = 1 := by
--   --     nth_rewrite 1 [←hof_odd_eq_itself (n:= y') (hodd := temp)]
--   --     exact Nat.div_self hpos
--   --   rw[temp2]
--   --   nth_rewrite 1 [←hof_odd_eq_itself (hodd := temp)]
--   --   simp
--   -- let g (y : ℕ) : ℕ := highest_odd_factor y
--   -- have hf_singleton_hof {y' : ℕ}(hodd : Odd y') (hpos : 0 < y') : f y' = ({g y'} : Multiset ℕ) := by
--   --   have temp: y' % 2 = 1 := by
--   --     apply odd_is_odd
--   --     exact hodd
--   --   have hhof : highest_odd_factor y' = y' := by
--   --     rw[ ←hof_odd_eq_itself (hodd := temp)]
--   --   have temp2: y' / highest_odd_factor y' = 1 := by
--   --     nth_rewrite 1 [←hof_odd_eq_itself (n:= y') (hodd := temp)]
--   --     exact Nat.div_self hpos
--   --   -- finish
--   --   simp [f, g, hhof, temp2]
--   -- simp[Finset.sum]
--   -- rw[Multiset.bind]
--   -- apply Multiset.ext.2
--   -- intro a
--   have nodup : p1.parts.Nodup := by
--     simpa [distincts] using (Finset.mem_filter.1 h1distinct).2
--   have each : ∀ x ∈ p1.parts,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x) = ({x} : Multiset ℕ) := by
--     intro x hx
--     have hcnt : Multiset.count x p1.parts = 1 := by
--       simpa using Multiset.count_eq_one_of_mem nodup hx
--     simp [hcnt, binary, List.replicate, Nat.one_mul]
--   have h_rewrite :(∑ x in p1.parts.toFinset,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x))= (∑ x in p1.parts.toFinset, ({x} : Multiset ℕ)) := by
--     refine Finset.sum_congr rfl ?_
--     intro x hx
--     have hx' : (x : ℕ) ∈ p1.parts := by
--       simpa [Multiset.mem_toFinset] using hx
--     simp [each x hx']
--   have h_sum_singletons :(∑ x ∈ p1.parts.toFinset, ({x} : Multiset ℕ)) = p1.parts := by
--     simp only [sum_multiset_singleton, toFinset_val]
--     exact Multiset.dedup_eq_self.2 nodup
--   have sum_eq :(∑ x in p1.parts.toFinset,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)) = p1.parts := by
--     rw [h_rewrite, h_sum_singletons]
--   set f : ℕ → Multiset ℕ :=
--       fun y ↦ ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)) with hf
--   have hf_singleton {y' : ℕ}(hodd : Odd y') (hpos : 0 < y'):  f y' = ({y'} : Multiset ℕ) := by
--     rw [hf]
--     have temp: y' % 2 = 1 := by
--       apply odd_is_odd
--       exact hodd
--     simp?
--     have temp2: y' / highest_odd_factor y' = 1 := by
--       nth_rewrite 1 [←hof_odd_eq_itself (n:= y') (hodd := temp)]
--       exact Nat.div_self hpos
--     rw[temp2]
--     nth_rewrite 1 [←hof_odd_eq_itself (hodd := temp)]
--     simp
--   have h_bind_id : p1.parts.bind f = p1.parts := by
--     have temp1: ∀ x ∈ p1.parts, f x = ({x} : Multiset ℕ) := by
--       intro x hx
--       have hodd : Odd x := by
--         apply odd_is_odd
--         exact (Finset.mem_filter.1 h1distinct).1 hx
--       have hpos : 0 < x := by
--         apply P.parts_pos
--         exact Multiset.mem_toFinset.mp hx
--       exact hf_singleton hodd hpos
--     apply Multiset.bind_singleton


--   apply Function.HasRightInverse.surjective
--   use otd n
--   unfold Function.RightInverse
--   unfold dto otd
--   unfold FromDis FromDis_parts FromOdd FromOdd_parts
--   simp only [Subtype.forall, Subtype.mk.injEq]
--   intro p1
--   ext1
--   simp
--   rcases p1 with ⟨p1_parts, p1_odd⟩
--   ext1
--   simp

  sorry

lemma sum_map_ite_filter{α} [DecidableEq α] {s : Multiset α} (p : α → Prop) [DecidablePred p] (f : α → ℕ) :
  (s.map (fun a => if p a then f a else 0)).sum = ((s.filter p).map f).sum := by
  classical
  refine s.induction_on ?h0 ?hcons
  · simp
  · intro a s ih
    by_cases ha : p a
    · simp [ha, ih]
    · simp [ha, ih]

lemma sum_bind {α β γ}(s : Finset α) (g : α → Multiset β) (f : β → Multiset γ) : (∑ a in s, g a).bind f = ∑ a in s, (g a).bind f := by
    classical
    refine Finset.induction ?_ ?_ s
    · simp
    · intro a s ha ih
      simp [Finset.sum_insert ha, Multiset.bind_add, ih]
-- lemma odd_to_dis_to_odd_id (n : ℕ) (P : n.Partition)(hP : P ∈ (odds n)):
lemma Multiset.count_filter_eq_zero {α} [DecidableEq α] (m : Multiset α) (p : α → Prop)
    [DecidablePred p] {a : α} (ha : ¬ p a) :
    Multiset.count a (m.filter p) = 0 :=
  by simp [Multiset.count_filter, ha]

-- If A is a Finset, it consists of a multiset A.val and a proposition A.nodup that A has no duplicates.

lemma left_inv (n : ℕ)(p1 : n.Partition) (h1odd : p1 ∈ odds n) : FromDis n (FromOdd n p1 h1odd) (InDist n p1 h1odd) = p1 := by
  unfold FromDis FromOdd InDist FromOdd_parts FromDis_parts
  ext1
  simp only [Subtype.forall, Subtype.mk.injEq]
  have aux_inp1_odd: ∀ x ∈ p1.parts, x % 2 = 1 := by
    intro x hx
    unfold odds at h1odd
    simp at h1odd
    specialize h1odd x
    apply odd_is_odd
    exact h1odd hx
  have aux_inp1_pos: ∀ x ∈ p1.parts, 0 < x := by
    intro x hx
    apply p1.parts_pos
    exact hx

  set f : ℕ → Multiset ℕ :=fun y ↦ ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y))
  with hf
  have bind_replicate (x k : ℕ) (hpos: 0 < x) (hodd : x % 2 = 1) :
  ((binary k).map (fun y ↦ y * x)).bind f = ↑(List.replicate k x: Multiset ℕ) := by
    have hfx : ∀ y ∈ binary n, f (y * x) = List.replicate y x := by
      intro y hy
      rcases two_pow_in_binary n hy with ⟨k, htwo_k⟩
      rw[htwo_k]
      rw[hf]
      simp[Nat.mul_comm (n:= 2 ^ k) (m:= x)]
      simp[←hof_same_undermul_2 (n:= x) (x:= k)]
      simp[←hof_odd_eq_itself (hodd := hodd)]
      simp[Nat.mul_div_right (m:= x) (H := hpos)]
    have hbind_rw : (binary k).map (fun y ↦ y * x) = Multiset.map (fun y ↦ y * x) (binary k) := by rfl
    ext a
    by_cases ha: a = x
    · rw[ha]
      simp[Multiset.bind_singleton]
      simp[Multiset.count_bind]
      have temp: Multiset.map (fun x_1 => Multiset.count x (f (x_1 * x))) (binary k) = Multiset.map (fun x_1 => Multiset.count x (List.replicate x_1 x)) (binary k) := by
        apply Multiset.map_congr
        simp
        simp[Multiset.count_replicate]
        intro b hb
        simp[f]
        rcases two_pow_in_binary2 k b hb with ⟨i, rfl⟩
        simp[Nat.mul_comm]
        simp[←hof_same_undermul_2 (n:= x) (x:= i)]
        simp[←hof_odd_eq_itself (n:=x) (hodd:=hodd)]
        simp[Nat.mul_div_right (m:= x) (H := hpos)]
      rw[temp]
      simp[Multiset.count_replicate]
      exact binary_sum k

    ·
      have temp: a ∉ List.replicate k x := by
        intro ha
        simp[Multiset.mem_replicate] at ha
        rcases ha with ⟨ha1,ha2⟩
        exact ha ha2
      have hcnt : List.count a (List.replicate k x) = 0 := by
        exact (List.count_eq_zero).2 temp
      simp[hcnt]
      intro b hb
      rcases two_pow_in_binary2 k b hb with ⟨i, rfl⟩
      have hfx2 : ∀ y ∈ binary k, f (y * x) = List.replicate y x := by
        intro y hy
        rcases two_pow_in_binary2 k y hy with ⟨j, rfl⟩
        unfold f
        have alg_temp: highest_odd_factor (2 ^ j * x) = highest_odd_factor x := by
          rw[Nat.mul_comm (n:= 2 ^ j) (m:= x)]
          rw[←hof_same_undermul_2]
        rw[alg_temp]
        rw[←hof_odd_eq_itself (n:=x) (hodd:=hodd)]
        simp?
        apply Nat.mul_div_left
        exact hpos
      rw[hfx2]
      have temp2: a ∉ List.replicate (2^i) x := by
        intro ha
        simp[Multiset.mem_replicate] at ha
        rcases ha with ⟨ha1,ha2⟩
        contradiction
      exact temp2
      exact hb
  have map_temp1 :
    (∑ x ∈ p1.parts.toFinset,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)).bind f =
    ∑ x ∈ p1.parts.toFinset,((binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)).bind f := by
      apply sum_bind (s:= p1.parts.toFinset) (g:= fun x ↦ (binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)) (f:= f)
--probably there is some way to do a tactic rather than haveing a have ? look at calc tactics
  have map_temp2 :
  (∑ x ∈ p1.parts.toFinset,((binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)).bind f) =
  ∑ x ∈ p1.parts.toFinset, (↑(List.replicate (Multiset.count x p1.parts) x) : Multiset ℕ) := by
    apply Finset.sum_congr rfl
    intro x hx
    specialize aux_inp1_odd x (Multiset.mem_toFinset.mp hx)
    specialize aux_inp1_pos x (Multiset.mem_toFinset.mp hx)
    rw[bind_replicate x (Multiset.count x p1.parts) aux_inp1_pos aux_inp1_odd]
  rw[map_temp1,map_temp2]

  have temp3:  ∑ x ∈ p1.parts.toFinset, ↑(List.replicate (Multiset.count x p1.parts) x) = p1.parts := by
    ext a
    rw [Multiset.count_sum']
    -- Now we want to count how many times `a` appears in the sum
    -- But it appears exactly `Multiset.count a p1.parts` times!
    rw [Finset.sum_eq_single a]
    simp only [coe_count, List.count_replicate_self]
    simp only [mem_toFinset, ne_eq, coe_count]
    intro b hb hne
    -- If `b` is not equal to `a`, then it does not contribute to the count
    simp [List.count_replicate]
    contrapose! hne
    exact hne.1
    simp?
  rw[temp3]

/-
everything here below are the lemma necessary to prove right inverse, we proove the right inverse through a series of rewrites
-/
-- have : (∑ x ∈ (B ).toFinset, p1.parts.filter (fun y ↦  highest_odd_factor y = x)) = p1.parts.filter (fun y ↦ highest_odd_factor y ∈ (B).toFinset) := by
lemma rhs_rw_lemma (n:ℕ)(B:Multiset ℕ) (p1: Partition n):(∑ x ∈ (B ).toFinset, p1.parts.filter (fun y ↦  highest_odd_factor y = x)) = p1.parts.filter (fun y ↦ highest_odd_factor y ∈ (B).toFinset) := by
  refine Finset.induction ?base ?step (B.toFinset)
  · simp only [sum_empty, notMem_empty]
    symm
    apply Multiset.filter_eq_nil.2
    simp
  · intro j fs hs_notmem hmap
    simp only [Finset.sum_insert hs_notmem, hmap]
    let Pfilter := Multiset.filter (fun y : ℕ => highest_odd_factor y = j) p1.parts
    let Qfilter := Multiset.filter (fun y : ℕ => highest_odd_factor y ∈ fs) p1.parts
    have hdisj : Disjoint Pfilter Qfilter := by
      refine (Multiset.disjoint_left).2 ?_
      intro a ha1 ha2
      have aj : (highest_odd_factor a) = j := by simpa using (Multiset.mem_filter.1 ha1).2
      have h_mem_dis : highest_odd_factor a ∈ fs := (Multiset.mem_filter.1 ha2).2
      have : j ∈ fs := by
        by_cases a_odd : j % 2 = 1
        simp[←hof_odd_eq_itself (hodd := a_odd)] at aj
        simp[←hof_odd_eq_itself (hodd := a_odd)] at h_mem_dis
        simp[aj] at h_mem_dis
        exact h_mem_dis
        simp[←aj] at a_odd
        have hof_a_zero: highest_odd_factor a = 0 := hof_even_is_0 (h := a_odd)
        have a_zero : a= 0:= hof_zero_iff_n_zero.2 hof_a_zero
        have : j = 0 := by
          simp[a_zero] at aj
          simp[highest_odd_factor] at aj
          exact aj.symm
        simp[hof_a_zero,←this] at h_mem_dis
        exact h_mem_dis
      exact hs_notmem this
    simp
    have add_disjoint:  Pfilter + Qfilter = Multiset.filter (fun x : ℕ => highest_odd_factor x = j ∨ highest_odd_factor x ∈ fs) p1.parts := by
      ext a
      simp [Multiset.count_add, hdisj]
      have : Multiset.count a Pfilter + Multiset.count a Qfilter = Multiset.count a  (Multiset.filter (fun x => highest_odd_factor x = j ∨ highest_odd_factor x ∈ fs) p1.parts) := by
        have count_P : Multiset.count a Pfilter = (if highest_odd_factor a = j then Multiset.count a p1.parts else 0) := by
          simp [Pfilter, Multiset.count_filter]
        have count_Q : Multiset.count a Qfilter = (if highest_odd_factor a ∈ fs then Multiset.count a p1.parts else 0) := by
          simp [Qfilter, Multiset.count_filter]
        rw [count_P, count_Q]
/-
count or seems like a generalizable claims coult look into doing this as a gerneral lemma
-/
        have count_or : Multiset.count a (Multiset.filter (fun x => highest_odd_factor x = j ∨ highest_odd_factor x ∈ fs) p1.parts) =
          (if (highest_odd_factor a = j ∨ highest_odd_factor a ∈ fs) then Multiset.count a p1.parts else 0) := by
            simp [Multiset.count_filter]
        simp [count_or]
        by_cases hP : highest_odd_factor a = j
        ·
          have hQ : highest_odd_factor a ∉ fs := by
            simp [hP]
            exact hs_notmem
          have : (highest_odd_factor a = j ∨ highest_odd_factor a ∈ fs) := Or.inl hP
          simp[hP, hQ, this]
          contrapose
          intro h
          exact hs_notmem
        ·
          by_cases hQ : highest_odd_factor a ∈ fs
          ·
            have : (highest_odd_factor a = j ∨ highest_odd_factor a ∈ fs) := Or.inr hQ
            simp[hP, hQ, this]
          ·
            have : (highest_odd_factor a = j ∨ highest_odd_factor a ∈ fs) = False := by
              simp [hP, hQ]
            simp [hP, hQ]
      exact this
    simp [Pfilter, Qfilter, add_disjoint]

--have a couple of hof_mem to be reused by this
--∀ {y : ℕ}, y ∈ p1.parts → highest_odd_factor y ∈ (B).toFinset :
lemma hof_mem (n: ℕ) (p1: Partition n) (hb: p1 ∈ distincts n) (B : Multiset ℕ)(hB: B = p1.parts.bind fun y ↦ List.replicate (y / highest_odd_factor y) (highest_odd_factor y)):
∀ {y : ℕ}, y ∈ p1.parts → highest_odd_factor y ∈ (B).toFinset := by
  have nodup_parts : p1.parts.Nodup := by
    simpa [distincts] using (Finset.mem_filter.1 hb).2
  have p1_parts_dedup : p1.parts.dedup = p1.parts := by
    apply Multiset.dedup_eq_self.2 nodup_parts
  have p1_parts_pos_and_non_zero : ∀ x ∈ p1.parts, 0 < x ∧ x ≠ 0 := by
    intro x hx
    constructor
    exact p1.parts_pos hx
    exact Nat.ne_of_gt (p1.parts_pos hx)
  intro y hy
  have : (highest_odd_factor y) ∈ (B) := by
    have : (highest_odd_factor y) ∈ (↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)) : Multiset ℕ) := by
      simp?
      constructor
      rcases p1_parts_pos_and_non_zero y hy with ⟨hpos, hneq0⟩
      exact hof_zero_iff_n_zero.not.1 hneq0
      exact hof_le_n
    rw[hB]
    exact Multiset.mem_bind.2 ⟨y, hy, this⟩
  exact Multiset.mem_toFinset.2 this

-- (hx : x ∈ B.toFinset) → x % 2 = 1
lemma odd_of_mem_B {n : ℕ} {p1 : Partition n} {B : Multiset ℕ} (hB : B = p1.parts.bind (fun y => ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)))) {x : ℕ} (hx : x ∈ B.toFinset) : x % 2 = 1 := by
  have hxB : x ∈ B := by
    simpa using Multiset.mem_toFinset.1 hx
  rw [hB] at hxB
  rcases Multiset.mem_bind.1 hxB with ⟨y, hy_parts, hx_rep⟩
  have y_nonzero : y ≠ 0 :=  Nat.ne_zero_of_lt (p1.parts_pos hy_parts)
  have hx_eq : x = highest_odd_factor y := by
    simp [List.mem_replicate.1 hx_rep]
  have hodd : (highest_odd_factor y) % 2 = 1 := hof_is_odd (n := y) (hn_nonzero := y_nonzero)
  simpa [hx_eq] using hodd

lemma pos_of_mem_B  {n : ℕ} {p1 : Partition n} {B : Multiset ℕ} (hB : B = p1.parts.bind (fun y => ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)))) {x : ℕ} (hx : x ∈ B.toFinset) : x ≠ 0 := by
  have :x%2 =1 := by
    exact odd_of_mem_B hB hx
  simp[Nat.mod_def] at this
  have: x = 1 + 2 * (x/2) := by omega
  omega

--not used
lemma count_of_hof_is_sum (b : ℕ) :
    (List.replicate (b / highest_odd_factor b) (highest_odd_factor b) : Multiset ℕ).count x =
      (if highest_odd_factor b = x then b / x else 0) := by
  by_cases h : highest_odd_factor b = x
  · simp [h, List.count_replicate]
  · simp [h, List.count_replicate]

--not used so far
--pretty helpful rw lemma will probably use it heavily in clean up
lemma hfun: (fun y : ℕ => if  highest_odd_factor y = x then y / highest_odd_factor y else 0)
              = (fun y : ℕ => if highest_odd_factor y = x then y / x else 0) := by
  funext z
  by_cases h : highest_odd_factor z = x
  · simp [h]
  · simp [h]


lemma nat_mul_left_injective {x : ℕ} (hx : x ≠ 0) : Function.Injective (λ y : ℕ => y * x) := by
  intro y₁ y₂ h
  apply mul_left_cancel₀ hx
  simp[h]
  sorry

lemma count_map_binary_eq_if {x a k c : ℕ} (hxpos : x ≠ 0) (hk : a = x * 2 ^ k) : Multiset.count a (Multiset.map (λ y => y * x) (binary c)) = if (2 ^ k) ∈ binary c then 1 else 0 := by
  have hnodup : (Multiset.map (fun y => y * x) (binary c)).Nodup := by
    apply Multiset.Nodup.map
    · simp[nat_mul_left_injective hxpos]
    · exact binary_nodup c
  by_cases hmem : (2 ^ k) ∈ binary c
  · ------------------------------------------------------------
    -- a) `2^k` *is* in `binary c`  →  `count = 1`
    have : a ∈ Multiset.map (fun y => y * x) (binary c) := by
      apply Multiset.mem_map.2
      exact ⟨2 ^ k, hmem, by simpa [hk, mul_comm]⟩
    have hcount : Multiset.count a (Multiset.map (fun y => y * x) (binary c)) = 1 := Multiset.count_eq_one_of_mem (d:=hnodup) (h:=this)
    simpa [hmem] using hcount
  · ------------------------------------------------------------
    have : a ∉ Multiset.map (fun y => y * x) (binary c) := by
      intro ha
      rcases Multiset.mem_map.1 ha with ⟨y, hy, hxy⟩
      have : y = 2 ^ k := by
        simp[hk,Nat.mul_comm,hxpos] at hxy
        exact hxy
      simp[←this] at hmem
      contradiction
    have hcount :
        Multiset.count a (Multiset.map (λ y => y * x) (binary c)) = 0 := by
      exact Multiset.count_eq_zero.mpr this
    simpa [hmem] using hcount

-- lemma count_formula {n x : ℕ} {p1 : n.Partition}{B : Multiset ℕ} (hB :  B = p1.parts.bind (fun y => ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)))) :
--   Multiset.count x B  = ((p1.parts.filter (fun y => highest_odd_factor y = x)).map (fun y => y / x)).sum := by
--   simp [hB, Multiset.count_bind]
--   induction p1.parts using Multiset.induction with
--   | empty =>
--       simp
--   | @cons y s ih =>
--       by_cases h : highest_odd_factor y = x
--       ·
--         simp [h, ih]
--       ·
--         simp [h, ih]
--         simp[←Multiset.coe_count]
--         intro h1 h2
--         by_contra contra
--         sorry




lemma temp(hnonzero: x_1 ≠ 0):∃ k, (List.replicate (x_1 / highest_odd_factor x_1) (highest_odd_factor x_1)) = (List.replicate (2 ^ k) (highest_odd_factor x_1)) := by
  simp [List.replicate, highest_odd_factor, Nat.div_eq_iff, Nat.mul_comm]
  have :  ∃ k2,2 ^ k2 = x_1 / highest_odd_factor x_1  := by
    exact hof_divid_n_2tosomepow (hn_nonzero:=hnonzero)
  rcases this with ⟨k2,hk2⟩
  use k2
  exact hk2.symm

def perExp (n : ℕ) : ℕ :=
  log 2 (n / highest_odd_factor n)

lemma div_eq_pow_perExp {n : ℕ} (hn : n ≠ 0) :n / highest_odd_factor n = 2 ^ perExp n := by
  rcases hof_divid_n_2tosomepow (n := n) hn with ⟨k, hk⟩
  have : perExp n = k := by
    dsimp [perExp]
    simp[←hk]
    apply Nat.log_pow
    simp
  simpa [this] using hk.symm

lemma single_map (hnonzero: x_1 ≠ 0): (List.replicate (x_1 / highest_odd_factor x_1) (highest_odd_factor x_1)) = (List.replicate (2 ^ perExp x_1) (highest_odd_factor x_1)) := by
  simp [List.replicate, highest_odd_factor, Nat.div_eq_iff, Nat.mul_comm]
  have :  ∃ k2,2 ^ k2 = x_1 / highest_odd_factor x_1  := by
    exact hof_divid_n_2tosomepow (hn_nonzero:=hnonzero)
  rcases this with ⟨k2,hk2⟩
  have : perExp x_1 = k2 := by
    simp [perExp]
    simp[←hk2]
    apply Nat.log_pow
    simp
  simpa [this] using hk2.symm

lemma temp2(n:ℕ) (p1:Partition n)(parts_nonzero : ∀ x_1 ∈ p1.parts, x_1 ≠ 0)
: (Multiset.map (fun x_1 => List.count x (List.replicate (x_1 / highest_odd_factor x_1) (highest_odd_factor x_1))) p1.parts) = (Multiset.map (fun x_1 => List.count x (List.replicate (2 ^ perExp x_1) (highest_odd_factor x_1))) p1.parts):= by
  apply Multiset.map_congr
  rfl
  intro x2 hx2
  rw[single_map]
  simp
  specialize parts_nonzero x2 hx2
  exact parts_nonzero


lemma part_iff_bit2
    {n x k a c : ℕ} {p1 : n.Partition}
    (hp  : p1 ∈ distincts n)
    (hax : highest_odd_factor a = x)
    (hk  : x * 2 ^ k = a)
    (hpart : x % 2 = 1)      -- `x` odd because it is a highest odd factor
    (hB : B = p1.parts.bind (fun y ↦ ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y))))
    (hc : c = Multiset.count x B)
    :(a ∈ p1.parts ↔ (2 ^ k) ∈ binary c) := by
  have hnodup : p1.parts.Nodup := by simpa [distincts] using (Finset.mem_filter.1 hp).2
  constructor
  intro hamem
  simp[hc]
  simp[hB]
  simp[Multiset.count_bind]
  rw[temp2]
  simp[binary]
  have nod: (Multiset.map (fun x_1 => List.count x (List.replicate (2 ^ perExp x_1) (highest_odd_factor x_1)))
        p1.parts).Nodup:= by sorry

    -- power is injective and nodup to beginwith
  -- simp[Finset.twoPowSum_toFinset_bitIndices]
  sorry
  sorry

  sorry

lemma map_binary_eq_filter2 (p1 : Partition n) (hp: p1 ∈ distincts n) {x : ℕ}(B : Multiset ℕ) (hB:B = p1.parts.bind fun y ↦ List.replicate (y / highest_odd_factor y) (highest_odd_factor y))  (hx : x ∈ B.toFinset) :
  Multiset.map (fun y : ℕ => y * x) (binary (Multiset.count x B)) = Multiset.filter (fun y : ℕ => highest_odd_factor y = x) p1.parts := by
  ext a
  have nodup_parts : p1.parts.Nodup := by simpa [distincts] using (Finset.mem_filter.1 hp).2
  -- simp[Multiset.map]
  -- simp[Multiset.filter]
  by_cases hax : highest_odd_factor a = x
  · ------------------------------------------------------------------
    -- ❶  `highest_odd_factor a = x`
    rcases hof_mul_2tosomepow_eq_n (n:=a) with ⟨k, hk⟩
    simp[hax,Nat.mul_comm] at hk
    set c : ℕ := Multiset.count x B
    have left : Multiset.count a (map (fun y => y * x) (binary c)) = (if (2^k) ∈ binary c then 1 else 0):= by
      have hxpos: x≠0 := by exact pos_of_mem_B hB hx
      exact count_map_binary_eq_if (x:=x) (a:=a) (k:=k) (c:=c) (hxpos:=hxpos) (hk:=hk.symm)

    have right:  Multiset.count a (Multiset.filter (fun y => highest_odd_factor y = x) p1.parts) = (if (2^k) ∈ binary c then 1 else 0) := by
      by_cases hmem : a ∈ Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts
      · have h1: Multiset.count a (Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts) = 1 := by
         --simp[hmem] --no dup of p1
         sorry
        -- `a ∈ filter _`  ⇒  `a ∈ p1.parts`
        have hamem: a ∈ p1.parts := (Multiset.mem_filter.1 hmem).1
        simp [h1]
        sorry
        --since a is in p1 then the
      · have : Multiset.count a (Multiset.filter (fun y => highest_odd_factor y = x) p1.parts) = 0 := by
          exact Multiset.count_eq_zero.mpr hmem
        have : a ∉ p1.parts := by
          intro h
          exact hmem (by
            have : highest_odd_factor a = x := hax
            exact Multiset.mem_filter.2 ⟨h, this⟩)
        have: 2^k ∉ binary c:= by
          sorry --use part_iff_bit2
        sorry
    simp[left]
    simp[right]

  · ------------------------------------------------------------------
    -- ❷  `highest_odd_factor a ≠ x`
    have hleft  : Multiset.count a (Multiset.map (fun y ↦ y * x) (binary (Multiset.count x B))) = 0 := by
      refine Multiset.count_eq_zero.mpr ?_
      intro hmem
      rcases Multiset.mem_map.1 hmem with ⟨w, hw, rfl⟩
      rcases two_pow_in_binary (x:=w) (n:= (Multiset.count x B)) hw with ⟨j, hj⟩
      have : highest_odd_factor (w * x) = x := by
        have xodd: x% 2 =1:= by
          apply odd_of_mem_B
          exact hB
          exact hx
        simp[hj,Nat.mul_comm,← hof_same_undermul_2,←hof_odd_eq_itself (hodd:=xodd)]
      exact hax this
    have hright : Multiset.count a
                    (Multiset.filter (fun b ↦ highest_odd_factor b = x)
                                     p1.parts) = 0 := by
      refine Multiset.count_eq_zero.mpr ?_
      intro hmem
      exact hax ((Multiset.mem_filter.1 hmem).2)
    simp [hleft, hright]

lemma right_in3 (n : ℕ) (p1 : n.Partition) (hb : p1 ∈ distincts n) : FromOdd n (FromDis n p1 hb) (InOdd n p1 hb) = p1 := by
  unfold FromDis FromOdd FromOdd_parts FromDis_parts
  ext1
  simp only [Subtype.forall, Subtype.mk.injEq]
  -- ext a
  set B : Multiset ℕ := p1.parts.bind (fun y => ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y))) with hB
  have nodup_parts : p1.parts.Nodup := by
    simpa [distincts] using (Finset.mem_filter.1 hb).2
  have p1_parts_dedup : p1.parts.dedup = p1.parts := by
    apply Multiset.dedup_eq_self.2 nodup_parts
  have p1_parts_pos_and_non_zero : ∀ x ∈ p1.parts, 0 < x ∧ x ≠ 0 := by
    intro x hx
    constructor
    exact p1.parts_pos hx
    exact Nat.ne_of_gt (p1.parts_pos hx)
  have rhs_rewrite : (p1.parts : Multiset ℕ) = ∑ x ∈ (B).toFinset, p1.parts.filter (fun y ↦ highest_odd_factor y = x) := by
    have hof_mem : ∀ {y : ℕ}, y ∈ p1.parts → highest_odd_factor y ∈ (B).toFinset := by
      intro y hy
      have : (highest_odd_factor y) ∈ (B) := by
        have : (highest_odd_factor y) ∈ (↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)) : Multiset ℕ) := by
          simp?
          constructor
          rcases p1_parts_pos_and_non_zero y hy with ⟨hpos, hneq0⟩
          exact hof_zero_iff_n_zero.not.1 hneq0
          exact hof_le_n
        exact Multiset.mem_bind.2 ⟨y, hy, this⟩
      exact Multiset.mem_toFinset.2 this
    have parts_eq_filter : (p1.parts.filter (fun y ↦ highest_odd_factor y ∈ (B).toFinset)) = p1.parts := by
      apply Multiset.filter_eq_self.2
      intro y hy
      exact hof_mem hy
    rw[rhs_rw_lemma (n:=n) (B:=B) (p1:=p1), parts_eq_filter]
  rw[rhs_rewrite]
  apply Finset.sum_congr
  rfl
  intro x hx
  simp[map_binary_eq_filter2 (n:=n) (p1:=p1) (hp:=hb) (x:=x) (B:=B) (hB:=hB) (hx:=hx)]




-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := card_bij' (FromOdd n) (FromDis n) (InDist n) (InOdd n) (left_inv n) (right_in3 n)
