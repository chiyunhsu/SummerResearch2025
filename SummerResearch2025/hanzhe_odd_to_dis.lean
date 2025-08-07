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

lemma binary_injective : Function.Injective (fun i : ℕ => 2 ^ i) := by
  intro i j h
  have : i = j := Nat.pow_right_injective (le_refl 2) h
  exact this

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

lemma binary_sum (n : ℕ) : (binary n).sum = n := by
  unfold binary
  apply Nat.twoPowSum_bitIndices

def highest_odd_factor : ℕ → ℕ
| 0       => 0
| n@(k+1) =>
  if n % 2 = 1 then n
  else highest_odd_factor (n / 2)

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

lemma hof_even_is_0 (n:ℕ)(h: highest_odd_factor n % 2 = 0): (highest_odd_factor n = 0 ):=by
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

lemma n_sub_n_zero (n:ℕ) : n - n = 0 :=by omega

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

def dto(n:ℕ): distincts n → odds n:=by
  intro distinct
  rcases distinct with ⟨p,p_distinct⟩
  refine{
    val:= FromDis n p p_distinct
    property := InOdd n p p_distinct
  }

def otd(n:ℕ) : odds n → distincts n := by
  intro odds
  rcases odds with ⟨p,p_odd⟩
  refine{
    val:= FromOdd n p p_odd
    property := InDist n p p_odd
  }

lemma odd_is_odd(n:ℕ)(hodd: Odd n) : n % 2 = 1 := by
  unfold Odd at hodd
  rw[ Nat.mod_def]
  rcases hodd with ⟨q,hq⟩
  omega

lemma dto_bij2 (n:ℕ): (dto n).Bijective := by
  rw[Function.Bijective]
  constructor
  apply Function.HasLeftInverse.injective
  simp[Function.HasLeftInverse]
  use otd n
  unfold Function.LeftInverse
  unfold dto otd
  unfold FromDis FromDis_parts FromOdd FromOdd_parts
  simp only [Subtype.forall, Subtype.mk.injEq]
  intro p1 h1distinct
  ext1
  simp?
   -- have hf_singleton {y' : ℕ}(hodd : Odd y') (hpos : 0 < y'):
  -- f y' = ({y'} : Multiset ℕ) := by
  --   rw [hf]
  --   have temp: y' % 2 = 1 := by
  --     apply odd_is_odd
  --     exact hodd
  --   simp?
  --   have temp2: y' / highest_odd_factor y' = 1 := by
  --     nth_rewrite 1 [←hof_odd_eq_itself (n:= y') (hodd := temp)]
  --     exact Nat.div_self hpos
  --   rw[temp2]
  --   nth_rewrite 1 [←hof_odd_eq_itself (hodd := temp)]
  --   simp
  -- let g (y : ℕ) : ℕ := highest_odd_factor y
  -- have hf_singleton_hof {y' : ℕ}(hodd : Odd y') (hpos : 0 < y') : f y' = ({g y'} : Multiset ℕ) := by
  --   have temp: y' % 2 = 1 := by
  --     apply odd_is_odd
  --     exact hodd
  --   have hhof : highest_odd_factor y' = y' := by
  --     rw[ ←hof_odd_eq_itself (hodd := temp)]
  --   have temp2: y' / highest_odd_factor y' = 1 := by
  --     nth_rewrite 1 [←hof_odd_eq_itself (n:= y') (hodd := temp)]
  --     exact Nat.div_self hpos
  --   -- finish
  --   simp [f, g, hhof, temp2]
  -- simp[Finset.sum]
  -- rw[Multiset.bind]
  -- apply Multiset.ext.2
  -- intro a
  have nodup : p1.parts.Nodup := by
    simpa [distincts] using (Finset.mem_filter.1 h1distinct).2
  have each : ∀ x ∈ p1.parts,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x) = ({x} : Multiset ℕ) := by
    intro x hx
    have hcnt : Multiset.count x p1.parts = 1 := by
      simpa using Multiset.count_eq_one_of_mem nodup hx
    simp [hcnt, binary, List.replicate, Nat.one_mul]
  have h_rewrite :(∑ x in p1.parts.toFinset,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x))= (∑ x in p1.parts.toFinset, ({x} : Multiset ℕ)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx' : (x : ℕ) ∈ p1.parts := by
      simpa [Multiset.mem_toFinset] using hx
    simp [each x hx']
  have h_sum_singletons :(∑ x ∈ p1.parts.toFinset, ({x} : Multiset ℕ)) = p1.parts := by
    simp only [sum_multiset_singleton, toFinset_val]
    exact Multiset.dedup_eq_self.2 nodup
  have sum_eq :(∑ x in p1.parts.toFinset,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)) = p1.parts := by
    rw [h_rewrite, h_sum_singletons]
  set f : ℕ → Multiset ℕ :=
      fun y ↦ ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)) with hf
  have hf_singleton {y' : ℕ}(hodd : Odd y') (hpos : 0 < y'):  f y' = ({y'} : Multiset ℕ) := by
    rw [hf]
    have temp: y' % 2 = 1 := by
      apply odd_is_odd
      exact hodd
    simp?
    have temp2: y' / highest_odd_factor y' = 1 := by
      nth_rewrite 1 [←hof_odd_eq_itself (n:= y') (hodd := temp)]
      exact Nat.div_self hpos
    rw[temp2]
    nth_rewrite 1 [←hof_odd_eq_itself (hodd := temp)]
    simp
  have h_bind_id : p1.parts.bind f = p1.parts := by
    have temp1: ∀ x ∈ p1.parts, f x = ({x} : Multiset ℕ) := by
      intro x hx
      have hodd : Odd x := by
        apply odd_is_odd
        exact (Finset.mem_filter.1 h1distinct).1 hx
      have hpos : 0 < x := by
        apply P.parts_pos
        exact Multiset.mem_toFinset.mp hx
      exact hf_singleton hodd hpos
    apply Multiset.bind_singleton


  apply Function.HasRightInverse.surjective
  use otd n
  unfold Function.RightInverse
  unfold dto otd
  unfold FromDis FromDis_parts FromOdd FromOdd_parts
  simp only [Subtype.forall, Subtype.mk.injEq]
  intro p1
  ext1
  simp
  rcases p1 with ⟨p1_parts, p1_odd⟩
  ext1
  simp

  sorry

lemma otd_bij (n:ℕ): (otd n).Bijective := by
  rw[Function.Bijective]
  constructor
  apply Function.HasLeftInverse.injective
  simp[Function.HasLeftInverse]
  use dto n
  unfold Function.LeftInverse
  unfold dto otd
  unfold FromDis FromDis_parts FromOdd FromOdd_parts
  simp only [Subtype.forall, Subtype.mk.injEq]
  intro p1 h1odd
  ext1
  simp?
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
  have bind_replicate (x k : ℕ) (hpos: 0 < x) (hodd : x % 2 = 1) :((binary k).map (fun y ↦ y * x)).bind f = ↑(List.replicate k x: Multiset ℕ) := by
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
  have sum_bind {α β γ}(s : Finset α) (g : α → Multiset β) (f : β → Multiset γ) : (∑ a in s, g a).bind f = ∑ a in s, (g a).bind f := by
    classical
    refine Finset.induction ?_ ?_ s
    · simp
    · intro a s ha ih
      simp [Finset.sum_insert ha, Multiset.bind_add, ih]
  have map_temp1 :
    (∑ x ∈ p1.parts.toFinset,(binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)).bind f =
    ∑ x ∈ p1.parts.toFinset,((binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)).bind f := by
      apply sum_bind

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
    by_cases case: a ∈ p1.parts.toFinset
    ·



















      -- rcases two_pow_in_binary2 n y hy with ⟨k, htwo_k⟩
      -- rw [hf]
      -- rw [htwo_k]
    sorry


    unfold binary
    simp[List.map_map]
    simp[Function.comp_def]


  -- have h1 :(∑ x ∈ p1.parts.toFinset, (binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)).bind f = ∑ x ∈ p1.parts.toFinset, (↑(List.replicate (Multiset.count x p1.parts) x) : Multiset ℕ) := by
  --  sorry
  -- have h2 :∑ x ∈ p1.parts.toFinset, (↑(List.replicate (Multiset.count x p1.parts) x) : Multiset ℕ) = p1.parts := by
  --   sorry














  -- apply Function.HasRightInverse.surjective
  -- use otd n
  -- unfold Function.RightInverse
  -- unfold dto otd
  -- unfold FromDis FromDis_parts FromOdd FromOdd_parts
  -- simp only [Subtype.forall, Subtype.mk.injEq]
  -- intro p1
  -- ext1
  -- simp
  -- rcases p1 with ⟨p1_parts, p1_odd⟩
  -- ext1
  -- simp

  -- sorry




  -- simp[Multiset.map]

  -- simp[Function.Injective]
  -- simp[Function.Injective]
  -- -- prove injective
  -- intro p1 h1odd p2 h2odd heq
  -- simp[otd] at heq
  -- simp[FromOdd] at heq
  -- simp[FromOdd_parts] at heq
  -- -- ext y
  -- simp[binary] at heq
  -- simp[Function.comp_def] at heq
  -- simp[Finset.sum] at heq
  -- let m₁ : Multiset ℕ := ↑(List.map (powMul x) ((Multiset.count x p1.parts).bitIndices))
  -- have hm₁ : m₁ =
  --     ↑(List.map (powMul x) ((Multiset.count x p1.parts).bitIndices)) := rfl
  -- let temp_map (a:ℕ) (ha:a ∈ p1.parts.toFinset): ℕ → ℕ := fun y => y * a
  --injective
  -- intro p1 p2 heq
  -- simp[otd] at heq
  -- simp[FromOdd] at heq
  -- simp[FromOdd_parts] at heq
  -- have p1_parts := p1.val.parts
  -- have p2_parts := p2.val.parts
  -- -- use (dto n)
  -- rw[p1_parts] at heq
  -- rw[p2_parts] at heq
  -- -- constructor
  -- unfold Function.LeftInverse
  -- unfold otd dto
  -- unfold FromOdd FromDis FromOdd_parts FromDis_parts
  -- simp
  -- intro a a_odd
  -- have id_map: (∑ x ∈ a.parts.toFinset, Multiset.map (fun y => y * x) (binary (Multiset.count x a.parts))).bind fun y => ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)) = a.parts := by
  --   sorry
  -- apply Function.leftInverse_iff_comp.2
  -- unfold dto otd
  -- simp
  -- unfold FromDis FromDis_parts FromOdd FromOdd_parts


lemma FromDis_parts_bij (n : ℕ) (P : n.Partition) (hP : P ∈ (distincts n)):
  -- This lemma needs to be rephrased, as FromDis_parts does not return a Partition, but a Multiset.
   True := by
  trivial




-- lemma odd_to_dis_to_odd_id (n : ℕ) (P : n.Partition)(hP : P ∈ (odds n)):

-- If A is a Finset, it consists of a multiset A.val and a proposition A.nodup that A has no duplicates.


-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
-- theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card := card_bij' (FromOdd n) (FromDist n) (InDist n) (InOdd n) RightInv LeftInv
