import Mathlib
/-!
# Euler's Identity for Integer Partitions

This file proves Euler's famous identity: the number of partitions of n into odd parts
equals the number of partitions of n into distinct parts.
-/

variable (n : ℕ)
variable (P : n.Partition)
#check P.parts
#check P.parts_pos
#check P.parts_sum

open Nat Partition Multiset Finset
#check Multiset.sort
#check Finset.single_le_sum

lemma odd_is_odd (n : ℕ) (hodd: Odd n) : n % 2 = 1 := by
  unfold Odd at hodd
  rw [Nat.mod_def]
  rcases hodd with ⟨q,hq⟩
  omega

def binary (n : ℕ): Multiset ℕ := n.bitIndices.map fun i => 2 ^ i

lemma mem_binary_is_power_of_two {x n : ℕ} : x ∈ binary n → ∃ k, x = 2 ^ k := by
  intro h
  unfold binary at h
  simp [List.mem_map] at h
  rcases h with ⟨wit, hwit1, hwit2⟩
  use wit
  exact hwit2.symm

lemma sorted_lt_nodup {l : List ℕ} (h : l.Sorted (· < ·)) : l.Nodup := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      -- `sorted_cons.1` splits the hypothesis:
      -- `ha : ∀ b ∈ l, a < b` and `hl : l.Sorted (· < ·)`
      rcases List.sorted_cons.1 h with ⟨ha, hl⟩
      have hnot : a ∉ l := by
        intro hmem
        have : a < a := ha a hmem
        exact (lt_irrefl a this)
      simpa using (List.nodup_cons.mpr ⟨hnot, ih hl⟩)

lemma binary_nodup : (binary n).Nodup := by
  unfold binary
  simp only [coe_nodup]
  apply List.Nodup.map
  simp [Function.Injective]
  have sorted: n.bitIndices.Sorted (· < ·) := by
    exact Nat.bitIndices_sorted
  exact sorted_lt_nodup (h:=sorted)

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
    exact ih ((n' + 1) / 2) nsuccle nsuccnonzero

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
  exact n_non0_hof_non0

lemma hof_odd_eq_itself{n:ℕ}(hodd:n % 2 = 1):n = highest_odd_factor n :=by
  induction' n using Nat.strong_induction_on with n ih
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

lemma hof_even_is_0 (n:ℕ)(h: (highest_odd_factor n) % 2 = 0): highest_odd_factor n = 0 :=by
  by_cases c: n = 0
  rw[c]
  simp[highest_odd_factor]
  apply hof_zero_iff_n_zero.not.1 at c
  false_or_by_contra
  have temp: n ≠ 0 := by
    exact hof_zero_iff_n_zero.not.2 c
  have temp2: highest_odd_factor n % 2 = 1:= by
    exact hof_is_odd (hn_nonzero:=temp)
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

lemma hof_le_n{n:ℕ}: highest_odd_factor n ≤ n := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero    =>
    simp[highest_odd_factor]
  | succ n' =>
    simp[highest_odd_factor]
    by_cases c: n'.succ % 2 = 1
    simp[c]
    simp[c]
    have hle: ((n' + 1) / 2) < n' + 1 := by omega
    specialize ih (m:= (n' + 1) / 2) hle
    have : (n' + 1) / 2 ≤ (n' + 1) := by omega
    omega

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
    simp[Multiset.coe_toList]
    let f : ℕ → Multiset ℕ :=  (fun a ↦(binary (Multiset.count a P.parts)).map (fun y ↦ y * a))
    apply(List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
        (l:= P.parts.dedup.toList)
        (f:= f)
        (hn:= (Finset.nodup_toList (s:=P.parts.toFinset)))
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

lemma sum_bind {α β γ}(s : Finset α) (g : α → Multiset β) (f : β → Multiset γ) : (∑ a in s, g a).bind f = ∑ a in s, (g a).bind f := by
  classical
  refine Finset.induction ?_ ?_ s
  · simp
  · intro a s ha ih
    simp [Finset.sum_insert ha, Multiset.bind_add, ih]

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

  set f : ℕ → Multiset ℕ :=fun y ↦ ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y)) with hf
  have bind_replicate (x k : ℕ) (hpos: 0 < x) (hodd : x % 2 = 1) : ((binary k).map (fun y ↦ y * x)).bind f = ↑(List.replicate k x: Multiset ℕ) := by
    ext a
    by_cases ha: a = x
    · rw [ha]
      simp [Multiset.bind_singleton]
      simp [Multiset.count_bind]
      have temp: Multiset.map (fun x_1 => Multiset.count x (f (x_1 * x))) (binary k) = Multiset.map (fun x_1 => Multiset.count x (List.replicate x_1 x)) (binary k) := by
        apply Multiset.map_congr
        simp [Multiset.count_replicate]
        intro b hb
        simp [f]
        rcases mem_binary_is_power_of_two  hb with ⟨i, rfl⟩
        simp [Nat.mul_comm]
        simp [←hof_same_undermul_2 (x:= i), ←hof_odd_eq_itself (hodd:=hodd), Nat.mul_div_right (H := hpos)]
      rw [temp]
      simp [Multiset.count_replicate]
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
      rcases mem_binary_is_power_of_two hb with ⟨i, rfl⟩
      have hfx2 : ∀ y ∈ binary k, f (y * x) = List.replicate y x := by
        intro y hy
        rcases mem_binary_is_power_of_two  hy with ⟨j, rfl⟩
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
  simp [sum_bind (s:= p1.parts.toFinset) (g:= fun x ↦ (binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)) (f:= f)]
  calc
    (∑ x ∈ p1.parts.toFinset,((binary (Multiset.count x p1.parts)).map (fun y ↦ y * x)).bind f) =
    ∑ x ∈ p1.parts.toFinset, (↑(List.replicate (Multiset.count x p1.parts) x) : Multiset ℕ) := by
      apply Finset.sum_congr rfl
      intro x hx
      specialize aux_inp1_odd x (Multiset.mem_toFinset.mp hx)
      specialize aux_inp1_pos x (Multiset.mem_toFinset.mp hx)
      rw[bind_replicate x (Multiset.count x p1.parts) aux_inp1_pos aux_inp1_odd]
    _ = p1.parts := by
      ext a
      rw [Multiset.count_sum']
      rw [Finset.sum_eq_single a]
      simp only [coe_count, List.count_replicate_self]
      simp only [mem_toFinset, ne_eq, coe_count]
      intro b hb hne
      simp [List.count_replicate]
      contrapose! hne
      exact hne.1
      simp?

/-
everything here below are the lemma necessary to prove right inverse, we proove the right inverse through a series of rewrites
-/
-- have : (∑ x ∈ (B ).toFinset, p1.parts.filter (fun y ↦  highest_odd_factor y = x)) = p1.parts.filter (fun y ↦ highest_odd_factor y ∈ (B).toFinset) := by

lemma hof_mem {n: ℕ} (p1: Partition n) {B : Multiset ℕ}(hB: B = p1.parts.bind fun y ↦ List.replicate (y / highest_odd_factor y) (highest_odd_factor y)):
∀ {y : ℕ}, y ∈ p1.parts → highest_odd_factor y ∈ (B).toFinset := by
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

lemma sum_filters_by_key
  {α β : Type*} [DecidableEq α] [DecidableEq β]
  (S : Finset β) (g : α → β) (M : Multiset α) :
  ∑ x ∈ S, Multiset.filter (fun y => g y = x) M = Multiset.filter (fun y => g y ∈ S) M := by
  classical
  ext a
  calc
    Multiset.count a (∑ x ∈ S, Multiset.filter (fun y => g y = x) M)
        = ∑ x ∈ S, Multiset.count a (Multiset.filter (fun y => g y = x) M) := by
          refine Finset.induction_on S ?base ?step
          · simp
          · intro x s hx ih
            simpa [Finset.sum_insert, hx, Multiset.count_add, ih]
    _ = ∑ x ∈ S, (if g a = x then Multiset.count a M else 0) := by
          simp [Multiset.count_filter, eq_comm]
    _ = (if g a ∈ S then Multiset.count a M else 0) := by
          classical
          by_cases hmem : g a ∈ S
          · simpa [hmem] using
              Finset.sum_eq_single_of_mem
                (f := fun x => if g a = x then Multiset.count a M else 0)
                hmem
                (by
                  intro x hx hxne
                  simp [hxne.symm])
          · have hzero : ∀ x ∈ S, (if g a = x then Multiset.count a M else 0) = 0 := by
                intro x hx
                by_cases hxeq : g a = x
                · exact (hmem (by simpa [hxeq])).elim
                · simp [hxeq]
            have : ∑ x ∈ S, (if g a = x then Multiset.count a M else 0)
                    = ∑ x ∈ S, 0 := by
              refine Finset.sum_congr rfl ?_
              intro x hx; simpa [hzero x hx]
            simpa [hmem, Finset.sum_const_zero] using this
    _ = Multiset.count a (Multiset.filter (fun y => g y ∈ S) M) := by
          simp [Multiset.count_filter]

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


lemma nat_mul_left_injective {x : ℕ} (hx : x ≠ 0) : Function.Injective (λ y : ℕ => y * x) :=
  fun a b h => Nat.mul_right_cancel (Nat.pos_of_ne_zero hx) h

lemma count_map_binary_eq_if {x a k c : ℕ} (hxpos : x ≠ 0) (hk : a = x * 2 ^ k) : Multiset.count a (Multiset.map (λ y => y * x) (binary c)) = if (2 ^ k) ∈ binary c then 1 else 0 := by
  have hnodup : (Multiset.map (fun y => y * x) (binary c)).Nodup := by
    apply Multiset.Nodup.map
    · simp[nat_mul_left_injective hxpos]
    · exact binary_nodup c
  by_cases hmem : (2 ^ k) ∈ binary c
  · have : a ∈ Multiset.map (fun y => y * x) (binary c) := by
      apply Multiset.mem_map.2
      exact ⟨2 ^ k, hmem, by simpa [hk, mul_comm]⟩
    have hcount : Multiset.count a (Multiset.map (fun y => y * x) (binary c)) = 1 := Multiset.count_eq_one_of_mem (d:=hnodup) (h:=this)
    simpa [hmem] using hcount
  · have : a ∉ Multiset.map (fun y => y * x) (binary c) := by
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

lemma count_replicate_hof_actual
    (x x₁ : ℕ) :
  List.count x
      (List.replicate (x₁ / (highest_odd_factor x₁)) (highest_odd_factor x₁))
    =
  if highest_odd_factor x₁ = x then (x₁ / (highest_odd_factor x₁)) else 0 := by
  by_cases h : highest_odd_factor x₁ = x
  ·  -- the replicated element *is* `x`
    subst h                        -- rewrite with `x`
    simp [List.count_replicate]    -- `count x (replicate n x) = n`
  ·  -- the replicated element is *not* `x`
    have hne : highest_odd_factor x₁ ≠ x := h
    simp [List.count_replicate, hne]      -- the count is `0`

lemma sort_nodup_of_nodup {S : Multiset ℕ} (hS : S.Nodup) :
    (Multiset.sort (· ≤ ·) S).Nodup :=
--  (Multiset.sort_eq (s := S) (r := (· ≤ ·))).symm ▸ hS
  by
  have hM : (Multiset.ofList (Multiset.sort (· ≤ ·) S)).Nodup := by
    simpa only [Multiset.sort_eq (s := S) (r := (· ≤ ·))] using hS
  exact hM

lemma parts_pos_non_zero {n : ℕ} (p1 : n.Partition) : ∀ x ∈ p1.parts, x ≠ 0 := λ x hx => Nat.ne_zero_of_lt (p1.parts_pos hx)

lemma parts_pos_hof_non_zero {n : ℕ} (p1 : n.Partition) : ∀ x ∈ p1.parts, highest_odd_factor x ≠ 0 := by
  intro x hx
  exact hof_zero_iff_n_zero.not.1 (parts_pos_non_zero p1 x hx)

lemma binary_c_rw
  {n x k a c : ℕ} {p1 : n.Partition}
  (hp  : p1 ∈ distincts n)
  (hk  : x * 2 ^ k = a)
  (hB : B = p1.parts.bind (fun y ↦ ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y))))
  (hc : c = Multiset.count x B):
  2 ^ k ∈ binary c ↔ (k ∈ List.map log2 (Multiset.sort (fun x1 x2 => x1 ≤ x2) (Multiset.map (fun x => x / highest_odd_factor x) (Multiset.filter (fun y => highest_odd_factor y = x) p1.parts)))):= by
  simp [hc, hB, Multiset.count_bind, binary, count_replicate_hof_actual]
--
--can get rid of m0 mexp m1 and maybe use a big calc
--
  set m0 := Multiset.map (fun y : ℕ => if highest_odd_factor y = x then (y / highest_odd_factor y) else 0) p1.parts
  set m1 := Multiset.map (fun y : ℕ => (y / highest_odd_factor y)) (Multiset.filter (fun y => highest_odd_factor y = x) p1.parts)
  have: m0.sum = m1.sum:= by
    have h_split : m0 = m1 + (Multiset.filter (fun z : ℕ => z = 0) m0) := by
      ext z
      by_cases h0 : z = 0
      · simp [m0, m1, h0, Multiset.mem_map, Multiset.mem_filter]
        intro x hx heq
        constructor
        exact parts_pos_hof_non_zero p1 x hx
        exact hof_le_n (n:=x)
      · simp[m0,m1,h0,Multiset.count_map]
        apply congrArg
        apply Multiset.filter_congr
        intro x1 hx1
        by_cases h : highest_odd_factor x1 = x
        · simp[h]
        · simp[h,h0]
    rw [h_split]
    simp[Multiset.sum_eq_zero]
  simp [this]

  simp [distincts] at hp
  have filter_nodup: (Multiset.filter (fun y => highest_odd_factor y = x) p1.parts).Nodup := by
    apply Multiset.Nodup.filter
    exact hp

  simp [m1]
  set S  : Multiset ℕ  :=  Multiset.map (fun x ↦ x / highest_odd_factor x)
    (Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts)
  -- set T := (Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts) with hT
  have hS: S.Nodup := by
    have mem_Filter: ∀ {y : ℕ}, y ∈ (Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts)
      → highest_odd_factor y = x :=by
      intro y hy
      simp [Multiset.mem_filter.1] at hy
      exact hy.2
    have q_inj_on_filter
      (a b : ℕ)
      (ha : a ∈ (Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts))
      (hb : b ∈ (Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts))
      (heq : a / highest_odd_factor a = b / highest_odd_factor b) :
    a = b := by
      obtain ⟨ka, hka⟩ := hof_divid_n_2tosomepow (parts_pos_non_zero p1 a (Multiset.mem_of_mem_filter ha))
      obtain ⟨kb, hkb⟩ := hof_divid_n_2tosomepow (parts_pos_non_zero p1 b (Multiset.mem_of_mem_filter hb))
      simp [←hka, ←hkb] at heq
      calc
        a = highest_odd_factor a * (a / highest_odd_factor a) :=
          (Nat.mul_div_cancel' (hof_divides (n := a))).symm
        _ = highest_odd_factor a * 2 ^ ka :=
          congrArg (fun t => highest_odd_factor a * t) hka.symm
        _ = highest_odd_factor b * 2 ^ ka :=
          congrArg (fun t => t * 2 ^ ka) (by simp [mem_Filter ha, mem_Filter hb])
        _ = highest_odd_factor b * 2 ^ kb := by
          simp [heq]
        _ = highest_odd_factor b * (b / highest_odd_factor b) := by
          simp [hkb]
        _ = b :=
          Nat.mul_div_cancel' (hof_divides (n := b))
    apply filter_nodup.map_on
    intro x hx y hy hxy
    exact q_inj_on_filter x y hx hy hxy

  let L : List ℕ := S.sort (· ≤ ·)
  have L_sorted_le : L.Sorted (· ≤ ·) := by simpa [L] using Multiset.sorted_sort (S := S) (r := (· ≤ ·))
--
--sort_nodup_of_nodup can be simplified as a lemma maybe it can't
--
  have LNodup : L.Nodup := (sort_nodup_of_nodup hS)
  have L_sorted_lt : L.Sorted (· < ·) := List.Sorted.lt_of_le L_sorted_le (sort_nodup_of_nodup hS)
  let idx : List ℕ := (L.map log2)
  have idx_sorted : (L.map (log 2)).Sorted (· < ·) := by
    have idx.Sorted :(L.map (log 2)).Sorted (· ≤ ·) := by
      apply L_sorted_le.map
      exact Nat.log_monotone
    have idx.Nodup : (L.map (log 2)).Nodup := by
      apply LNodup.map_on
      intro a ha b hb hab
      simp [L,S] at ha hb
      rcases ha with ⟨sa, hsa, rfl⟩
      rcases hb with ⟨sb, hsb, rfl⟩
      rcases hof_divid_n_2tosomepow (parts_pos_non_zero p1 sa hsa.1) with ⟨ka, hka⟩
      rcases hof_divid_n_2tosomepow (parts_pos_non_zero p1 sb hsb.1) with ⟨kb, hkb⟩
      simp [←hka, ←hkb, Nat.log_pow] at hab
      simp [←hka, ←hkb]
      exact hab
    apply List.Sorted.lt_of_le
    exact idx.Sorted
    exact idx.Nodup
  have map_pow_idx_eq_L : List.map (fun i : ℕ => 2 ^ i) (L.map (log 2)) = L := by
    simp [ List.map_map, Function.comp_def]
    have id: L = List.map (fun x => x) L := by
      simp [List.map_id]
    conv_rhs => rw [id]
    set f := (fun x => 2 ^ log 2 x)
    set g := (fun x => x)
    apply List.map_congr_left (f := (fun x => 2 ^ log 2 x)) (g := (fun x => x))
    intro a ha
    have h_pow2_L : ∀ b : ℕ, b ∈ L → ∃ k : ℕ, b = 2 ^ k := by
      simp [L]
      intro s hsS
      have: s ∈ Multiset.map (fun y : ℕ =>
              2 ^ Nat.log2 (y / highest_odd_factor y)) (Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts) := by
        simp [S] at hsS
        rcases hsS with ⟨a, ⟨ha,ha1⟩⟩
        simp
        use a
        constructor
        exact ha
        rcases hof_divid_n_2tosomepow (n := a) (hn_nonzero := (parts_pos_non_zero p1 a ha.1)) with ⟨k, hk⟩
        simp [←hk, ←ha1]
      simp at this
      rcases this with ⟨k, ⟨hkmem,hkhof⟩⟩
      rcases hof_divid_n_2tosomepow (n:=k) (hn_nonzero:=parts_pos_non_zero p1 k hkmem.1) with ⟨ka, hka⟩
      simp [←hka] at hkhof
      use ka
      exact hkhof.symm
    specialize h_pow2_L a ha
    rcases h_pow2_L with ⟨ka,hka⟩
    simp [hka, Nat.log_pow]

  have S_sum_bitIndices : S.sum.bitIndices = (L.map (log 2)) := by
    have hSum : (List.map (fun i : ℕ => 2 ^ i) (L.map (log 2))).sum = S.sum := by
      have : (List.map (fun i : ℕ => 2 ^ i) (L.map (log 2))).sum = L.sum := by
        simpa [map_pow_idx_eq_L] using rfl
      have hLS : L.sum = S.sum :=
        (Multiset.sum_coe (l := L)).symm.trans
          (congrArg (fun M : Multiset ℕ => M.sum)
            (show ((Multiset.sort (· ≤ ·) S : List ℕ) : Multiset ℕ) = S from
                Multiset.sort_eq (s := S) (r := (· ≤ ·))))
      simpa [hLS] using this
    have hBit := Nat.bitIndices_twoPowsum (L := (L.map (log 2))) (idx_sorted)
    simpa [←hSum] using hBit

  simp [S_sum_bitIndices]
  dsimp [L, S]
  simp only [Multiset.mem_sort]
  simp only [Multiset.mem_map]
  simp only [Multiset.mem_filter]
  simp only [exists_exists_and_eq_and]

  constructor

  intro h
  rcases h with ⟨y, hy, rfl⟩
  rcases hof_divid_n_2tosomepow (n:=y) (hn_nonzero:=parts_pos_non_zero p1 y hy.1) with ⟨ky, hky⟩
  simp [←hky, Nat.log_pow] at hk
  use y
  constructor
  exact hy
  simp [←hky, Nat.log_pow]

  intro h
  rcases h with ⟨y, hy, rfl⟩
  rcases hof_divid_n_2tosomepow (n:=y) (hn_nonzero:=parts_pos_non_zero p1 y hy.1) with ⟨ky, hky⟩
  use y
  constructor
  exact hy
  simp [←hky, Nat.log_pow]

lemma part_iff_bit3
    {n x k a c : ℕ} {p1 : n.Partition}
    (hp  : p1 ∈ distincts n)
    (hax : highest_odd_factor a = x)
    (hk  : x * 2 ^ k = a)
    (hB : B = p1.parts.bind (fun y ↦ ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y))))
    (hc : c = Multiset.count x B)
    :(a ∈ p1.parts ↔ (2 ^ k) ∈ binary c) := by
    simp [binary_c_rw (hp := hp) (hk := hk) (hB := hB ) (hc := hc)]
    constructor
    intro hamem
    use a
    have : a / highest_odd_factor a = 2 ^ k := by
      simp [←hax] at hk
      calc
        _ = (highest_odd_factor a * 2 ^ k) / highest_odd_factor a := by
          simp [hk]
        _  = 2 ^ k := by
          have hpos : 0 < highest_odd_factor a := Nat.pos_of_ne_zero (hof_zero_iff_n_zero.not.1 (parts_pos_non_zero p1 a hamem))
          simp [Nat.mul_comm (m := 2 ^ k), Nat.mul_div_left (H := hpos)]
    simp [this]
    exact ⟨hamem, hax⟩
    intro h
    rcases h with ⟨y, hy, rfl⟩
    rcases hof_divid_n_2tosomepow (n:=y) (hn_nonzero:=parts_pos_non_zero p1 y hy.1) with ⟨ky, hky⟩
    simp [←hky, Nat.log_pow] at hk
    have : a = y := by
      calc
      a = x * 2 ^ ky := by
        simpa using hk.symm
      _ = x * (y / x) := by
        have : y / x = 2 ^ ky := by
          simpa [hy.2] using hky.symm
        simpa [this]
      _ = y := by
        have hdiv : x ∣ y := by
          simpa [hy.2] using hof_divides (n := y)
        simp [Nat.mul_div_cancel' hdiv]
    rw[this]
    exact hy.1

lemma map_binary_eq_filter2 (p1 : Partition n) (hp: p1 ∈ distincts n) {x : ℕ}(B : Multiset ℕ) (hB:B = p1.parts.bind fun y ↦ List.replicate (y / highest_odd_factor y) (highest_odd_factor y))  (hx : x ∈ B.toFinset) :
  Multiset.map (fun y : ℕ => y * x) (binary (Multiset.count x B)) = Multiset.filter (fun y : ℕ => highest_odd_factor y = x) p1.parts := by
  have nodup_parts : p1.parts.Nodup := by simpa [distincts] using (Finset.mem_filter.1 hp).2
  ext a
  by_cases hax : highest_odd_factor a = x
  · rcases hof_mul_2tosomepow_eq_n (n:=a) with ⟨k, hk⟩
    simp [hax, Nat.mul_comm] at hk
    set c : ℕ := Multiset.count x B with hc
    calc
      _ = (if (2^k) ∈ binary c then 1 else 0) :=
        count_map_binary_eq_if (x:=x) (a:=a) (k:=k) (c:=c) (hxpos:=(pos_of_mem_B hB hx)) (hk:=hk.symm)
      _ = Multiset.count a (Multiset.filter (fun y => highest_odd_factor y = x) p1.parts) := by
        by_cases hmem : a ∈ Multiset.filter (fun y ↦ highest_odd_factor y = x) p1.parts
        · simp [(Multiset.count_eq_one_of_mem (s := Multiset.filter (fun y => highest_odd_factor y = x) p1.parts) (a := a)
               (Multiset.Nodup.filter (p := fun y => highest_odd_factor y = x) nodup_parts) hmem)]
          simp [(part_iff_bit3 (hp := hp) (hax := hax) (hk := hk) (hB := hB) (hc := hc)).1 ((Multiset.mem_filter.1 hmem).1)]
        · have anotmem: a ∉ p1.parts := fun ha => hmem (Multiset.mem_filter.2 ⟨ha, hax⟩)
          simp [Multiset.count_filter, hax, anotmem]
          simp [part_iff_bit3 (hp:=hp) (hax:=hax) (hk:=hk) (hB:=hB) (hc:=hc)] at anotmem
          exact anotmem
  · calc
      _ = 0 := by
        refine Multiset.count_eq_zero.mpr ?_
        intro hmem
        rcases Multiset.mem_map.1 hmem with ⟨w, hw, rfl⟩
        rcases mem_binary_is_power_of_two (x:=w) (n:= (Multiset.count x B)) hw with ⟨j, hj⟩
        have : highest_odd_factor (w * x) = x := by
          simp [hj, Nat.mul_comm, ← hof_same_undermul_2, ← hof_odd_eq_itself (hodd:=(odd_of_mem_B hB hx))]
        exact hax this
     0 = Multiset.count a (Multiset.filter (fun b ↦ highest_odd_factor b = x) p1.parts) := by
        symm
        refine Multiset.count_eq_zero.mpr ?_
        intro hmem
        exact hax ((Multiset.mem_filter.1 hmem).2)

lemma right_in3 (n : ℕ) (p1 : n.Partition) (hb : p1 ∈ distincts n) : FromOdd n (FromDis n p1 hb) (InOdd n p1 hb) = p1 := by
  unfold FromDis FromOdd FromOdd_parts FromDis_parts
  ext1
  simp only [Subtype.forall, Subtype.mk.injEq]
  set B : Multiset ℕ := p1.parts.bind (fun y => ↑(List.replicate (y / highest_odd_factor y) (highest_odd_factor y))) with hB
  symm
  calc
    p1.parts = ∑ x ∈ (B).toFinset, p1.parts.filter (fun y ↦ highest_odd_factor y = x) := by
      rw [sum_filters_by_key (S := B.toFinset) (g := highest_odd_factor) (M := p1.parts)]
      rw [(Multiset.filter_eq_self.2 (fun y hy => hof_mem (p1 := p1) (hB := hB) hy))]
    _ = ∑ x ∈ B.toFinset, Multiset.map (fun y => y * x) (binary (Multiset.count x B)) := by
      apply Finset.sum_congr
      rfl
      intro x hx
      simp[map_binary_eq_filter2 (n:=n) (p1:=p1) (hp:=hb) (x:=x) (B:=B) (hB:=hB) (hx:=hx)]

-- Euler's identity states that the number of odd partitions of `n` is equal to the number of distinct partitions of `n`.
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card :=
  card_bij' (FromOdd n) (FromDis n) (InDist n) (InOdd n) (left_inv n) (right_in3 n)
