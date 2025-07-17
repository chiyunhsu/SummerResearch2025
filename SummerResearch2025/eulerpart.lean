import mathlib
import Mathlib.Data.Multiset.Basic
--todo:
--distinct to odd
--bijective map on finite sets give smae carindanity

lemma lt_div(a:ℕ)(b:ℕ)(c:ℕ)(h_le:a ≤ b)(h_lt_1: c > 1):(a / c) < b:=by
  sorry
@[simp]
def highest_odd_factor : ℕ → ℕ
| 0       => 0
| n@(k+1) =>
  if n % 2 = 1 then n
  else highest_odd_factor (n / 2)
termination_by n => n
decreasing_by
  simp_wf
  rename_i h1 h2
  rw[h1]
  let a := k+1
  have p: 2 > 1 := by
    simp
  have r: a≤ a :=by
    rfl
  exact lt_div
    (a:=a)
    (b:=a)
    (c:=2)
    (h_lt_1:= p)
    (h_le:=r)

--hof of ALL the image
  --they come from different odd numbers they haveto be different
  --to show distince look at intersection and get contradiviton

-- lemma distinct_hof (n1:ℕ)(hoodd1:n1%2 = 1)(n2:ℕ)(hoodd2:n2%2 = 1)
-- (hne:n1 ≠ n2): highest_odd_factor n1 ≠ highest_odd_factor n2:=by
--   unfold highest_odd_factor





#eval highest_odd_factor 16
#eval highest_odd_factor 8
structure partition{n:ℕ} where
  parts     : Multiset ℕ
  sums      : parts.sum = n
structure OP (n : ℕ) where--currently just type
--on implmentation partition is type, but OP is finset of type
  odd_parts           : Multiset ℕ
  sums                : odd_parts.sum = n
  odd                 : ∀ x ∈ odd_parts, x % 2 = 1
  distinct_odd_parts  : Finset ℕ
  dop_def             : distinct_odd_parts=odd_parts.toFinset
structure DistinctPartition (n : ℕ) where
  dis_parts       : Multiset ℕ
  sums            : dis_parts.sum = n
  dis             : dis_parts.Nodup
def binary2: ℕ → Multiset Nat
| 0 => 0
|(m+1)  =>
  let k := Nat.log2 (m+1)
  let p := 2 ^ k
  p ::ₘ binary2 ((m+1)-p)
#eval binary2 1023
#eval Nat.log2 1023
#eval 1023 - 2 ^ 9
lemma binary2_sum_to_n(n:ℕ): (binary2 n).sum = n := by
  induction' n using Nat.strong_induction_on with n1 ih
  cases n1 with
  | zero =>
    simp[binary2]
  | succ n =>
    let k := Nat.log2 (n + 1)
    let p := 2 ^ k
    have hp_le : p ≤ n + 1 := by
      dsimp[p,k]
      rw[Nat.log2_eq_log_two]
      have temp: n+1 ≠0:= by
        simp
      exact Nat.pow_log_le_self
        (b:=2)
        (x:= n+1)
        (hx:= temp)
    let m := n + 1 - p
    have h_m_lt: m < n + 1 := by
      apply Nat.sub_lt (Nat.succ_pos n)
      apply Nat.pow_pos
      exact Nat.zero_lt_two
    have ih_m := ih m h_m_lt
    unfold binary2
    simp only[Nat.add_sub_cancel' hp_le]
    simp only [Multiset.sum_cons, ih_m]
    rw[ih_m]
    rw [Nat.add_sub_cancel' hp_le]

#eval binary2 0
#eval Nat.log2 6
lemma binary_no_duplicate(n:ℕ): (binary2 n).Nodup:= by
  induction' n using Nat.strong_induction_on with n1 ih
  cases n1 with
  | zero => simp [binary2]
  | succ n =>
    let k := Nat.log2 (n + 1)
    let p := 2 ^ k
    have hp_le : p ≤ n + 1 := by
      dsimp[p,k]
      rw[Nat.log2_eq_log_two]
      have temp: n+1 ≠0:= by simp
      exact Nat.pow_log_le_self (b:=2) (x:= n+1) (hx:= temp)
    let m := n + 1 - p
    have h_m_lt: m < n + 1 := by
      apply Nat.sub_lt (Nat.succ_pos n)
      apply Nat.pow_pos
      exact Nat.zero_lt_two
    have ih_m := ih m h_m_lt
    unfold binary2
    simp only[Nat.add_sub_cancel' hp_le]
    apply Multiset.nodup_cons.2
    constructor
    · -- p ∉ binary2 m
      intro h_mem
<<<<<<< HEAD
      -- Powers of 2 in binary representation are unique
      have h_pow_unique : ∀ x ∈ binary2 m, x < p := by
        intro x hx
        -- Each element in binary2 m corresponds to a power of 2 less than p
        have h_bound : binary2 m = binary2 ((n + 1) - p) := by rfl
        -- Since m < n + 1 and p = 2^k where k = log2(n+1),
        -- all powers in binary2 m are < p
        sorry -- This requires more detailed analysis of binary representation
      exact lt_irrefl p ((h_pow_unique p h_mem))
    · exact ih_m

=======
      have h_pow_unique : ∀ x ∈ binary2 m, x < p := by
        intro x hx
        -- Each element in binary2 m corresponds
        -- to a power of 2 less than p
        have h_bound : binary2 m = binary2 ((n + 1) - p) := by rfl

        -- Since m < n + 1 and p = 2^k where k = log2(n+1),
        -- all powers in binary2 m are < p

        -- have x ≤ p:=by
        --   sorry
        -- by_contra!

        sorry -- This requires more detailed analysis of binary representation

      exact lt_irrefl p ((h_pow_unique p h_mem))
    · exact ih_m


  --   intro x hx
  --   -- Each element in binary2 m corresponds to a power of 2 less than p
  --   have h_bound : binary2 m = binary2 ((n + 1) - p) := by rfl
  --   -- Since m < n + 1 and p = 2^k where k = log2(n+1),
  --   -- all powers in binary2 m are < p
  --   sorry -- This requires more detailed analysis of binary representation
  -- exact lt_irrefl p ((h_pow_unique p h_mem))
--use induction add one to the multiset
lemma binary_no_duplicate(n:ℕ): (binary2 n).Nodup:= by
  induction n with
  | zero =>
      sorry
  | succ n ih =>
      let k := Nat.log2 (n + 1)
      let p := 2 ^ k
      let m := n + 1 - p
      simp[binary2]
      constructor
      ·have temp': p ≤ n + 1:=by
        dsimp[p,k]
        rw[ Nat.log2_eq_log_two]
        have temp: n+1 ≠0:=by
          simp
        exact Nat.pow_log_le_self
          (b:=2)
          (x:=n+1)
          (hx:=temp)
      rcases temp' with a | b



>>>>>>> 654c89d (during 7/17meeting)

--natural number include 0 but we don't need natural number for
--partitions just positive integers need to fix later
lemma nd_time_const_nd(n:ℕ) (ms: Multiset ℕ)(hnd:ms.Nodup):
  (ms.map fun x ↦ x * n).Nodup:=by
  sorry

<<<<<<< HEAD

=======
>>>>>>> 654c89d (during 7/17meeting)
lemma finset_nsmul_eq_mul (s : Multiset ℕ) :
    ∑ x ∈ s.toFinset, (s.count x) * x =
    ∑ x ∈ s.toFinset, (s.count x) • x:= by
    simp[nsmul_eq_mul]

lemma count_sum (s : Multiset ℕ) :
    ∑ x ∈ s.toFinset, (s.count x) * x = s.sum:= by
    rw [finset_nsmul_eq_mul]
    rw[ ←Finset.sum_multiset_map_count]
    simp
lemma fsnp_listnp(fs: Finset ℕ): fs.val.toList.Nodup := by
  sorry


def OddToDistinct (n : ℕ) : OP n → DistinctPartition n:= by
  intro h
  let dis_parts := (h.distinct_odd_parts).val.bind fun y ↦
      (binary2 (h.odd_parts.count y)).map fun z ↦ z * y
  refine{
    dis_parts := dis_parts
    sums      := by
      simp[dis_parts]
      simp[Multiset.sum_map_mul_right]
      simp[binary2_sum_to_n]
      simp[←h.sums]
      simp[←count_sum]
      rw[h.dop_def]
    dis       := by
      dsimp[dis_parts]
      apply Multiset.nodup_bind.2
      refine ⟨?all,?pairwise⟩
      intro a ain
      exact nd_time_const_nd
        (n:=a)
        (ms:=(binary2 (Multiset.count a h.odd_parts)))
        (hnd:= binary_no_duplicate (Multiset.count a h.odd_parts))
      --all's cases proof finished

      dsimp[Multiset.Pairwise]
      refine ⟨?a, ?b⟩
      use h.distinct_odd_parts.val.toList
      simp
      have aa: h.distinct_odd_parts.val.toList.Nodup:=by
        exact fsnp_listnp
          (fs:=h.distinct_odd_parts)

      let f : ℕ → Multiset ℕ :=
        fun y ↦ (binary2 (h.odd_parts.count y)).map (fun z ↦ z * y)

      apply(List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
        (l:= h.distinct_odd_parts.val.toList)
        (f:= f)
        (hn:= aa)
      ).1
      simp

      intro h1 h2 h3 h4 h5
      dsimp[Function.onFun]
      dsimp[Disjoint]
      --its not symmetric anymore, two images are divisible
      --by the different largest odd factor
      --need to have completly new different lemma
      --take the biggest odd factor of image of h1 and h3
      --if there exists a image not divisible by bof then im. disjoint
      --we canalways fnd existence of bof that suffice the above
      --condition because h1 != h3 -> h1 >h3 or h3 >h1
      --biggest odd factor will be
      --still break symmetry with the b.o.f. thought
      --the bigger one of h1 and h3 could still divide
      --both the b.o.f.

      --or we can look at for all elements in the smaller
      --of h1 and h3's image, it des not divide the bigger
      --not looking at divisibility but just all the
      --elements in the image having different bof
      have temp: ∀ x∈ f h1,
      highest_odd_factor x = highest_odd_factor h1:=by
        sorry
      have temp2: ∀ x∈ f h3,
      highest_odd_factor x = highest_odd_factor h3:=by
        sorry

      -- have a1(x: ℕ)(ms:Multiset ℕ)(hms:ms ≤ f h1):
      -- ∀ x ∈ ms, x % highest_odd_factor h1 = 0 ∧ x % h3 ≠ 0 :=by
      --   sorry
      -- have a2(x: ℕ)(ms:Multiset ℕ)(hms:ms ≤ f h3):
      -- ∀ x ∈ ms , x % h3 = 0 ∧ x % h1 ≠ 0:=by
      --   sorry
      -- -- intro c1 c2 c3

      -- by_contra! contr
      -- rcases contr with ⟨c1,c2 ,c3,c4⟩

      -- have b1: ∀ n ∈ c1, n % h1 = 0 ∧ n % h3 ≠ 0:=by
      --   exact a1
      --     (x:=n)
      --     (ms:=c1)
      --     (hms:=c2)
      -- have b2: ∀ n ∈ c1, n % h3 = 0 ∧ n % h1 ≠ 0:=by
      --   exact a2
      --     (x:=n)
      --     (ms:=c1)
      --     (hms:=c3)
      -- have b3: ∀ n∈ c1, n % h1 = 0 ∧ n % h1 ≠ 0 := by
      --   -- ∀ n ∈ c1 proof:
      --   intro a b
      --   exact ⟨(b1 a b).left , (b2 a b).right⟩
      --   --sorry
      -- intro hh1 hh2 hh3 at c4
      -- exact (b3 c4).1 (b3 a b).2


      -- have b4: (n % h1 ≠ 0) = ¬(n % h1 = 0) := by
      --   simp
      -- have b5: ∃ n∈ c1, n % h1 = 0 ∧ n % h1 ≠ 0:=by
      --   -- constructor
      --   sorry
      --tryin gto prove {3,6} and {5} are pairwise disjoint
      --remember its the largest odd factor is different
      --in terms of math
  }

  -- oddpartition
  -- op:{1,3,3,3,5,5}
  -- dop:{1,3,5}
  -- 3 -> 3 * 3 -> 3* {2^1,2^0} ->{6,3}
  --5 ->...{10}
  --hof of ALL the image
  --they come from different odd numbers they haveto be different
  --to show distince look at intersection and get contradiviton
  --remember its the largest odd factor is different in terms of math
  --dop.map -> {},{},{}
  --dop.bind ->{a.b.,d,d,ae}
