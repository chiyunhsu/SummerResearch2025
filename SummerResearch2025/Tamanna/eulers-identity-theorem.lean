import Mathlib
import Mathlib.Data.Multiset.Basic

structure partition{n:ℕ} where
  parts     : Multiset ℕ
  sums      : parts.sum = n
structure OP (n : ℕ) where
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

lemma binary2_sum_to_n(n:ℕ): (binary2 n).sum = n := by
 induction' n using Nat.strong_induction_on with n1 ih
 cases n1 with
 | zero => simp [binary2]
 | succ n =>
   let k := Nat.log2 (n + 1)
   let p := 2 ^ k
   have hp_le : p ≤ n + 1 := by
     dsimp[p]
     dsimp[k]
     rw[ Nat.log2_eq_log_two]
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
   rw[Nat.add_sub_cancel' hp_le]


  --use induction add one to the multiset
lemma binary_no_duplicate(n:ℕ): (binary2 n).Nodup:= by
  sorry
--natural number include 0 but we don't need natural number for
--partitions just positive integers need to fix later
lemma nd_time_const_nd(n:ℕ) (ms: Multiset ℕ)(hnd:ms.Nodup):
  (ms.map fun x ↦ x * n).Nodup:=by
  sorry
lemma finset_nsmul_eq_mul (s : Multiset ℕ) :
    ∑ x ∈ s.toFinset, (s.count x) * x =
    ∑ x ∈ s.toFinset, (s.count x) • x:= by
    simp[nsmul_eq_mul]

lemma count_sum (s : Multiset ℕ) :
    ∑ x ∈ s.toFinset, (s.count x) * x = s.sum:= by
    rw [finset_nsmul_eq_mul]
    rw[ ←Finset.sum_multiset_map_count]
    simp

def OddToDistinct (n : ℕ) : OP n → DistinctPartition n:= by
  intro h
  let dis_parts := (h.distinct_odd_parts).val.bind fun y ↦
      (binary2 (h.odd_parts.count y)).map fun z ↦ z * y
      -- oddpartition
      -- op:{1,3,3,3,5,5}
      -- dop:{1,3,5}
      -- 3 -> 3 * 3 -> 3* {2^1,2^0} ->{6,3}
      --5 ->...{10}
      --remember its the largest odd factor is different in terms of math
      --dop.map -> {},{},{}
      --dop.bind ->{a.b.,d,d,ae}
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

      dsimp[Multiset.Pairwise]
      constructor
      --tryin gto prove {3,6} and {5} are pairwise disjoint

      use h.distinct_odd_parts.toList
      apply Finset.nodup h.distinct_odd_parts
      simp

      -- constructor
      -- dsimp[List.Pairwise]

      --use (h.distinct_odd_parts.val).toList

  }
