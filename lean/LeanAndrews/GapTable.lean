import LeanAndrews.VerifiedTable
import LeanAndrews.CoinBridge

namespace LeanAndrews.GapTable
open LeanAndrews.VerifiedTable LeanAndrews.CoinBridge

private def term (g n k : Nat) : Nat :=
  if shift g k ≤ n then restricted k (n-shift g k) else 0

private def total (g n k : Nat) := ((List.range k).map (term g n)).sum

private theorem sum_append_single (xs : List Nat) (x : Nat) : (xs ++ [x]).sum = xs.sum + x := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Nat.add_assoc]

private theorem total_succ (g n k : Nat) :
    total g n (k+1) = total g n k + term g n k := by
  simp [total, List.range_succ, sum_append_single]

/-- At stage k the first array tabulates partitions into parts at most k.
The second stores the sum over lengths 0 through k at weights s*i. -/
private def stages (g s N : Nat) : Nat → Array Nat × Array Nat
  | 0 => (base (s*N+1), row (N+1) fun i _ => if s*i = 0 then 1 else 0)
  | k+1 =>
    let (prev, sums) := stages g s N k
    let curr := addCoin (k+1) prev
    let offset := (k+1) + g*(k+1)*k/2
    let newSums := row (N+1) fun i _ =>
      let w := s*i
      sums[i]! + if offset ≤ w then curr[w-offset]! else 0
    (curr,newSums)

private theorem correct (g s N k : Nat) :
    (stages g s N k).1.size = s*N+1 ∧
    (stages g s N k).2.size = N+1 ∧
    Matches (stages g s N k).1 (restricted k) ∧
    Matches (stages g s N k).2 (fun i => total g (s*i) (k+1)) := by
  induction k with
  | zero =>
    refine ⟨base_size _, row_size _ _, ?_, ?_⟩
    · intro i hi
      simpa [restricted_zero] using base_matches (s*N+1) i hi
    · apply row_matches
      intro a _ _
      rw [total_succ]
      simp [total, term, shift, Lower.triangle, restricted_zero]
  | succ k ih =>
    obtain ⟨hp,hs,hp',hs'⟩ := ih
    have hcurr : Matches (addCoin (k+1) (stages g s N k).1) (restricted (k+1)) :=
      addCoin_matches (by omega) hp' (restricted_succ k)
    simp only [stages, addCoin_size, row_size, hp, true_and]
    refine ⟨hcurr,?_⟩
    apply row_matches
    intro a ha _
    rw [total_succ, hs' a.size (by omega)]
    have hoff : shift g (k+1) = k+1 + g*(k+1)*k/2 := by simp [shift_eq]
    simp only [term, hoff]
    by_cases h : k+1 + g*(k+1)*k/2 ≤ s*a.size
    · simp only [if_pos h]
      rw [hcurr _ (by
        rw [addCoin_size, hp]
        have := Nat.mul_le_mul_left s (Nat.le_of_lt_succ ha)
        omega)]
    · simp [h]

def table (g s N k : Nat) : Array Nat := (stages g s N k).2

@[simp] theorem table_size (g s N k : Nat) : (table g s N k).size = N+1 :=
  (correct g s N k).2.1

theorem table_get (g s N k i : Nat) (hi : i ≤ N) (cut : s*N < shift g (k+1)) :
    (table g s N k)[i]! = Andrews.Small.hCount g (s*i) := by
  rw [gapCount_eq_sum_cutoff g (s*i) (k+1)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left s hi) cut)]
  exact (correct g s N k).2.2.2 i (by rw [(correct g s N k).2.1]; omega)

end LeanAndrews.GapTable
