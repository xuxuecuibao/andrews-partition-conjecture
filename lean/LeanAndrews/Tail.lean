import LeanAndrews.Analytic
import LeanAndrews.EulerBound
import LeanAndrews.Sorting
import LeanAndrews.UpperBridge

namespace LeanAndrews.Tail
open Andrews.Small LeanAndrews.Analytic LeanAndrews.Sorting

private theorem power_comparison (m : ℕ) (hm : 65536 ≤ m) :
    (Analytic.residual m (length m)) ^ (length m - 1) ≤
      (length m - 1).factorial * (length m).factorial * hCount 5 (4*m) := by
  obtain ⟨_, hk, _, hL, _, _⟩ := staircase_parameters m hm
  apply power_bound_of_stars
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let L := Analytic.residual m (length m)
  have hs := stars_hCount L j 5
  have hsize : L + (j+1) + Lower.triangle (j+1)*5 = 4*m := by
    rw [triangle_eq_choose, Nat.mul_comm _ 5]
    dsimp [L, Analytic.residual]
    rw [hj] at hL ⊢
    unfold Analytic.residual at hL
    change 0 < 4*m - ((j+1) + 5*(j+1).choose 2) at hL
    change 4*m - ((j+1) + 5*(j+1).choose 2) + (j+1) + 5*(j+1).choose 2 = 4*m
    omega
  rw [hsize] at hs
  simpa only [L, hj, Nat.succ_sub_one] using hs

private theorem sum_cast (f : ℕ → ℕ) (N : ℕ) :
    (((List.range N).map f).sum : ℝ) =
      ∑ i ∈ Finset.range N, (f i : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.sum_range_succ, Nat.cast_add, Finset.sum_range_succ, ih]

/-- The tail implication for the genuine functions. FiniteEuler is discharged
for ordinary partitions in the companion FiniteEuler module. -/
theorem large_of_finiteEuler (m : ℕ) (hm : 65536 ≤ m)
    (he : ∀ t : ℝ, 0 < t → EulerBound.FiniteEuler (fun n => (partitions n).length) m t) :
    UpperBridge.cumulative m < hCount 5 (4*m) := by
  apply large_of_counting_bounds hm (power_comparison m hm)
  unfold UpperBridge.cumulative
  rw [sum_cast]
  exact EulerBound.cumulative_log_le _ _ (by omega) he

end LeanAndrews.Tail
