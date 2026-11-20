import LeanAndrews.FiniteEuler
import LeanAndrews.Analytic

/-! A computable, integer-valued majorant for ordinary cumulative counts. -/

namespace LeanAndrews.IntegerEuler
open Real

theorem cumulative_le (m : ℕ) (hm : 0 < m) :
    UpperBridge.cumulative m ≤ 2^(Nat.sqrt (14*m)+1) := by
  have logTwo : (69/100 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
  have rootFourteen : (373/100 : ℝ) ≤ √14 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14),Real.sqrt_nonneg 14]
  have coefficient : π*√(2/3) ≤ √14 * log 2 := by
    calc
      _ ≤ 257/100 := Analytic.pi_sqrt_two_thirds.le
      _ ≤ (373/100 : ℝ)*(69/100) := by norm_num
      _ ≤ _ := mul_le_mul rootFourteen logTwo (by norm_num) (Real.sqrt_nonneg _)
  have upperRoot : √(14*(m:ℝ)) ≤ (Nat.sqrt (14*m) : ℝ) + 1 := by
    simpa using (Real.real_sqrt_lt_nat_sqrt_succ (a:=14*m)).le
  have exponent : π*√(2*(m:ℝ)/3) ≤ ((Nat.sqrt (14*m) : ℝ)+1)*log 2 := by
    calc
      _ = (π*√(2/3)) * √(m:ℝ) := by
        rw [show 2*(m:ℝ)/3 = (2/3)*m by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2/3)]
        ring
      _ ≤ (√14*log 2)*√(m:ℝ) := mul_le_mul_of_nonneg_right coefficient (Real.sqrt_nonneg _)
      _ = √(14*(m:ℝ))*log 2 := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 14)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right upperRoot (by linarith)
  by_cases hp : 0 < UpperBridge.cumulative m
  · have hp' : (0:ℝ) < UpperBridge.cumulative m := Nat.cast_pos.mpr hp
    have hl := (FiniteEuler.cumulative_log m hm).trans exponent
    have hpow : Real.log ((2:ℝ)^(Nat.sqrt (14*m)+1)) =
        ((Nat.sqrt (14*m) : ℝ)+1)*log 2 := by rw [Real.log_pow]; push_cast; rfl
    rw [← hpow] at hl
    have := (Real.log_le_log_iff hp' (by positivity)).1 hl
    exact_mod_cast this
  · exact (Nat.eq_zero_of_not_pos hp) ▸ Nat.zero_le _

end LeanAndrews.IntegerEuler
