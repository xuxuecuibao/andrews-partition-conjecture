import LeanAndrews.EulerBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The integral and series comparison for the logarithm of Euler's product. -/

open Real MeasureTheory Set

namespace LeanAndrews.EulerIntegral

private noncomputable def term (k : ℕ) (x : ℝ) : ℝ :=
  exp (-((k:ℝ)+1)*x) / ((k:ℝ)+1)

private theorem term_integral (k : ℕ) :
    ∫ x in Ioi (0:ℝ), term k x = 1/((k:ℝ)+1)^2 := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  simp only [term, integral_div, integral_exp_mul_Ioi (neg_lt_zero.mpr hk), mul_zero, exp_zero]
  rw [neg_div_neg_eq, div_div, ← sq]

private theorem term_sum {x : ℝ} (hx : 0 < x) :
    ∑' k : ℕ, term k x = -log (1-exp (-x)) := by
  have hlog := hasSum_pow_div_log_of_abs_lt_one (x := exp (-x))
    (by rw [abs_of_pos (exp_pos _)]; exact exp_lt_one_iff.mpr (neg_lt_zero.mpr hx))
  rw [← hlog.tsum_eq]
  congr 1
  funext k
  simp only [term, ← exp_nat_mul, Nat.cast_add, Nat.cast_one]
  congr 2; ring

/-- Evaluation of the improper integral of the logarithmic Euler kernel. -/
theorem logKernel_integral : (∫ x in Ioi (0:ℝ), -log (1-exp (-x))) = π^2/6 := by
  have hz : HasSum (fun k : ℕ => 1/((k:ℝ)+1)^2) (π^2/6) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hi (k : ℕ) : IntegrableOn (term k) (Ioi (0:ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (a := -((k:ℝ)+1)) (neg_lt_zero.mpr (by positivity)) 0).div_const _
  have hn (k : ℕ) (x : ℝ) : ‖term k x‖ = term k x := by
    apply Real.norm_of_nonneg
    dsimp [term]
    positivity
  have hh : Summable (fun k : ℕ => ∫ x in Ioi (0:ℝ), ‖term k x‖) := by
    simp_rw [hn, term_integral]
    exact hz.summable
  calc
    _ = ∫ x in Ioi (0:ℝ), ∑' k : ℕ, term k x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with x hx
      exact (term_sum hx).symm
    _ = ∑' k : ℕ, ∫ x in Ioi (0:ℝ), term k x := (integral_tsum_of_summable_integral_norm hi hh).symm
    _ = _ := by simp_rw [term_integral]; exact hz.tsum_eq

/-- The product-series mesh bound with the manuscript's integral on its right. -/
theorem logKernel_riemann_le {t : ℝ} (ht : 0 < t) :
    t * (∑' j : ℕ, -log (1-exp (-t*((j:ℝ)+1)))) ≤
      ∫ x in Ioi (0:ℝ), -log (1-exp (-x)) := by
  have hnon (j : ℕ) : 0 ≤ -log (1-exp (-t*((j:ℝ)+1))) := by
    have hex : exp (-t*((j:ℝ)+1)) < 1 := exp_lt_one_iff.mpr
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) (by positivity))
    exact neg_nonneg.mpr (log_nonpos (sub_pos.mpr hex).le (sub_le_self _ (exp_pos _).le))
  have hts := tsum_le_of_sum_range_le hnon (fun M => EulerBound.finite_logProduct_le M ht)
  rw [logKernel_integral, mul_comm, ← le_div_iff₀ ht]
  convert hts using 1; ring

end LeanAndrews.EulerIntegral
