import LeanAndrews.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! The explicit intermediate numerical estimates of Proposition 3.1, including
the three-term logarithm series comparison and the manuscript's derivative. -/

open Real
open scoped Real

namespace LeanAndrews.Analytic

theorem residual_lower_twelve_fifths {m : ℕ} (hm : 65536 ≤ m) :
    12 * (m : ℝ) / 5 ≤ residual m (length m) := by
  let k := length m
  have hp := (staircase_parameters m hm).2.2.2.1
  change 0 < 4 * m - (k + 5 * k.choose 2) at hp
  have hfit : k + 5 * k.choose 2 ≤ 4 * m := by omega
  have hx := sqrt_nonneg (m : ℝ)
  have hk : (k : ℝ) ≤ 4 * √(m : ℝ) / 5 := Nat.floor_le (by positivity)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hs := sq_le_sq' (by linarith : -(4 * √(m : ℝ) / 5) ≤ k) hk
  have hx2 := sq_sqrt (by positivity : 0 ≤ (m : ℝ))
  change 12 * (m : ℝ) / 5 ≤ ((4 * m - (k + 5 * k.choose 2) : ℕ) : ℝ)
  rw [Nat.cast_sub hfit]
  push_cast
  rw [Nat.cast_choose_two]
  nlinarith

/-- The manuscript uses the first three positive terms of the expansion at 11/19. -/
theorem log_fifteen_fourths_three_terms : (13/10 : ℝ) < log (15/4) := by
  have hs := hasSum_log_sub_log_of_abs_lt_one (x := (11/19 : ℝ)) (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/19)]; norm_num)
  have nonneg (j : ℕ) : 0 ≤ (2 : ℝ) * (1 / (2 * j + 1)) * (11 / 19 : ℝ) ^ (2*j+1) :=
    by positivity
  have ht := sum_le_hasSum (Finset.range 3) (fun j _ => nonneg j) hs
  rw [← log_div (by norm_num) (by norm_num)] at ht
  norm_num [Finset.sum_range_succ] at ht
  linarith

theorem log_two_four_terms : log 2 < 7 / 10 := by
  apply (log_lt_iff_lt_exp (by norm_num)).2
  have hs := sum_le_exp_of_nonneg (by norm_num : 0 ≤ (7 / 10 : ℝ)) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  linarith

noncomputable def tailRemainder (x : ℝ) :=
  7 * x / 100 - 53 / 10 - log (4 * x ^ 2)

theorem tailRemainder_at_256 : (1 / 50 : ℝ) < tailRemainder 256 := by
  rw [tailRemainder, show 4 * (256 : ℝ)^2 = 2^18 by norm_num, log_pow]
  push_cast
  linarith [log_two_four_terms]

theorem tailRemainder_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt tailRemainder (7 / 100 - 2 / x) x := by
  have hlin : HasDerivAt (fun y : ℝ => 7 * y / 100 - 53 / 10) (7 / 100) x := by
    simpa using ((((hasDerivAt_id x).const_mul (7 : ℝ)).div_const 100).sub_const (53 / 10))
  have hs : HasDerivAt (fun y : ℝ => 4 * y^2) (4*(2*x)) x := by
    simpa using (((hasDerivAt_id x).pow 2).const_mul (4 : ℝ))
  have hlog := hs.log (by positivity)
  convert hlin.sub hlog using 1
  field_simp [hx.ne']
  ring

theorem tailRemainder_deriv_pos {x : ℝ} (hx : 256 ≤ x) :
    deriv tailRemainder x = 7 / 100 - 2 / x ∧ 0 < deriv tailRemainder x := by
  have hpos : 0 < x := by linarith
  have hd := (tailRemainder_hasDerivAt x hpos).deriv
  refine ⟨hd, ?_⟩
  rw [hd, sub_pos, div_lt_iff₀ hpos]
  linarith

/-- The displayed lower bound for the logarithm of the ratio itself. -/
theorem tailRemainder_lt_log_ratio {x H P : ℝ} (hx : 256 ≤ x)
    (hHpos : 0 < H) (hPpos : 0 < P)
    (hH : (4*x/5-1) * (2 + log (15/4)) - 2 - log (4*x^2) ≤ log H)
    (hP : log P ≤ π * √(2 / 3) * x) : tailRemainder x < log (H / P) := by
  rw [tailRemainder, log_div hHpos.ne' hPpos.ne']
  have hl := mul_lt_mul_of_pos_left log_fifteen_fourths_three_terms
    (by linarith : 0 < 4*x/5-1)
  have hu := mul_lt_mul_of_pos_right pi_sqrt_two_thirds (by linarith : 0 < x)
  linarith


/-- The unit-interval trapezoid bound expressed using the antiderivative. -/
theorem log_unit_trapezoid_algebra {a : ℝ} (ha : 0 < a) :
    (log a + log (a+1))/2 ≤ (a+1)*log (a+1) - a*log a - 1 := by
  have h₀ := le_log_one_add_of_nonneg (inv_nonneg.mpr ha.le)
  have heq : log (1 + a⁻¹) = log (a+1) - log a := by
    rw [← log_div (by positivity) ha.ne']
    congr 1
    field_simp
  rw [heq] at h₀
  have hmult := mul_le_mul_of_nonneg_left h₀ (by positivity : (0:ℝ) ≤ a + 1/2)
  have one : (a + 1/2)*(2*a⁻¹/(a⁻¹+2))=1 := by
    field_simp [ha.ne', (by positivity : a⁻¹+2 ≠ 0)]
    ring
  rw [one] at hmult
  linarith

theorem log_unit_trapezoid {a : ℝ} (ha : 0 < a) :
    (log a + log (a+1))/2 ≤ ∫ s in a..a+1, log s := by
  rw [integral_log]
  linarith [log_unit_trapezoid_algebra ha]

/-- Summing the unit bounds inductively reproduces the factorial estimate. -/
theorem factorial_from_unit_trapezoids (k : ℕ) (hk : 1 ≤ k) :
    log k.factorial ≤ ((k : ℝ) + 1/2)*log k - k + 1 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs := log_unit_trapezoid_algebra hn'
    rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity)]
    push_cast
    linarith

end LeanAndrews.Analytic
