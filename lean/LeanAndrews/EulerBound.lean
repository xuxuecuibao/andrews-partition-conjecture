import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A finite logarithmic Euler-product bound. The finite Euler
coefficient inequality is exposed explicitly for an arbitrary sequence. -/

open Finset Real

namespace LeanAndrews.EulerBound

private theorem geometric_bound (M : ℕ) {a : ℝ} (ha : 0 < a) :
    ∑ j ∈ range M, (exp (-a)) ^ (j+1) ≤ 1 / a := by
  have he : 1 < exp a := (Real.one_lt_exp_iff).mpr ha
  have hlt : exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hseries := (hasSum_geometric_of_lt_one (Real.exp_pos (-a)).le hlt).mul_left (exp (-a))
  have hpartial := sum_le_hasSum (range M)
    (fun j _ => mul_nonneg (Real.exp_pos (-a)).le (pow_nonneg (Real.exp_pos (-a)).le j)) hseries
  calc
    ∑ j ∈ range M, (exp (-a)) ^ (j+1)
        ≤ exp (-a) * (1 - exp (-a))⁻¹ := by simpa only [pow_succ'] using hpartial
    _ = 1 / (exp a - 1) := by
      rw [Real.exp_neg]
      field_simp [ne_of_gt (Real.exp_pos a), ne_of_gt (sub_pos.mpr he)]
    _ ≤ 1 / a := one_div_le_one_div_of_le ha (by linarith [Real.add_one_le_exp a])

private theorem column_bound (M k : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ j ∈ range M, exp (-t * (j+1)) ^ (k+1) / (k+1) ≤
      (1 / ((k:ℝ)+1)^2) / t := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have swap (j : ℕ) : exp (-t * ((j:ℝ)+1)) ^ (k+1)
      = exp (-(t * ((k:ℝ)+1))) ^ (j+1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← Finset.sum_div]
  calc
    (∑ j ∈ range M, exp (-t * (j+1)) ^ (k+1)) / (k+1)
        = (∑ j ∈ range M, exp (-(t * (k+1))) ^ (j+1)) / (k+1) := by simp_rw [swap]
    _ ≤ (1/(t*(k+1))) / (k+1) := div_le_div_of_nonneg_right
      (geometric_bound M (mul_pos ht hk)) hk.le
    _ = _ := by field_simp [ht.ne', hk.ne']; ring

theorem finite_logProduct_le (M : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ j ∈ range M, -log (1-exp (-t*(j+1))) ≤ π^2/(6*t) := by
  have hlog (j : ℕ) := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := exp (-t*((j:ℝ)+1))) (by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) (by positivity)))
  have hsum := hasSum_sum (s := range M) (fun j _ => hlog j)
  have hz : HasSum (fun k : ℕ => 1 / ((k:ℝ)+1)^2) (π^2/6) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hbound := hasSum_le (fun k => column_bound M k ht) hsum (hz.div_const t)
  convert hbound using 1; ring

/-- Finite version of Euler's coefficient majorization at a positive parameter. -/
def FiniteEuler (p : ℕ → ℕ) (m : ℕ) (t : ℝ) : Prop :=
    ∑ i ∈ range (m+1), (p i : ℝ) * exp (-t*i) ≤
      ∏ j ∈ range m, (1-exp (-t*(j+1)))⁻¹

theorem cumulative_le (p : ℕ → ℕ) (m : ℕ) {t : ℝ} (ht : 0 < t) (hEuler : FiniteEuler p m t) :
    (∑ i ∈ range (m+1), (p i : ℝ)) ≤ exp (t*m + π^2/(6*t)) := by
  have hweight : (∑ i ∈ range (m+1), (p i : ℝ)) * exp (-t*m) ≤
      ∑ i ∈ range (m+1), (p i : ℝ) * exp (-t*i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hin : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hin) (neg_nonpos.mpr ht.le))
  have hfac (j : ℕ) : 0 < 1-exp (-t*((j:ℝ)+1)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) (by positivity)
  have heq : (∏ j ∈ range m, (1-exp (-t*(j+1)))⁻¹) =
      exp (∑ j ∈ range m, -log (1-exp (-t*(j+1)))) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [Real.exp_neg, Real.exp_log (hfac j)]
  have hcomb := (hweight.trans hEuler).trans (heq.le.trans (Real.exp_le_exp.mpr (finite_logProduct_le m ht)))
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv] at hcomb
  have hfinal := (div_le_iff₀ (Real.exp_pos (t*m))).mp hcomb
  simpa [Real.exp_add, mul_comm] using hfinal

/-- Choosing the saddle parameter gives the logarithmic form used in the
large-weight estimate. The only combinatorial premise is the explicitly
displayed finite Euler coefficient majorization. -/
theorem cumulative_log_le (p : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (hEuler : ∀ t : ℝ, 0 < t → FiniteEuler p m t) :
    log (∑ i ∈ range (m+1), (p i : ℝ)) ≤ π * √(2 * (m:ℝ) / 3) := by
  let x : ℝ := √(2 * (m:ℝ) / 3)
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hx : 0 < x := by dsimp [x]; positivity
  have hx2 : x^2 = 2*(m:ℝ)/3 := Real.sq_sqrt (by positivity)
  let t : ℝ := π/(3*x)
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := cumulative_le p m ht (hEuler t ht)
  have saddle : t*m + π^2/(6*t) = π*x := by
    calc
      t*m + π^2/(6*t) = π*((m:ℝ)/(3*x) + x/2) := by
        dsimp [t]
        field_simp [Real.pi_ne_zero, hx.ne']; ring
      _ = π*x := by
        congr 1
        field_simp [hx.ne']
        nlinarith [hx2]
  rw [saddle] at hb
  have hnon : 0 ≤ ∑ i ∈ range (m+1), (p i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  rcases hnon.eq_or_lt with ha | ha
  · rw [← ha, Real.log_zero]; exact (mul_pos Real.pi_pos hx).le
  · exact (Real.log_le_iff_le_exp ha).2 hb

end LeanAndrews.EulerBound
