import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The analytic comparison in Proposition 3.1. The final theorem accepts an
integer bound obtained by sorting compositions, and an Euler-product upper
bound for the cumulative partition count. These are explicit inputs. -/

namespace LeanAndrews.Analytic

open Real
open scoped Real

/-- The explicit real lower bound used for the entropy of the chosen length. -/
theorem log_fifteen_fourths : (13 / 10 : ℝ) < log (15 / 4) := by
  apply (lt_log_iff_exp_lt (by norm_num)).2
  have ha : exp (1 / 10) ≤ 10 / 9 := by
    have h := exp_bound_div_one_sub_of_interval (x := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have h1 : exp 1 ≤ 2719 / 1000 := by linarith [exp_one_lt_d9]
  calc
    exp (13 / 10) = exp 1 * exp (1 / 10) ^ 3 := by
      rw [show (13 / 10 : ℝ) = 1 + ((1 / 10 + 1 / 10) + 1 / 10) by norm_num,
        exp_add, exp_add, exp_add]
      ring
    _ ≤ (2719 / 1000) * (10 / 9) ^ 3 := by gcongr
    _ < 15 / 4 := by norm_num

theorem pi_sqrt_two_thirds : π * √(2 / 3) < 257 / 100 := by
  have hp : π < 31416 / 10000 := by linarith [pi_lt_d4]
  have hs : √(2 / 3 : ℝ) ≤ 817 / 1000 := by
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num),
      sqrt_nonneg (2 / 3 : ℝ)]
  calc
    π * √(2 / 3) ≤ (31416 / 10000) * (817 / 1000) := by gcongr
    _ < 257 / 100 := by norm_num

/-- The factorial estimate follows from the monotone normalized Stirling
sequence, without an asymptotic error or an assumption on factorials. -/
theorem log_factorial_bound (k : ℕ) (hk : 0 < k) :
    log k.factorial ≤ ((k : ℝ) + 1 / 2) * log k - k + 1 := by
  have form (n : ℕ) (hn : n ≠ 0) :
      log (Stirling.stirlingSeq n) =
      log n.factorial - (1 / 2) * (log 2 + log n) - n * (log n - 1) := by
    rw [Stirling.log_stirlingSeq_formula,
      log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn),
      log_div (Nat.cast_ne_zero.mpr hn) (exp_pos 1).ne', log_exp]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le j)
  change log (Stirling.stirlingSeq j.succ) ≤ log (Stirling.stirlingSeq 1) at h
  rw [form _ (Nat.succ_ne_zero j), form 1 one_ne_zero] at h
  norm_num only [Nat.factorial_one, Nat.cast_one, log_one] at h
  linarith

/-- A global linear upper bound for the logarithmic remainder; this avoids
differentiating the final expression and is valid for real, not just integer, x. -/
theorem log_remainder (x : ℝ) (hx : 256 ≤ x) :
    log (4 * x ^ 2) ≤ 18 * (7 / 10) + 2 * (x / 256 - 1) := by
  have hpos : 0 < x / 256 := by linarith
  have ht := log_le_sub_one_of_pos hpos
  have h2 : log 2 ≤ 7 / 10 := by linarith [log_two_lt_d9]
  have hi : 4 * x ^ 2 = (2 : ℝ)^18 * (x / 256)^2 := by ring
  rw [hi, log_mul (by positivity) (by positivity), log_pow, log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The tail comparison after both partition functions have been bounded. -/
theorem tail_of_log_bounds (x logH logP : ℝ) (hx : 256 ≤ x)
    (hH : (4 * x / 5 - 1) * (2 + log (15 / 4)) - 2 - log (4 * x ^ 2) ≤ logH)
    (hP : logP ≤ π * √(2 / 3) * x) : logP < logH := by
  have hcoeff : 0 < 4 * x / 5 - 1 := by linarith
  have hl := mul_lt_mul_of_pos_left log_fifteen_fourths hcoeff
  have hu := mul_lt_mul_of_pos_right pi_sqrt_two_thirds (by linarith : 0 < x)
  linarith [log_remainder x hx]

/-- Integer length and residual weight of the selected staircase. -/
noncomputable def length (m : ℕ) : ℕ := ⌊4 * √(m : ℝ) / 5⌋₊
def residual (m k : ℕ) : ℕ := 4 * m - (k + 5 * k.choose 2)

/-- All parameter bounds, including the natural subtraction in the residual. -/
theorem staircase_parameters (m : ℕ) (hm : 65536 ≤ m) :
    256 ≤ √(m : ℝ) ∧ 0 < length m ∧
    4 * √(m : ℝ) / 5 - 1 ≤ (length m : ℝ) ∧
    0 < residual m (length m) ∧
    15 / 4 * (length m : ℝ) ^ 2 ≤ (residual m (length m) : ℝ) ∧
    (residual m (length m) : ℝ) ≤ 4 * (√(m : ℝ)) ^ 2 := by
  let k := length m
  have hx0 := sqrt_nonneg (m : ℝ)
  have hx2 := sq_sqrt (by positivity : 0 ≤ (m : ℝ))
  have hm' : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 256 ≤ √(m : ℝ) := by nlinarith
  have hku : (k : ℝ) ≤ 4 * √(m : ℝ) / 5 := Nat.floor_le (by positivity)
  have hkl : 4 * √(m : ℝ) / 5 < k + 1 := Nat.lt_floor_add_one _
  have hkp : 0 < (k : ℝ) := by linarith
  have hk : 0 < k := by exact_mod_cast hkp
  have hsq := sq_le_sq' (by linarith : -(4 * √(m : ℝ) / 5) ≤ k) hku
  have hshape : ((k + 5 * k.choose 2 : ℕ) : ℝ) =
      5 / 2 * (k : ℝ)^2 - 3 / 2 * k := by
    push_cast
    rw [Nat.cast_choose_two]
    ring
  have hfit' : ((k + 5 * k.choose 2 : ℕ) : ℝ) ≤ 4 * (m : ℝ) := by
    rw [hshape]
    nlinarith
  have hfit : k + 5 * k.choose 2 ≤ 4 * m := by exact_mod_cast hfit'
  have hL : (residual m k : ℝ) = 4 * (m : ℝ) - 5 / 2 * (k : ℝ)^2 + 3 / 2 * k := by
    rw [residual, Nat.cast_sub hfit, hshape]
    push_cast
    ring
  have hLpos : (0 : ℝ) < residual m k := by rw [hL]; nlinarith
  refine ⟨hx, hk, by linarith, by exact_mod_cast hLpos, ?_, ?_⟩
  · change 15 / 4 * (k : ℝ)^2 ≤ (residual m k : ℝ)
    rw [hL]
    nlinarith
  · change (residual m k : ℝ) ≤ 4 * (√(m : ℝ)) ^ 2
    rw [hx2]
    exact_mod_cast (Nat.sub_le (4 * m) (k + 5 * k.choose 2))

/-- The elementary binomial lower bound needed after sorting stars and bars. -/
theorem power_bound_of_stars {L k H : ℕ}
    (hstars : (L + (k - 1)).choose (k - 1) ≤ k.factorial * H) :
    L ^ (k - 1) ≤ (k - 1).factorial * k.factorial * H := by
  calc
    L ^ (k - 1) ≤ (L + 1) ^ (k - 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (L + 1).ascFactorial (k - 1) := Nat.pow_succ_le_ascFactorial _ _
    _ = (k - 1).factorial * (L + (k - 1)).choose (k - 1) :=
      Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ (k - 1).factorial * (k.factorial * H) := Nat.mul_le_mul_left _ hstars
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- Passing from the composition bound to the lower logarithmic envelope. -/
theorem lower_log_of_compositions {k L H : ℕ} (hk : 0 < k) (hL : 0 < L)
    (hc : L ^ (k - 1) ≤ (k - 1).factorial * k.factorial * H) :
    (k : ℝ) * (2 + log ((L : ℝ) / (k : ℝ)^2)) - 2 - log L ≤ log H := by
  have hH : 0 < H := by
    by_contra! h
    have hz : H = 0 := by omega
    rw [hz, Nat.mul_zero] at hc
    exact (Nat.not_lt_of_ge hc) (pow_pos hL _)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hH' : 0 < (H : ℝ) := by exact_mod_cast hH
  have hpred : (k - 1).succ = k := by omega
  have hf : (k - 1).factorial * k = k.factorial := by
    calc
      _ = (k - 1).succ.factorial := by rw [Nat.factorial_succ, show k - 1 + 1 = k by omega, Nat.mul_comm]
      _ = _ := by rw [hpred]
  have hfr : (((k - 1).factorial : ℕ) : ℝ) * k = k.factorial := by exact_mod_cast hf
  have hkfac := Nat.factorial_pos k
  have hfacpred := Nat.factorial_pos (k - 1)
  have hprev : log ((k - 1).factorial : ℝ) + log k = log k.factorial := by
    rw [← log_mul (by positivity) hk'.ne', hfr]
  have hc' : (L : ℝ) ^ (k - 1) ≤
       ((k - 1).factorial : ℝ) * (k.factorial : ℝ) * H := by exact_mod_cast hc
  have hlog := log_le_log (pow_pos hL' _) hc'
  rw [log_pow, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
    log_mul (by positivity) hH'.ne', log_mul (by positivity) (by positivity)] at hlog
  rw [log_div hL'.ne' (by positivity), log_pow]
  have hSt := log_factorial_bound k hk
  push_cast
  nlinarith

/-- Proposition 3.1 from its two counting inputs: the lower estimate by sorting
compositions and the Euler upper estimate for cumulative ordinary partitions. -/
theorem large_of_counting_bounds {m H P : ℕ} (hm : 65536 ≤ m)
    (hcount : (residual m (length m)) ^ (length m - 1) ≤
      (length m - 1).factorial * (length m).factorial * H)
    (hEuler : log P ≤ π * √(2 * (m : ℝ) / 3)) : P < H := by
  let k := length m
  let L := residual m k
  let x := √(m : ℝ)
  obtain ⟨hx, hk, hfloor, hL, hratio, hLmax⟩ := staircase_parameters m hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hHpos : 0 < H := by
    by_contra! h
    have hz : H = 0 := by omega
    rw [hz, Nat.mul_zero] at hcount
    exact (Nat.not_lt_of_ge hcount) (pow_pos hL _)
  by_cases hPpos : 0 < P
  swap
  · omega
  have hrat : (15 / 4 : ℝ) ≤ (L : ℝ) / (k : ℝ)^2 :=
    (le_div_iff₀ (by positivity)).2 hratio
  have hratlog := log_le_log (by norm_num : (0 : ℝ) < 15 / 4) hrat
  have hLlog : log L ≤ log (4 * x ^ 2) := log_le_log hL' hLmax
  have hh := lower_log_of_compositions hk hL hcount
  have hprod : (4 * x / 5 - 1) * (2 + log (15 / 4))
      ≤ (k : ℝ) * (2 + log ((L : ℝ) / (k : ℝ)^2)) := by
    exact mul_le_mul hfloor (by linarith) (by linarith [log_fifteen_fourths]) hk'.le
  have hup : log P ≤ π * √(2 / 3) * x := by
    have heq : √(2 * (m : ℝ) / 3) = √(2 / 3) * x := by
      rw [show 2 * (m : ℝ) / 3 = (2 / 3) * m by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    rw [heq, ← mul_assoc] at hEuler
    exact hEuler
  have hstrict := tail_of_log_bounds x (log H) (log P) hx (by linarith) hup
  have hhpos' : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hp' : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hreal : (P : ℝ) < H := (log_lt_log_iff hp' hhpos').1 hstrict
  exact_mod_cast hreal

/-- Form taking the direct output of the sorting map. -/
theorem large_of_sorting_euler {m H P : ℕ} (hm : 65536 ≤ m)
    (hstars : (residual m (length m) + (length m - 1)).choose (length m - 1)
      ≤ (length m).factorial * H)
    (hEuler : log P ≤ π * √(2 * (m : ℝ) / 3)) : P < H :=
  large_of_counting_bounds hm (power_bound_of_stars hstars) hEuler

end LeanAndrews.Analytic
