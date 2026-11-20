import LeanAndrews.EulerBound
import LeanAndrews.CoinBridge
import LeanAndrews.UpperBridge

/-! A finite weighted Euler bound for the canonical partition lists. The proof
uses the bounded coin recurrence and never passes to an infinite Euler product. -/
namespace LeanAndrews.FiniteEuler
open LeanAndrews.CoinBridge
open Andrews.Small

private theorem gap_zero (xs : List Nat) (hp : xs.Pairwise (· ≥ ·)) : gapOK 0 xs = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hp
      have hab := hhead b (by simp)
      simp [gapOK, hab, ih htail]

private theorem all_partitions (n : Nat) : hCount 0 n = (partitions n).length := by
  unfold hCount hParts
  congr 1
  exact List.filter_eq_self.mpr (fun xs h => gap_zero xs (mem_partitions.mp h).2.2)

private theorem sum_append_nat (xs ys : List Nat) : (xs++ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih,Nat.add_assoc]

private theorem telescope (k n : Nat) :
    ((List.range (k+1)).map (fun j => if j ≤ n then restricted j (n-j) else 0)).sum
      = restricted k n := by
  induction k with
  | zero => simp [List.range_succ]
  | succ k ih =>
    rw [List.range_succ, List.map_append, sum_append_nat, ih]
    simpa using (restricted_succ k n).symm

theorem ordinary_restricted (n m : Nat) (hn : n ≤ m) :
    (partitions n).length = restricted m n := by
  rw [← all_partitions, gapCount_eq_sum_cutoff 0 n (m+1) (by simp [shift]; omega)]
  simpa [shift] using telescope m n
open Finset Real

private noncomputable def weighted (k m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range (m+1), (restricted k i : ℝ) * x^i

private theorem sum_shift (f : ℕ → ℝ) (a M : ℕ) :
    (∑ i ∈ range M, if a ≤ i then f (i-a) else 0) = ∑ i ∈ range (M-a), f i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ,ih]
    by_cases h : a ≤ M
    · rw [if_pos h, show M+1-a = (M-a)+1 by omega, sum_range_succ]
    · rw [if_neg h,show M-a=0 by omega,show M+1-a=0 by omega,add_zero]

/-- Removing one copy of the largest permitted part shifts the finite sum.
After truncation its contribution is at most x^(k+1) times the existing sum. -/
private theorem weighted_step (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    weighted (k+1) m x ≤ weighted k m x + x^(k+1)*weighted (k+1) m x := by
  let f := fun i : ℕ => (restricted (k+1) i : ℝ)*x^i
  have expand (i : ℕ) : (restricted (k+1) i : ℝ)*x^i =
      (restricted k i : ℝ)*x^i + x^(k+1)*(if k+1 ≤ i then f (i-(k+1)) else 0) := by
    rw [restricted_succ k i]
    by_cases h : k+1 ≤ i
    · simp only [if_pos h,Nat.cast_add,add_mul,f]
      congr 1
      have pow_split : x^i = x^(k+1)*x^(i-(k+1)) := by rw [← pow_add]; congr 1; omega
      rw [pow_split]
      ring
    · simp [h]
  calc
    weighted (k+1) m x = weighted k m x +
        x^(k+1)*(∑ i ∈ range (m+1), if k+1 ≤ i then f (i-(k+1)) else 0) := by
      unfold weighted
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => expand i)
    _ ≤ weighted k m x + x^(k+1)*weighted (k+1) m x := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx _)
      rw [sum_shift]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le ..))
      intro i _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)

private theorem product_bound (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hlt : x < 1) :
    weighted k m x ≤ ∏ j ∈ range k, (1-x^(j+1))⁻¹ := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero]
    apply le_of_eq
    calc
      weighted 0 m x = (restricted 0 0 : ℝ) * x^0 :=
        Finset.sum_eq_single 0
          (by intro b _ hb; simp [restricted_zero,hb])
          (by simp)
      _ = 1 := by simp [restricted_zero]
  | succ k ih =>
    rw [Finset.prod_range_succ,←div_eq_mul_inv]
    have hpos : 0 < 1-x^(k+1) := sub_pos.mpr (pow_lt_one₀ hx hlt (by omega))
    apply (le_div_iff₀ hpos).mpr
    linarith [weighted_step k m hx]

private theorem actual_formula (m : ℕ) {t : ℝ} (ht : 0<t) :
    ∑ i ∈ range (m+1), ((partitions i).length : ℝ)*exp (-t*i) ≤
    ∏ j ∈ range m, (1-exp (-t*(j+1)))⁻¹ := by
  have hp (i : ℕ) : exp (-t) ^ i = exp (-t*i) := by
    rw [← Real.exp_nat_mul, mul_comm]
  have hp' (j : ℕ) : exp (-t) ^ (j+1) = exp (-t*(j+1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hp (j+1)
  calc
    _ = weighted m m (exp (-t)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hp,ordinary_restricted i m (by have := Finset.mem_range.mp hi; omega)]
    _ ≤ _ := by
      simpa only [hp'] using product_bound m m (Real.exp_pos (-t)).le
        (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))

/-- The finite Euler coefficient bound for genuine ordinary partitions. -/
theorem actual_bound (m : ℕ) {t : ℝ} (ht : 0 < t) :
    EulerBound.FiniteEuler (fun n => (partitions n).length) m t :=
  actual_formula m ht

private theorem cast_range_sum (f : ℕ → ℕ) (M : ℕ) :
    (((List.range M).map f).sum : ℝ) = ∑ i ∈ range M, (f i : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ,List.map_append,sum_append_nat, Nat.cast_add,ih,Finset.sum_range_succ]
    simp

/-- The logarithmic majorant for the same cumulative count that appears
in the residue comparison and the finite verification. -/
theorem cumulative_log (m : ℕ) (hm : 0 < m) :
    log (UpperBridge.cumulative m : ℝ) ≤ π * √(2*(m:ℝ)/3) := by
  rw [UpperBridge.cumulative,cast_range_sum]
  exact EulerBound.cumulative_log_le _ m hm (fun _ ht => actual_bound m ht)

end LeanAndrews.FiniteEuler
