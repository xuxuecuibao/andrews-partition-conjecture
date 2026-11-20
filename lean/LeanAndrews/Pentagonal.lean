import LeanAndrews.UpperBridge

/-! A certified Euler-recurrence evaluator. The external statement concerns only
the ordinary combinatorial count and the two generalized pentagonal numbers.
The bounds, early stopping, cache invariants and prefix sums are proved here. -/

namespace LeanAndrews.Pentagonal

open Andrews.Small

def ordinary (n : Nat) : Nat := (partitions n).length

theorem ordinary_zero : ordinary 0 = 1 := by decide

/-- For `k=j+1`, these are `k(3k-1)/2` and `k(3k+1)/2`. -/
def first (j : Nat) := (j+1) * (3*j+2) / 2
def second (j : Nat) := first j + (j+1)

/-- Closed form of the second generalized pentagonal number. -/
theorem second_formula (j : Nat) : second j = (j+1)*(3*(j+1)+1)/2 := by
  have h : 3*(j+1)+1 = (3*j+2)+2 := by omega
  rw [h, Nat.mul_add, Nat.mul_comm (j+1) 2, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  rfl

private def shifted (p : Nat → Nat) (n a : Nat) : Int :=
  if a ≤ n then (p (n-a) : Int) else 0

def summand (p : Nat → Nat) (n j : Nat) : Int :=
  let both := shifted p n (first j) + shifted p n (second j)
  if j % 2 = 0 then both else -both

/-- The finite sum over j = start,...,start+terms-1 of the signed pair of
Euler terms. Terms with negative partition arguments are interpreted as zero. -/
def eulerSum (p : Nat → Nat) (n : Nat) : Nat → Nat → Int
  | _, 0 => 0
  | j, fuel+1 => summand p n j + eulerSum p n (j+1) fuel

/-- Classical external input: Euler's pentagonal recurrence for p(n).
This statement makes no reference to arrays, programs, or numerical checks. -/
def EulerRecurrence : Prop :=
  ∀ n : Nat, 0 < n → (ordinary n : Int) = eulerSum ordinary n 0 n

private theorem first_pos (j : Nat) : 0 < first j := by
  have h := Nat.mul_le_mul (show 1 ≤ j+1 by omega) (show 2 ≤ 3*j+2 by omega)
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by simpa using h)

private theorem first_mono (j : Nat) : first j ≤ first (j+1) := by
  apply Upper.div_monotone (by decide : 0 < 2)
  exact Nat.mul_le_mul (by omega) (by omega)

private theorem sum_zero_of_start {p : Nat → Nat} {n : Nat} (j fuel : Nat)
    (hn : n < first j) : eulerSum p n j fuel = 0 := by
  induction fuel generalizing j with
  | zero => rfl
  | succ k ih =>
    have h2 : n < second j := by unfold second; omega
    have hnext := Nat.lt_of_lt_of_le hn (first_mono j)
    simp [eulerSum, summand, shifted, Nat.not_le_of_gt hn, Nat.not_le_of_gt h2, ih _ hnext]

private theorem sum_congr {p q : Nat → Nat} {n : Nat} (j fuel : Nat)
    (h : ∀ i < n, p i = q i) : eulerSum p n j fuel = eulerSum q n j fuel := by
  induction fuel generalizing j with
  | zero => rfl
  | succ k ih =>
    have sh (a : Nat) (hpos : 0 < a) : shifted p n a = shifted q n a := by
      unfold shifted
      split
      · rw [h (n-a) (by omega)]
      · rfl
    have h₁ := sh (first j) (first_pos j)
    have h₂ := sh (second j) (by unfold second; omega)
    simp only [eulerSum, summand, h₁, h₂, ih]

/-- Short-circuit at the first pentagonal number exceeding n. The accumulator
keeps the recursion tail-recursive. -/
private def accumulate (p : Nat → Nat) (n : Nat) : Nat → Nat → Int → Int
  | _, 0, z => z
  | j, fuel+1, z =>
      if n < first j then z else
        accumulate p n (j+1) fuel (z + summand p n j)

private theorem accumulate_eq (p : Nat → Nat) (n j fuel : Nat) (z : Int) :
    accumulate p n j fuel z = z + eulerSum p n j fuel := by
  induction fuel generalizing j z with
  | zero => simp [accumulate, eulerSum]
  | succ k ih =>
    by_cases ht : n < first j
    · rw [sum_zero_of_start _ _ ht]
      simp [accumulate, ht]
    · simp [accumulate, ht, eulerSum, ih, Int.add_assoc]

private structure Cache where
  ordinary : Array Nat
  cumulative : Array Nat

private def initial : Cache := ⟨#[1], #[1]⟩

/-- At index `i`, append the two coefficients of weight `i+1`. -/
private def advance (c : Cache) (i : Nat) : Cache :=
  let next := (accumulate (fun j => c.ordinary[j]?.getD 0) (i+1) 0 (i+1) 0).toNat
  ⟨c.ordinary.push next, c.cumulative.push (c.cumulative[i]?.getD 0 + next)⟩

private def run (N : Nat) : Cache :=
  (List.range N).foldl advance initial

def cumulative (N : Nat) : Array Nat := (run N).cumulative

private theorem run_succ (n : Nat) : run (n+1) = advance (run n) n := by
  simp [run, List.range_succ, List.foldl_append]

private theorem prefix_zero : UpperBridge.cumulative 0 = 1 := by decide

private theorem sum_snoc (xs : List Nat) (x : Nat) :
    (xs ++ [x]).sum = xs.sum + x := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Nat.add_assoc]

private theorem prefix_succ (n : Nat) :
    UpperBridge.cumulative (n+1) = UpperBridge.cumulative n + ordinary (n+1) := by
  unfold UpperBridge.cumulative ordinary
  rw [List.range_succ (n := n+1), List.map_append]
  exact sum_snoc _ _

private theorem run_sizes (n : Nat) :
    (run n).ordinary.size = n+1 ∧ (run n).cumulative.size = n+1 := by
  induction n with
  | zero => decide
  | succ n ih => simp [run_succ, advance, ih.1, ih.2]

theorem cumulative_size (N : Nat) : (cumulative N).size = N+1 :=
  (run_sizes N).2

private theorem cache_correct (H : EulerRecurrence) (N : Nat) :
    ∀ j, j ≤ N → (run N).ordinary[j]? = some (ordinary j) ∧
      (run N).cumulative[j]? = some (UpperBridge.cumulative j) := by
  induction N with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst j; decide
  | succ N ih =>
    let c := run N
    let f := fun (j : Nat) => c.ordinary[j]?.getD 0
    have hf (i : Nat) (hi : i < N+1) : f i = ordinary i := by
      simp [f, c, (ih i (by omega)).1]
    have hc : c.cumulative[N]?.getD 0 = UpperBridge.cumulative N := by
      simp [c, (ih N (by omega)).2]
    have value : (accumulate f (N+1) 0 (N+1) 0).toNat = ordinary (N+1) := by
      rw [accumulate_eq, Int.zero_add, sum_congr _ _ hf, ← H (N+1) (by omega)]
      simp
    obtain ⟨s1,s2⟩ := run_sizes N
    intro j hj
    rw [run_succ]
    change (c.ordinary.push _)[j]? = _ ∧ (c.cumulative.push _)[j]? = _
    change c.ordinary.size = N+1 at s1
    change c.cumulative.size = N+1 at s2
    by_cases he : j = N+1
    · subst j
      simp only [Array.getElem?_push, s1, s2, if_true]
      change some (accumulate f (N+1) 0 (N+1) 0).toNat = _ ∧
        some (c.cumulative[N]?.getD 0 + (accumulate f (N+1) 0 (N+1) 0).toNat) = _
      simp [value, hc, prefix_succ]
    · have hsmall : j ≤ N := by omega
      simpa only [Array.getElem?_push, s1, s2, if_neg he] using ih j hsmall

/-- Every array entry is the cumulative partition count, conditional only on
the stated classical Euler recurrence for ordinary partitions. -/
theorem cumulative_correct (H : EulerRecurrence) (N m : Nat) (hm : m ≤ N) :
    (cumulative N)[m]? = some (UpperBridge.cumulative m) :=
  (cache_correct H N m hm).2

end LeanAndrews.Pentagonal
