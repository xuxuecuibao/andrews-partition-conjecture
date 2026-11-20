import LeanAndrews.GapTable
import Mathlib.Data.Nat.Sqrt

namespace LeanAndrews.FiniteHigh

/-- The remaining finite weights are compared with an elementary integral
upper bound on the cumulative partition count. -/
private def check (a : Array Nat) : Bool :=
  (List.range (65536-7000)).all (fun j =>
    let m := 7000+j
    decide (2^(Nat.sqrt (14*m)+1) + 22332733 < a[m]!))

private theorem passed : check (GapTable.table 5 4 65535 324) = true := by native_decide

theorem highMargin (m : Nat) (hl : 7000 ≤ m) (hu : m < 65536) :
    2^(Nat.sqrt (14*m)+1) + 22332733 < Andrews.Small.hCount 5 (4*m) := by
  have h := List.all_eq_true.mp passed (m-7000) (List.mem_range.mpr (by omega))
  have hm : 7000+(m-7000)=m := by omega
  have cut : 4*65535 < CoinBridge.shift 5 (324+1) := by rw [CoinBridge.shift_eq]; decide
  change decide (2^(Nat.sqrt (14*(7000+(m-7000)))+1) + 22332733 <
    (GapTable.table 5 4 65535 324)[7000+(m-7000)]!) = true at h
  rw [hm, GapTable.table_get _ _ _ _ _ (by omega) cut] at h
  exact of_decide_eq_true h

theorem high (m : Nat) (hl : 7000 ≤ m) (hu : m < 65536) :
    2^(Nat.sqrt (14*m)+1) < Andrews.Small.hCount 5 (4*m) :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (highMargin m hl hu)

#print axioms high

end LeanAndrews.FiniteHigh
