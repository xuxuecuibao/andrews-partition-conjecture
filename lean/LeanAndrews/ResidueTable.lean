import LeanAndrews.ResidueRefine
import LeanAndrews.VerifiedTable

namespace LeanAndrews.ResidueTable
open LeanAndrews.VerifiedTable
open LeanAndrews.ResidueRefine
open Andrews.Small

/-- Coefficient rows after admitting the allowed parts at most cap. -/
def rows (d N : Nat) : (cap : Nat) → Array Nat
  | 0 => base (N+1)
  | k+1 =>
    let prev := rows d N k
    if allowed d (k+1) then addCoin (k+1) prev else prev

theorem rows_size (d N k : Nat) : (rows d N k).size = N+1 := by
  induction k with
  | zero => simp [rows]
  | succ k ih => by_cases h : allowed d (k+1) <;> simp [rows,h,ih]

theorem rows_matches (d N k : Nat) : Matches (rows d N k) (count d k) := by
  induction k with
  | zero =>
    intro i hi
    simpa [rows,count_zero] using (base_matches (N+1) i hi)
  | succ k ih =>
    by_cases h : allowed d (k+1)
    · simp only [rows,if_pos h]
      apply addCoin_matches (Nat.zero_lt_succ _) ih
      exact fun n => by simpa [h] using count_succ d k n
    · simp only [rows,if_neg h]
      intro i hi
      rw [count_succ]
      simpa [h] using ih i hi

def table (d N : Nat) : Array Nat := rows d N N

theorem table_size (d N : Nat) : (table d N).size = N+1 := rows_size d N N

theorem table_get (d N i : Nat) (hi : i ≤ N) : (table d N)[i]! = QCount d i :=
  (rows_matches d N N i (by rw [rows_size]; omega)).trans (count_eq_QCount d N i hi)

end LeanAndrews.ResidueTable
