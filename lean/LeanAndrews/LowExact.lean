import LeanAndrews.FiniteEuler
import LeanAndrews.GapTable
import LeanAndrews.Finite

/-! Exact finite comparisons without any pentagonal-number identity. The arrays
are the ordinary unlimited-coin dynamic program for parts 1,...,N followed by
a prefix sum. Every output coefficient is linked to the literal population. -/
namespace LeanAndrews.LowExact

open VerifiedTable

private def coinRows (N k : Nat) : Array Nat :=
  (List.range k).foldl (fun a j => addCoin (j+1) a) (base (N+1))

private theorem coinRows_succ (N k : Nat) :
    coinRows N (k+1) = addCoin (k+1) (coinRows N k) := by
  simp [coinRows, List.range_succ, List.foldl_append]

private theorem coins_correct (N k : Nat) :
    (coinRows N k).size = N+1 ∧ Matches (coinRows N k) (CoinBridge.restricted k) := by
  induction k with
  | zero =>
    change (base (N+1)).size = N+1 ∧ Matches (base (N+1)) (CoinBridge.restricted 0)
    exact ⟨base_size _, fun i hi => by simpa [CoinBridge.restricted_zero] using base_matches (N+1) i hi⟩
  | succ k ih =>
    rw [coinRows_succ]
    exact ⟨(addCoin_size _ _).trans ih.1,
      addCoin_matches (Nat.zero_lt_succ k) ih.2 (CoinBridge.restricted_succ k)⟩

/-- Exact cumulative ordinary partition counts for weights 0,...,N. -/
def table (N : Nat) : Array Nat :=
  let coeffs := coinRows N N
  row (N+1) fun i acc => coeffs[i]! + if i = 0 then 0 else acc[i-1]!

@[simp] theorem table_size (N : Nat) : (table N).size = N+1 := row_size _ _

private theorem sum_snoc (xs : List Nat) (x : Nat) : (xs ++ [x]).sum = xs.sum + x := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Nat.add_assoc]

private theorem cumulative_succ (n : Nat) :
    UpperBridge.cumulative (n+1) = UpperBridge.cumulative n + (Andrews.Small.partitions (n+1)).length := by
  unfold UpperBridge.cumulative
  rw [List.range_succ (n := n+1), List.map_append]
  exact sum_snoc _ _

theorem table_get (N i : Nat) (h : i ≤ N) : (table N)[i]! = UpperBridge.cumulative i := by
  have hc := coins_correct N N
  have hm : Matches (table N) UpperBridge.cumulative := by
    apply row_matches
    intro a ha hprev
    have hi : a.size ≤ N := by omega
    rw [hc.2 a.size (by omega), ←FiniteEuler.ordinary_restricted a.size N hi]
    by_cases hz : a.size = 0
    · rw [hz]
      change (Andrews.Small.partitions 0).length = UpperBridge.cumulative 0
      decide
    · simp only [if_neg hz]
      rw [hprev (a.size-1) (by omega)]
      have hrec := cumulative_succ (a.size-1)
      rw [show a.size-1+1=a.size by omega] at hrec
      omega
  exact hm i (by rw [table_size]; omega)

/-- The row predicate also certifies its minimum, first minimizer and zeros. -/
private def check (g s k : Nat) (c : Finite.Claim) : Bool :=
  Finite.checkRow c (GapTable.table g s c.last k) (table c.last)

private theorem from_check {g s k i : Nat} {c : Finite.Claim} (pass : check g s k c = true)
    (cut : s*c.last < CoinBridge.shift g (k+1)) (hl : c.first ≤ i) (hi : i ≤ c.last) :
    Finite.entryStatement c i (Andrews.Small.hCount g (s*i)) (UpperBridge.cumulative i) := by
  have ht := (Finite.checkRow_sound (show Finite.checkRow c
    (GapTable.table g s c.last k) (table c.last) = true from pass)).2 i hl hi
  simpa only [table_get c.last i hi, GapTable.table_get g s c.last k i hi cut] using ht

private def lowClaim : Finite.Claim := { Finite.bigClaim with last := 6999 }

private theorem mediumPassed : check 11 10 15 Finite.mediumClaim = true := by native_decide
private theorem lowPassed : check 5 4 107 lowClaim = true := by native_decide

theorem mediumEntry (m : Nat) (hl : 2 ≤ m) (hh : m < 100) :
    Finite.entryStatement Finite.mediumClaim m (Andrews.Small.hCount 11 (10*m))
      (UpperBridge.cumulative m) := by
  apply from_check mediumPassed _ hl (show m ≤ 99 by omega)
  rw [CoinBridge.shift_eq]; decide

theorem largeEntry (m : Nat) (hl : 100 ≤ m) (hh : m < 7000) :
    Finite.entryStatement Finite.bigClaim m (Andrews.Small.hCount 5 (4*m))
      (UpperBridge.cumulative m) := by
  apply from_check lowPassed _ hl (show m ≤ 6999 by omega)
  rw [CoinBridge.shift_eq]; decide

theorem medium (m : Nat) (hl : 2 ≤ m) (hh : m < 100) :
    UpperBridge.cumulative m < Andrews.Small.hCount 11 (10*m) := by
  have ht := (mediumEntry m hl hh).1
  change UpperBridge.cumulative m + 1 ≤ _ at ht
  omega

theorem large (m : Nat) (hl : 100 ≤ m) (hh : m < 7000) :
    UpperBridge.cumulative m < Andrews.Small.hCount 5 (4*m) := by
  have ht := (largeEntry m hl hh).1
  change UpperBridge.cumulative m + 22332733 ≤ _ at ht
  omega

#print axioms large
#print axioms medium
end LeanAndrews.LowExact
