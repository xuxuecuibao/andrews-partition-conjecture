import LeanAndrews.CertifiedRows

namespace LeanAndrews.LinkedFinite
open Finite CertifiedRows

private theorem cumGet (H : Pentagonal.EulerRecurrence) (N i : Nat) (hi : i ≤ N) :
    (Pentagonal.cumulative N)[i]! = UpperBridge.cumulative i := by
  have hb : i < (Pentagonal.cumulative N).size := by rw [Pentagonal.cumulative_size]; omega
  have he := Pentagonal.cumulative_correct H N i hi
  rw [getElem?_pos (Pentagonal.cumulative N) i hb] at he
  exact (getElem!_pos (Pentagonal.cumulative N) i hb).trans (Option.some.inj he)

private theorem pEntry {g s k i : Nat} {c : Claim}
    (pass : checkP g s k c = true) (cut : s*c.last < CoinBridge.shift g (k+1))
    (H : Pentagonal.EulerRecurrence) (lo : c.first ≤ i) (hi : i ≤ c.last) :
    entryStatement c i (Andrews.Small.hCount g (s*i)) (UpperBridge.cumulative i) := by
  have h := (checkRow_sound (show checkRow c (GapTable.table g s c.last k)
    (Pentagonal.cumulative c.last) = true from pass)).2 i lo hi
  simpa only [GapTable.table_get g s c.last k i hi cut, cumGet H c.last i hi] using h

theorem bigEntry (H : Pentagonal.EulerRecurrence) (i : Nat)
    (lo : bigClaim.first ≤ i) (hi : i ≤ bigClaim.last) :
    entryStatement bigClaim i (Andrews.Small.hCount 5 (4*i)) (UpperBridge.cumulative i) := by
  apply pEntry bigPassed _ H lo hi
  rw [CoinBridge.shift_eq]
  decide

theorem mediumEntry (H : Pentagonal.EulerRecurrence) (i : Nat)
    (lo : mediumClaim.first ≤ i) (hi : i ≤ mediumClaim.last) :
    entryStatement mediumClaim i (Andrews.Small.hCount 11 (10*i)) (UpperBridge.cumulative i) := by
  apply pEntry mediumPassed _ H lo hi
  rw [CoinBridge.shift_eq]
  decide

theorem smallEntry (d : Nat) (c : Claim) (mem : (d,c) ∈ smallClaims) (i : Nat)
    (lo : c.first ≤ i) (hi : i ≤ c.last) :
    entryStatement c i (Andrews.Small.hCount (d+1) i) (Andrews.Small.QCount d i) := by
  have h := List.all_eq_true.mp smallPassed (d,c) mem
  simp only [checkQ, Bool.and_eq_true, decide_eq_true_eq] at h
  have he := (checkRow_sound h.2).2 i lo hi
  have cut : 1*c.last < CoinBridge.shift (d+1) (24+1) := by
    simpa [CoinBridge.shift_eq] using h.1
  simpa only [GapTable.table_get _ _ _ _ _ hi cut, Nat.one_mul,
    ResidueTable.table_get _ _ _ hi] using he

#print axioms bigEntry
#print axioms mediumEntry
#print axioms smallEntry

end LeanAndrews.LinkedFinite
