import LeanAndrews.Finite
import LeanAndrews.GapTable
import LeanAndrews.ResidueTable
import LeanAndrews.Pentagonal

namespace LeanAndrews.CertifiedRows
open Finite

def checkP (g s k : Nat) (c : Claim) : Bool :=
  checkRow c (GapTable.table g s c.last k) (Pentagonal.cumulative c.last)

def checkQ (r : Nat × Claim) : Bool :=
  let (d,c) := r
  let k := 24
  decide (c.last < (k+1) + (d+1)*(k+1)*k/2) &&
    checkRow c (GapTable.table (d+1) 1 c.last k) (ResidueTable.table d c.last)

theorem mediumPassed : checkP 11 10 15 mediumClaim = true := by native_decide
theorem smallPassed : smallClaims.all checkQ = true := by native_decide
theorem bigPassed : checkP 5 4 324 bigClaim = true := by native_decide

end LeanAndrews.CertifiedRows
