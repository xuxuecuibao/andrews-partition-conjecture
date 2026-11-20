import LeanAndrews.Finite
import LeanAndrews.Reduction
import LeanAndrews.UpperBridge

namespace LeanAndrews.FiniteConsequences
open LeanAndrews.Finite LeanAndrews.Reduction LeanAndrews.UpperBridge Andrews.Small

structure Entries : Prop where
  big : ∀ i, bigClaim.first ≤ i → i ≤ bigClaim.last →
    entryStatement bigClaim i (hCount 5 (4*i)) (cumulative i)
  medium : ∀ i, mediumClaim.first ≤ i → i ≤ mediumClaim.last →
    entryStatement mediumClaim i (hCount 11 (10*i)) (cumulative i)
  small : ∀ d c, (d,c) ∈ smallClaims → ∀ i, c.first ≤ i → i ≤ c.last →
    entryStatement c i (hCount (d+1) i) (QCount d i)

theorem large (v : Entries) (m : Nat) (hl : 100 ≤ m) (hu : m < 65536) :
    cumulative m < hCount 5 (4*m) := by
  have h := (v.big m hl (show m ≤ 65535 by omega)).1
  change cumulative m + 22332733 ≤ _ at h
  omega

theorem medium (v : Entries) (m : Nat) (hl : 2 ≤ m) (hu : m < 100) :
    cumulative m < hCount 11 (10*m) := by
  have h := (v.medium m hl (show m ≤ 99 by omega)).1
  change cumulative m + 1 ≤ _ at h
  omega

private def directClaim (d : Nat) : Claim :=
  ⟨2*d, 100*d-1, (d-3)/2, 2*d, if d=4 then [8,10,12,16,17,18] else []⟩

private theorem direct_mem (d : Nat) (hl : 4 ≤ d) (hr : d ≤ 9) :
    (d, directClaim d) ∈ smallClaims := by
  have hd : d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 := by omega
  rcases hd with h|h|h|h|h|h <;> subst d <;> simp [smallClaims, directClaim]

theorem direct_of_small
    (rows : ∀ d c, (d,c) ∈ smallClaims → ∀ i, c.first ≤ i → i ≤ c.last →
      entryStatement c i (hCount (d+1) i) (QCount d i))
    (d n : Nat) (hl : 4 ≤ d) (hr : d ≤ 9)
    (low : 2*d ≤ n) (high : n < 100*d) :
    QCount d n ≤ hCount (d+1) n ∧
      (QCount d n = hCount (d+1) n → d=4 ∧ exceptional n) := by
  have h := rows d _ (direct_mem d hl hr) n low (show n ≤ 100*d-1 by omega)
  constructor
  · exact Nat.le_trans (Nat.le_add_right _ _) h.1
  · intro e
    have hz := h.2.2.2.mpr e.symm
    by_cases hd : d=4
    · exact ⟨hd, by simpa [directClaim,hd,exceptional] using hz⟩
    · simp [directClaim,hd] at hz

theorem direct (v : Entries) (d n : Nat) (hl : 4 ≤ d) (hr : d ≤ 9)
    (low : 2*d ≤ n) (high : n < 100*d) :
    QCount d n ≤ hCount (d+1) n ∧
      (QCount d n = hCount (d+1) n → d=4 ∧ exceptional n) :=
  direct_of_small v.small d n hl hr low high

end LeanAndrews.FiniteConsequences
