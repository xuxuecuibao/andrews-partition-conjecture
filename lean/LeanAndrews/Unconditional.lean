import LeanAndrews.Main
import LeanAndrews.FiniteHigh
import LeanAndrews.LowExact
import LeanAndrews.IntegerEuler

/-! A second finite proof dispenses with the pentagonal identity. A direct
partition recurrence verifies the beginning of the table. For the rest, a
certified integer upper bound on P already leaves more than the claimed
minimum. The exact minimum is attained in the directly verified portion. -/
namespace LeanAndrews.Unconditional
open Andrews.Small LeanAndrews.Finite

theorem bigEntry (m : Nat) (hl : bigClaim.first ≤ m) (hu : m ≤ bigClaim.last) :
    entryStatement bigClaim m (hCount 5 (4*m)) (UpperBridge.cumulative m) := by
  by_cases hd : m < 7000
  · exact LowExact.largeEntry m hl hd
  · have hlo : 7000 ≤ m := by omega
    have h := FiniteHigh.highMargin m hlo (show m < 65536 by exact Nat.lt_succ_of_le hu)
    have z := IntegerEuler.cumulative_le m (by omega)
    change UpperBridge.cumulative m + 22332733 ≤ hCount 5 (4*m) ∧
      (m=100 → UpperBridge.cumulative m + 22332733 = hCount 5 (4*m)) ∧
      (m<100 → UpperBridge.cumulative m + 22332733 < hCount 5 (4*m)) ∧
      (m ∈ ([] : List Nat) ↔ hCount 5 (4*m) = UpperBridge.cumulative m)
    simp only [List.not_mem_nil, false_iff]
    omega

theorem entries : FiniteConsequences.Entries where
  big := bigEntry
  medium := fun i lo hi => LowExact.mediumEntry i lo (Nat.lt_succ_of_le hi)
  small := LinkedFinite.smallEntry

theorem comparisons :
    Reduction.Comparisons qCount QCount hCount UpperBridge.cumulative where
  residue := fun _ _ _ hd hr => UpperBridge.upper_count hd hr
  scaling := fun _ _ _ _ he hed hm _ => GapBridge.scaling hed (by omega) hm
  analytic := largeComparison
  tableLarge := FiniteConsequences.large entries
  tableTen := FiniteConsequences.medium entries
  tableDirect := FiniteConsequences.direct entries
  small := CountBasics.small
  gapInclusion := fun d n _ => CountBasics.gapInclusion d n
  sixWeights := CountBasics.sixWeights

/-- Both the inequality and the exceptional values, with no external hypotheses. -/
theorem strengthened {d n : ℕ} (hd : 4 ≤ d) (hn : 1 ≤ n) :
    (n ≠ d+2 → QCount d n ≤ hCount (d+1) n) ∧
    (n = d+2 → hCount (d+1) n = 1 ∧ qCount d n = 2 ∧ QCount d n = 2) :=
  Reduction.strengthened_of_comparisons comparisons hd hn

/-- All d ≥ 4, including the exact equality set, without any literature premise. -/
theorem andrews_from_four {d n : ℕ} (hd : 4 ≤ d) (hn : 1 ≤ n) :
    QCount d n ≤ qCount d n ∧
    (qCount d n = QCount d n ↔ n ≤ d+3 ∨ (d=4 ∧ n=12)) :=
  Reduction.andrews_from_four comparisons hd hn

/-- For the full range, only Göllnitz–Gordon and Schur remain as inputs. -/
theorem andrews (I : ClassicalIdentities) {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    QCount d n ≤ qCount d n ∧
    (qCount d n = QCount d n ↔ d=2 ∨ d=3 ∨ n ≤ d+3 ∨ (d=4 ∧ n=12)) :=
  Reduction.andrews_of_comparisons comparisons I hd hn

#print axioms entries
#print axioms strengthened
#print axioms andrews_from_four
#print axioms andrews
end LeanAndrews.Unconditional
