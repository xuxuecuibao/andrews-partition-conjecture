import LeanAndrews.Tail
import LeanAndrews.CountBasics
import LeanAndrews.LinkedFinite
import LeanAndrews.FiniteConsequences
import LeanAndrews.FiniteEuler

/-! Main theorems for the genuine partition counts. All imported classical
partition identities used as external inputs are explicit hypotheses. -/
namespace LeanAndrews
open Andrews.Small

def ClassicalIdentities : Prop :=
  ∀ d n, (d = 2 ∨ d = 3) → 1 ≤ n → qCount d n = QCount d n

private theorem entries (E : Pentagonal.EulerRecurrence) : FiniteConsequences.Entries where
  big := LinkedFinite.bigEntry E
  medium := LinkedFinite.mediumEntry E
  small := LinkedFinite.smallEntry

theorem largeComparison (m : ℕ) (hm : 65536 ≤ m) :
    UpperBridge.cumulative m < hCount 5 (4*m) := by
  apply Tail.large_of_finiteEuler m hm
  exact fun t ht => FiniteEuler.actual_bound m ht

theorem comparisons (E : Pentagonal.EulerRecurrence) :
    Reduction.Comparisons qCount QCount hCount UpperBridge.cumulative where
  residue := fun _ _ _ hd hr => UpperBridge.upper_count hd hr
  scaling := fun _ _ _ _ he hed hm _ => GapBridge.scaling hed (by omega) hm
  analytic := largeComparison
  tableLarge := FiniteConsequences.large (entries E)
  tableTen := FiniteConsequences.medium (entries E)
  tableDirect := FiniteConsequences.direct (entries E)
  small := CountBasics.small
  gapInclusion := fun d n _ => CountBasics.gapInclusion d n
  sixWeights := CountBasics.sixWeights

/-- The strengthened gap inequality, including the exact forbidden weight. -/
theorem strengthened (E : Pentagonal.EulerRecurrence) {d n : ℕ}
    (hd : 4 ≤ d) (hn : 1 ≤ n) :
    (n ≠ d+2 → QCount d n ≤ hCount (d+1) n) ∧
    (n = d+2 → hCount (d+1) n = 1 ∧ qCount d n = 2 ∧ QCount d n = 2) :=
  Reduction.strengthened_of_comparisons (comparisons E) hd hn

/-- For d ≥ 4 neither of the two classical equality identities is needed. -/
theorem andrews_from_four (E : Pentagonal.EulerRecurrence)
    {d n : ℕ} (hd : 4 ≤ d) (hn : 1 ≤ n) :
    QCount d n ≤ qCount d n ∧
    (qCount d n = QCount d n ↔ n ≤ d+3 ∨ (d=4 ∧ n=12)) :=
  Reduction.andrews_from_four (comparisons E) hd hn

/-- Andrews's inequality and its exact equality set. -/
theorem andrews (E : Pentagonal.EulerRecurrence) (I : ClassicalIdentities)
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    QCount d n ≤ qCount d n ∧
    (qCount d n = QCount d n ↔ d=2 ∨ d=3 ∨ n ≤ d+3 ∨ (d=4 ∧ n=12)) :=
  Reduction.andrews_of_comparisons (comparisons E) I hd hn

#print axioms largeComparison
#print axioms strengthened
#print axioms andrews_from_four
#print axioms andrews
end LeanAndrews
