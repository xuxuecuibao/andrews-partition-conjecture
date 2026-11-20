import LeanAndrews.CountBasics

/-! Direct kernel checks of the explicit partitions in the final paragraph
of the proof. Permutation ignores enumeration order but preserves multiplicity. -/
namespace LeanAndrews.Witnesses

open Andrews.Small

theorem gap_list_at_twelve :
    (qParts 4 12).Perm [[12],[11,1],[10,2],[9,3]] := by decide

theorem residue_list_at_twelve :
    (QParts 4 12).Perm [List.replicate 12 1, 6 :: List.replicate 6 1,
      [6,6],[10,1,1]] := by decide

/-- Each listed partition has an allowed gap of exactly four. -/
theorem strict_witnesses :
    ([6,2] ∈ qParts 4 8 ∧ [6,2] ∉ hParts 5 8) ∧
    ([7,3] ∈ qParts 4 10 ∧ [7,3] ∉ hParts 5 10) ∧
    ([10,6] ∈ qParts 4 16 ∧ [10,6] ∉ hParts 5 16) ∧
    ([10,6,1] ∈ qParts 4 17 ∧ [10,6,1] ∉ hParts 5 17) ∧
    ([11,7] ∈ qParts 4 18 ∧ [11,7] ∉ hParts 5 18) := by decide

end LeanAndrews.Witnesses
