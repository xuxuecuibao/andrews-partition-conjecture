import Mathlib.Data.Sym.Card
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanAndrews.GapBridge
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.OfFn

/-! A counting proof for the sorted weak compositions in Proposition 3.1. -/
open scoped BigOperators
namespace LeanAndrews.Sorting
open LeanAndrews.Lower

private theorem spaced_of_sorted {l : List Nat} {lo : Nat} (hh : ∀ a ∈ l, lo ≤ a)
    (h : l.Pairwise (· ≤ ·)) : Spaced 0 lo l := by
  induction l generalizing lo with
  | nil => trivial
  | cons a as ih =>
    refine ⟨hh a (by simp), ?_⟩
    exact ih (List.pairwise_cons.mp h).1 (List.pairwise_cons.mp h).2

private def freq {k L : Nat} (s : Sym (Fin k) L) : Fin k → Nat :=
  fun i => s.val.count i

private noncomputable def order {k L : Nat} (s : Sym (Fin k) L) := Tuple.sort (freq s)

private noncomputable def sorted {k L : Nat} (s : Sym (Fin k) L) :=
  List.ofFn (freq s ∘ order s)

private theorem sorted_spaced {k L : Nat} (s : Sym (Fin k) L) : Spaced 0 0 (sorted s) := by
  apply spaced_of_sorted (fun a _ => Nat.zero_le a)
  exact List.pairwise_ofFn.mpr (fun {_ _} hij => Tuple.monotone_sort (freq s) hij.le)

private theorem sorted_sum {k L : Nat} (s : Sym (Fin k) L) : (sorted s).sum = L := by
  unfold sorted
  rw [List.sum_ofFn]
  calc
    ∑ i, (freq s ∘ order s) i = ∑ i, freq s i := Equiv.sum_comp (order s) (freq s)
    _ = L := (Multiset.sum_count_eq_card (s := Finset.univ) (m := s.val)
      (fun _ _ => Finset.mem_univ _)).trans s.property

noncomputable def packed (g : Nat) {k L : Nat} (s : Sym (Fin k) L) :
    Gap g (L + k + triangle k*g) := by
  refine ⟨dress g 1 (sorted s), ?_, ?_⟩
  · exact (spaced_dress_iff g 1 0 _).2 (sorted_spaced s)
  · rw [sum_dress, sorted_sum]
    simp [sorted]

private theorem unpack_freq {k L g : Nat} {s t : Sym (Fin k) L}
    (ho : order s = order t) (he : packed g s = packed g t) : s = t := by
  have hs := congrArg (fun (a : Gap g (L + k + triangle k*g)) => undress g 1 a.val) he
  change undress g 1 (dress g 1 (sorted s)) = undress g 1 (dress g 1 (sorted t)) at hs
  simp only [undress_dress] at hs
  have hf := List.ofFn_injective (show List.ofFn _ = List.ofFn _ from hs)
  change freq s ∘ order s = freq t ∘ order t at hf
  rw [ho] at hf
  apply Subtype.ext
  apply Multiset.ext.mpr
  intro i
  have hc := congrFun hf ((order t).symm i)
  simpa [Function.comp_def, freq] using hc

/-- Version for any finite, injective encoding of genuine ascending gap partitions. -/
theorem stars_bound {j L g : Nat} {H : Type} [Fintype H]
    (encode : Gap g (L + (j+1) + triangle (j+1)*g) → H) (hinj : Function.Injective encode) :
    (L+j).choose j ≤ (j+1).factorial * Fintype.card H := by
  classical
  let f (s : Sym (Fin (j+1)) L) : Equiv.Perm (Fin (j+1)) × H :=
    (order s, encode (packed g s))
  have h : Function.Injective f := by
    intro s t hst
    exact unpack_freq (congrArg Prod.fst hst) (hinj (congrArg Prod.snd hst))
  have z := Fintype.card_le_of_injective f h
  rw [Sym.card_sym_eq_choose, Fintype.card_fin, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_fin] at z
  have e : j + 1 + L - 1 = L+j := by omega
  rw [e, ← Nat.choose_symm (show L ≤ L+j by omega)] at z
  simpa using z
/-- The sorted tuples are counted by the manuscript's enumerator of gap partitions. -/
theorem stars_hCount (L j g : Nat) :
    (L+j).choose j ≤ (j+1).factorial *
      Andrews.Small.hCount g (L+(j+1)+triangle (j+1)*g) := by
  classical
  let N := L+(j+1)+triangle (j+1)*g
  let S := (Andrews.Small.hParts g N).toFinset
  let encode (x : Gap g N) : ↥S :=
    ⟨x.val.reverse, List.mem_toFinset.mpr (GapBridge.gapToSmall_mem x)⟩
  have hi : Function.Injective encode := by
    intro a b e
    apply Subtype.ext
    have he := congrArg (fun u : ↥S => u.val.reverse) e
    simpa [encode] using he
  have h := stars_bound encode hi
  rw [Fintype.card_coe] at h
  exact h.trans (Nat.mul_le_mul_left _ (List.toFinset_card_le _))

theorem triangle_eq_choose (k : Nat) : triangle k = k.choose 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [triangle, ih, Nat.choose_succ_succ k 1, Nat.choose_one_right]
    exact Nat.add_comm _ _

end LeanAndrews.Sorting
