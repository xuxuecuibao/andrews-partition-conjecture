import Std

/-! The logical last section of the manuscript. The fields below are formal
proof obligations, not global axioms. This module alone proves no unconditional
partition inequality. Counts are abstract here so that every dependency is visible. -/
namespace LeanAndrews.Reduction

def exceptional (n : Nat) : Prop :=
  n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 16 ∨ n = 17 ∨ n = 18

structure Comparisons (q Q h : Nat → Nat → Nat) (P : Nat → Nat) : Prop where
  residue : ∀ d m r, 4 ≤ d → r < d → Q d (d*m+r) ≤ P m
  scaling : ∀ d e m r, 4 ≤ e → e ≤ d → 1 ≤ m → r < d →
    h (e+1) (e*m) ≤ h (d+1) (d*m+r)
  analytic : ∀ m, 65536 ≤ m → P m < h 5 (4*m)
  tableLarge : ∀ m, 100 ≤ m → m < 65536 → P m < h 5 (4*m)
  tableTen : ∀ m, 2 ≤ m → m < 100 → P m < h 11 (10*m)
  tableDirect : ∀ d n, 4 ≤ d → d ≤ 9 → 2*d ≤ n → n < 100*d →
    Q d n ≤ h (d+1) n ∧ (Q d n = h (d+1) n → d = 4 ∧ exceptional n)
  small : ∀ d n, 4 ≤ d → 1 ≤ n → n < 2*d →
    q d n = 1 + (n-d)/2 ∧ Q d n = 1 + (if d+2 ≤ n then 1 else 0) ∧
    h (d+1) n = 1 + (n-d-1)/2
  gapInclusion : ∀ d n, 4 ≤ d → h (d+1) n ≤ q d n
  sixWeights : ∀ n, exceptional n → (q 4 n = Q 4 n ↔ n = 12)

private theorem largeRange {q Q h P} (H : Comparisons q Q h P)
    {d n : Nat} (hd : 4 ≤ d) (hn : 2*d ≤ n) :
    Q d n ≤ h (d+1) n ∧ (Q d n = h (d+1) n → d = 4 ∧ exceptional n) := by
  let m := n / d
  let r := n % d
  have hd0 : 0 < d := by omega
  have hr : r < d := Nat.mod_lt n hd0
  have hn' : d*m+r = n := Nat.div_add_mod n d
  have hm : 2 ≤ m := (Nat.le_div_iff_mul_le hd0).2 hn
  have base (e : Nat) (he : 4 ≤ e) (hed : e ≤ d) (hb : P m < h (e+1) (e*m)) :
      Q d n < h (d+1) n := by
    rw [← hn']
    exact Nat.lt_of_le_of_lt (H.residue d m r hd hr)
      (Nat.lt_of_lt_of_le hb (H.scaling d e m r he hed (by omega) hr))
  have strict (x : Q d n < h (d+1) n) :
      Q d n ≤ h (d+1) n ∧ (Q d n = h (d+1) n → d = 4 ∧ exceptional n) :=
    ⟨Nat.le_of_lt x, fun e => False.elim (Nat.ne_of_lt x e)⟩
  by_cases hb : 100 ≤ m
  · apply strict
    apply base 4 (by decide) hd
    by_cases ht : 65536 ≤ m
    · exact H.analytic m ht
    · exact H.tableLarge m hb (by omega)
  · by_cases h10 : 10 ≤ d
    · exact strict (base 10 (by decide) h10 (H.tableTen m hm (by omega)))
    · have hm' : n / d < 100 := by change m < 100; omega
      exact H.tableDirect d n hd (by omega) hn ((Nat.div_lt_iff_lt_mul hd0).1 hm')

theorem strengthened_of_comparisons {q Q h P} (H : Comparisons q Q h P)
    {d n : Nat} (hd : 4 ≤ d) (hn : 1 ≤ n) :
    (n ≠ d+2 → Q d n ≤ h (d+1) n) ∧
    (n = d+2 → h (d+1) n = 1 ∧ q d n = 2 ∧ Q d n = 2) := by
  by_cases hs : n < 2*d
  · obtain ⟨a,b,c⟩ := H.small d n hd hn hs
    split at b <;> constructor <;> intro hh <;> omega
  · have z := (largeRange H hd (by omega : 2*d ≤ n)).1
    constructor
    · exact fun _ => z
    · intro e; omega

/-- The nonclassical case, including the full equality classification. -/
theorem andrews_from_four {q Q h P} (H : Comparisons q Q h P)
    {d n : Nat} (hd : 4 ≤ d) (hn : 1 ≤ n) :
    Q d n ≤ q d n ∧ (q d n = Q d n ↔ n ≤ d+3 ∨ (d = 4 ∧ n = 12)) := by
  by_cases hs : n < 2*d
  · obtain ⟨a,b,_⟩ := H.small d n hd hn hs
    split at b <;> constructor <;> omega
  · obtain ⟨hgap, heq⟩ := largeRange H hd (by omega : 2*d ≤ n)
    have hincl := H.gapInclusion d n hd
    refine ⟨Nat.le_trans hgap hincl, ?_⟩
    constructor
    · intro h
      obtain ⟨d4,hweights⟩ := heq (by omega)
      subst d
      exact Or.inr ⟨rfl, (H.sixWeights n hweights).1 h⟩
    · intro h
      have d4 : d = 4 := by omega
      have n12 : n = 12 := by omega
      subst d; subst n
      exact (H.sixWeights 12 (by simp [exceptional])).2 rfl

/-- The two classical identities are the historical external inputs. -/
theorem andrews_of_comparisons {q Q h P} (H : Comparisons q Q h P)
    (classicalEq : ∀ d n, (d = 2 ∨ d = 3) → 1 ≤ n → q d n = Q d n)
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    Q d n ≤ q d n ∧
    (q d n = Q d n ↔ d = 2 ∨ d = 3 ∨ n ≤ d+3 ∨ (d = 4 ∧ n = 12)) := by
  by_cases h4 : 4 ≤ d
  · obtain ⟨hle,heq⟩ := andrews_from_four H h4 hn
    exact ⟨hle, by constructor <;> intro h <;> omega⟩
  · have low : d = 2 ∨ d = 3 := by omega
    have e := classicalEq d n low hn
    constructor <;> omega
end LeanAndrews.Reduction
