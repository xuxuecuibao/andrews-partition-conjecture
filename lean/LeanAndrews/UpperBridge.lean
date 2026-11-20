import LeanAndrews.Small
import LeanAndrews.Upper

/-! Lemma 2.1 for the literal descending-list counts used by the main theorem. -/

namespace LeanAndrews.UpperBridge

open Andrews.Small LeanAndrews.Upper

/-- Sum of the ordinary partition counts through weight `m`, including zero. -/
def cumulative (m : Nat) : Nat :=
  ((List.range (m+1)).map (fun w => (partitions w).length)).sum

/-- Translate the actual modular test used by `QCount` to a unique indexed part. -/
theorem indexed_of_allowed {d x : Nat} (hd : 4 ≤ d) (hx : 1 < x)
    (ha : allowed d x = true) : ∃ i, x = residuePart d i := by
  let j := x / (4*d)
  have hw : 4*j*d + x % (4*d) = x := by
    dsimp [j]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.div_add_mod x (4*d))
  obtain ⟨h0,h1,h2,h3⟩ := residuePart_block d j hd
  simp only [allowed, Bool.or_eq_true, beq_iff_eq] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · cases hj : j with
    | zero => simp [hj, ha] at hw; omega
    | succ t =>
      refine ⟨4*t+3, ?_⟩
      rw [(residuePart_block d t hd).2.2.2]
      simp only [hj, Nat.mul_succ, Nat.add_mul, ha] at hw
      omega
  · exact ⟨4*j, by omega⟩
  · have hh := Nat.sub_add_cancel (show 2 ≤ 3*d by omega)
    exact ⟨4*j+1, by omega⟩
  · have hh := Nat.sub_add_cancel (show 1 ≤ 4*d by omega)
    exact ⟨4*j+2, by omega⟩

def strip (xs : List Nat) : List Nat := xs.filter (fun a => decide (1 < a))

theorem strip_weight (xs : List Nat) : (strip xs).sum ≤ xs.sum := by
  induction xs with
  | nil => simp [strip]
  | cons a xs ih =>
    by_cases h : 1 < a <;> simp [strip, h, List.filter_cons] at * <;> omega

theorem recover_list (xs : List Nat) (hp : ∀ a ∈ xs, 0 < a)
    (ho : xs.Pairwise (· ≥ ·)) :
    strip xs ++ List.replicate (xs.sum - (strip xs).sum) 1 = xs := by
  induction xs with
  | nil => simp [strip]
  | cons x xs ih =>
    have hx : 0 < x := hp x (by simp)
    have tail := ih (fun a ha => hp a (by simp [ha])) ho.of_cons
    by_cases hh : 1 < x
    · simpa [strip, hh, List.filter_cons, Nat.add_sub_add_left] using congrArg (x :: ·) tail
    · have he : x = 1 := by omega
      subst x
      have hnil : strip xs = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha
        have h := (List.pairwise_cons.mp ho).1 a ha
        simp
        omega
      change strip (1::xs) ++ _ = _
      have hs : strip (1::xs) = [] := by simpa [strip] using hnil
      rw [hs]
      rw [hnil] at tail
      simp at tail
      simp [Nat.add_comm, List.replicate_succ, tail]

def code (d : Nat) (xs : List Nat) := (strip xs).map (· / d)

theorem on_source {d n : Nat} {xs : List Nat} (hd : 4 ≤ d)
    (hx : xs ∈ QParts d n) :
    IsPartition n xs ∧ ∀ a ∈ strip xs, ∃ i, a = residuePart d i := by
  obtain ⟨ph, hh⟩ := List.mem_filter.mp hx
  refine ⟨mem_partitions.mp ph, ?_⟩
  intro a ha
  obtain ⟨hm, hn⟩ := List.mem_filter.mp ha
  exact indexed_of_allowed hd (of_decide_eq_true hn) (List.all_eq_true.mp hh a hm)

theorem code_injective_on {d n : Nat} (hd : 4 ≤ d) {xs ys : List Nat}
    (hx : xs ∈ QParts d n) (hy : ys ∈ QParts d n) (he : code d xs = code d ys) : xs = ys := by
  obtain ⟨px, ax⟩ := on_source hd hx
  obtain ⟨py, ay⟩ := on_source hd hy
  have hn : strip xs = strip ys := by
    rw [← expand_mapped d hd (strip xs) ax, ← expand_mapped d hd (strip ys) ay]
    exact congrArg (expand d) he
  calc xs = strip xs ++ List.replicate (n - (strip xs).sum) 1 := by
              rw [← px.1]; exact (recover_list xs px.2.1 px.2.2).symm
       _ = strip ys ++ List.replicate (n - (strip ys).sum) 1 := by rw [hn]
       _ = ys := by rw [← py.1]; exact recover_list ys py.2.1 py.2.2

private theorem code_mem {d m r : Nat} (hd : 4 ≤ d) (hr : r < d) {xs : List Nat}
    (hx : xs ∈ QParts d (d*m+r)) :
    code d xs ∈ (List.range (m+1)).flatMap partitions := by
  obtain ⟨px, ax⟩ := on_source hd hx
  have upper : d * (code d xs).sum ≤ d*m+r :=
    Nat.le_trans (div_sum_le d (strip xs)) (by have := strip_weight xs; rw [px.1] at this; exact this)
  have hb : (code d xs).sum ≤ m := by
    apply Classical.byContradiction
    intro h
    have lower := Nat.mul_le_mul_left d (show m+1 ≤ (code d xs).sum by omega)
    rw [Nat.mul_succ] at lower
    omega
  apply List.mem_flatMap.mpr
  refine ⟨(code d xs).sum, List.mem_range.mpr (by omega), mem_partitions.mpr ⟨rfl, ?_, ?_⟩⟩
  · intro a ha
    obtain ⟨b, hm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, rfl⟩ := ax b hm
    rw [residuePart_div d i hd]; omega
  · exact (px.2.2.filter _).map _ (fun _ _ h => div_monotone (by omega : 0 < d) h)

theorem length_le_of_subset {α : Type} [DecidableEq α] {xs ys : List α}
    (hx : xs.Nodup) (hi : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hna, hxs⟩ := List.nodup_cons.mp hx
    have hay := hi (by simp : a ∈ a::xs)
    have hrest : xs ⊆ ys.erase a := by
      intro x hm
      have hne : x ≠ a := fun eq => hna (eq ▸ hm)
      exact (List.mem_erase_of_ne hne).2 (hi (by simp [hm]))
    have hd := ih hxs hrest
    rw [List.length_erase_of_mem hay] at hd
    have hypos : 0 < ys.length := by cases ys <;> simp_all
    simp; omega

/-- The manuscript's cardinal inequality for the shared, literal partition model. -/
theorem upper_count {d m r : Nat} (hd : 4 ≤ d) (hr : r < d) :
    QCount d (d*m+r) ≤ cumulative m := by
  let source := QParts d (d*m+r)
  have hn : source.Nodup := (partitions_nodup _).filter _
  have coded : (source.map (code d)).Nodup := by
    apply List.pairwise_map.mpr
    exact hn.imp_of_mem (fun hx hy h he => h (code_injective_on hd hx hy he))
  have hi : source.map (code d) ⊆ (List.range (m+1)).flatMap partitions := by
    intro xs hx
    obtain ⟨orig, hm, rfl⟩ := List.mem_map.mp hx
    exact code_mem hd hr hm
  have h := length_le_of_subset coded hi
  simpa [QCount, source, cumulative, List.length_flatMap] using h

end LeanAndrews.UpperBridge
