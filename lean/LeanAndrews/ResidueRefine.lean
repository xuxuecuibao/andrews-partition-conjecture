import LeanAndrews.Small

/-! The ordinary coin-change recurrence for Andrews's residue-side count,
proved by sorting actual partitions according to their largest part. -/
namespace LeanAndrews.ResidueRefine
open Andrews.Small

/-- Residue partitions of weight n with all parts at most k. -/
def parts (d k n : Nat) : List (List Nat) :=
  (partitions n).filter fun xs => xs.all fun a => allowed d a && decide (a ≤ k)

def count (d k n : Nat) : Nat := (parts d k n).length

theorem mem_parts {d k n : Nat} {xs : List Nat} :
    xs ∈ parts d k n ↔ IsPartition n xs ∧ ∀ a ∈ xs, allowed d a = true ∧ a ≤ k := by
  simp [parts, List.all_eq_true, mem_partitions]

theorem parts_nodup (d k n : Nat) : (parts d k n).Nodup :=
  List.Pairwise.filter _ (partitions_nodup n)

private theorem member_le_sum {a : Nat} {xs : List Nat} (h : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => contradiction
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp
    · have := ih ht; simp only [List.sum_cons]; omega

theorem count_eq_QCount (d k n : Nat) (hk : n ≤ k) : count d k n = QCount d n := by
  apply same_length (parts_nodup ..) (List.Pairwise.filter _ (partitions_nodup n))
  intro xs
  simp only [mem_parts, QParts, List.mem_filter, mem_partitions, residueOK, List.all_eq_true]
  constructor
  · rintro ⟨hp, ha⟩
    exact ⟨hp, fun a h => (ha a h).1⟩
  · rintro ⟨hp, ha⟩
    exact ⟨hp, fun a h => ⟨ha a h, Nat.le_trans (hp.1 ▸ member_le_sum h) hk⟩⟩

theorem count_zero (d n : Nat) : count d 0 n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    rfl
  · have he : parts d 0 n = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro xs hx
      obtain ⟨hp,ha⟩ := mem_parts.mp hx
      cases xs with
      | nil => have := hp.1; simp_all [IsPartition]
      | cons b bs =>
        have hpos := hp.2.1 b (by simp)
        have hzero := (ha b (by simp)).2
        omega
    simp [count,he,hn]

private theorem include_iff {d k n : Nat} (ys : List Nat) :
    (k+1)::ys ∈ parts d (k+1) n ↔
    (allowed d (k+1) = true ∧ k+1 ≤ n) ∧ ys ∈ parts d (k+1) (n-(k+1)) := by
  simp only [mem_parts, IsPartition, List.sum_cons, List.forall_mem_cons, List.pairwise_cons]
  constructor
  · rintro ⟨⟨hw,⟨_,hp⟩,_,ho⟩, ⟨hak,_⟩,ha⟩
    exact ⟨⟨hak,by omega⟩, ⟨by omega,hp,ho⟩,ha⟩
  · rintro ⟨⟨hak,hn⟩, ⟨hw,hp,ho⟩,ha⟩
    refine ⟨⟨by omega, ⟨by omega,hp⟩, ?_,ho⟩, ⟨hak,Nat.le_refl _⟩,ha⟩
    exact fun a h => (ha a h).2

private def included (d k n : Nat) : List (List Nat) :=
  if allowed d (k+1) = true ∧ k+1 ≤ n then
    (parts d (k+1) (n-(k+1))).map (List.cons (k+1))
  else []

private theorem mem_included {d k n : Nat} {xs : List Nat} :
    xs ∈ included d k n ↔ ∃ ys, xs = (k+1) :: ys ∧ xs ∈ parts d (k+1) n := by
  constructor
  · intro h
    unfold included at h
    split at h
    next ha =>
      obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp h
      exact ⟨ys,rfl,(include_iff ys).mpr ⟨ha,hy⟩⟩
    next _ => contradiction
  · rintro ⟨ys,rfl,hp⟩
    obtain ⟨ha,hy⟩ := (include_iff ys).mp hp
    simp [included,ha,hy]

private theorem includes_nodup (d k n : Nat) : (included d k n).Nodup := by
  unfold included
  split
  · apply List.pairwise_map.mpr
    exact (parts_nodup ..).imp (by intro a b hab heq; exact hab (List.cons.inj heq).2)
  · simp

theorem count_succ (d k n : Nat) : count d (k+1) n = count d k n +
    (if allowed d (k+1) = true ∧ k+1 ≤ n then count d (k+1) (n-(k+1)) else 0) := by
  have union : (parts d k n ++ included d k n).Nodup := by
    refine List.pairwise_append.mpr ⟨parts_nodup .., includes_nodup .., ?_⟩
    intro xs hx ys hy he
    obtain ⟨zs,rfl,_⟩ := mem_included.mp hy
    subst xs
    have := ((mem_parts.mp hx).2 (k+1) (by simp)).2
    omega
  have eqLen := same_length (parts_nodup d (k+1) n) union (by
    intro xs
    rw [List.mem_append, mem_included]
    constructor
    · intro hx
      obtain ⟨hp,ha⟩ := mem_parts.mp hx
      cases xs with
      | nil => exact Or.inl (mem_parts.mpr ⟨hp,by simp⟩)
      | cons a as =>
        by_cases he : a = k+1
        · subst a; exact Or.inr ⟨as,rfl,hx⟩
        · left
          apply mem_parts.mpr
          refine ⟨hp, fun b hb => ⟨(ha b hb).1,?_⟩⟩
          have hmax := (ha a (by simp)).2
          rcases List.mem_cons.mp hb with rfl | htail
          · omega
          · have hba := (List.pairwise_cons.mp hp.2.2).1 b htail
            omega
    · rintro (hx | ⟨ys,_,hx⟩)
      · obtain ⟨hp,ha⟩ := mem_parts.mp hx
        exact mem_parts.mpr ⟨hp,fun b hb => ⟨(ha b hb).1,Nat.le_succ_of_le (ha b hb).2⟩⟩
      · exact hx)
  rw [List.length_append] at eqLen
  unfold count
  by_cases ha : allowed d (k+1) = true ∧ k+1 ≤ n <;> simpa [included,ha] using eqLen

end LeanAndrews.ResidueRefine
