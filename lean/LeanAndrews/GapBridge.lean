import LeanAndrews.Lower
import LeanAndrews.Small

namespace LeanAndrews.GapBridge
open LeanAndrews.Lower
open Andrews.Small

theorem spaced_iff (g lo : Nat) (xs : List Nat) :
    Spaced g lo xs ↔ (∀ a ∈ xs, lo ≤ a) ∧ xs.Pairwise (fun a b => a+g ≤ b) := by
  induction xs generalizing lo with
  | nil => simp [Spaced]
  | cons x xs ih =>
    simp only [Spaced,List.forall_mem_cons,List.pairwise_cons,ih]
    constructor
    · rintro ⟨hx,hxs,hpw⟩
      exact ⟨⟨hx,fun a ha => Nat.le_trans (by omega : lo ≤ x+g) (hxs a ha)⟩, hxs, hpw⟩
    · rintro ⟨⟨hx,_⟩,hxs,hpw⟩
      exact ⟨hx,hxs,hpw⟩

theorem gapOK_iff (g : Nat) (xs : List Nat) :
    gapOK g xs = true ↔ xs.Pairwise (fun a b => b+g ≤ a) := by
  induction xs with
  | nil => simp [gapOK]
  | cons a xs ih =>
    cases xs with
    | nil => simp [gapOK]
    | cons b bs =>
      simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq] 
      change (b+g ≤ a ∧ gapOK g (b::bs) = true) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hab,hrest⟩
        refine List.pairwise_cons.mpr ⟨?_, hrest⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · have hcb := (List.pairwise_cons.mp hrest).1 c hc
          omega
      · intro hw
        obtain ⟨hfirst,hrest⟩ := List.pairwise_cons.mp hw
        exact ⟨hfirst b (by simp), hrest⟩

private theorem sum_snoc (xs : List Nat) (x : Nat) :
    (xs ++ [x]).sum = xs.sum + x := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.cons_append, List.sum_cons, ih]
    omega

theorem nat_sum_reverse (xs : List Nat) : xs.reverse.sum = xs.sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.reverse_cons,sum_snoc,ih,List.sum_cons,Nat.add_comm]

theorem reverse_mem_hParts_iff (g n : Nat) (xs : List Nat) :
    xs.reverse ∈ hParts g n ↔ Spaced g 1 xs ∧ xs.sum = n := by
  rw [hParts,List.mem_filter,mem_partitions,gapOK_iff,List.pairwise_reverse,spaced_iff]
  constructor
  · rintro ⟨⟨hs,hpos,_⟩,hgap⟩
    exact ⟨⟨fun a ha => hpos a (by simpa using ha),hgap⟩, (nat_sum_reverse xs) ▸ hs⟩
  · rintro ⟨⟨hpos,hgap⟩,hs⟩
    refine ⟨⟨(nat_sum_reverse xs).trans hs, ?_, List.pairwise_reverse.mpr ?_⟩, hgap⟩
    · intro a ha
      exact hpos a (by simpa using ha)
    · exact hgap.imp (by intro a b hab; omega)

/-- The actual descending-list enumeration includes the reverse of each genuine gap partition. -/
theorem gapToSmall_mem {g n : Nat} (xs : Gap g n) : xs.val.reverse ∈ hParts g n :=
  (reverse_mem_hParts_iff g n _).mpr xs.property

/-- Counting an injection between lists of distinct representatives. The target
may even repeat entries. -/
theorem length_le_of_injection {α β : Type} [DecidableEq β]
    {src : List α} {dst : List β} (f : α → β) (hnd : src.Nodup)
    (hmap : ∀ a ∈ src, f a ∈ dst)
    (hinj : ∀ a ∈ src, ∀ b ∈ src, f a = f b → a = b) : src.length ≤ dst.length := by
  induction src generalizing dst with
  | nil => simp
  | cons a as ih =>
    obtain ⟨hna,hn⟩ := List.nodup_cons.mp hnd
    have hfa : f a ∈ dst := hmap a (by simp)
    have h' : as.length ≤ (dst.erase (f a)).length := by
      apply ih hn
      · intro b hb
        have hne : f b ≠ f a := by
          intro eq
          exact hna ((hinj b (by simp [hb]) a (by simp) eq) ▸ hb)
        exact (List.mem_erase_of_ne hne).mpr (hmap b (by simp [hb]))
      · intro b hb c hc eq
        exact hinj b (by simp [hb]) c (by simp [hc]) eq
    have hdst : 0 < dst.length := by
      cases dst with
      | nil => contradiction
      | cons b bs => simp
    rw [List.length_erase_of_mem hfa] at h'
    simp only [List.length_cons]
    omega

/-- Lemma 2.2 in the exact numerical counting definitions used for the final theorem. -/
theorem scaling {d e m r : Nat} (hed : e ≤ d) (he : 0 < e) (hm : 0 < m) :
    hCount (e+1) (e*m) ≤ hCount (d+1) (d*m+r) := by
  let f := fun (xs : List Nat) => (scaleRaw d e m r xs.reverse).reverse
  have hsource (xs : List Nat) (h : xs ∈ hParts (e+1) (e*m)) :
      Spaced (e+1) 1 xs.reverse ∧ xs.reverse.sum=e*m := by
    apply (reverse_mem_hParts_iff (e+1) (e*m) xs.reverse).mp
    simpa using h
  apply length_le_of_injection f (List.Pairwise.filter _ (partitions_nodup _))
  · intro xs hx
    exact (reverse_mem_hParts_iff _ _ _).mpr (scaleRaw_valid hed he hm ⟨xs.reverse,hsource xs hx⟩)
  · intro xs hx ys hy eq
    have h := congrArg List.reverse eq
    simp only [f,List.reverse_reverse] at h
    have hinj := scaleRaw_injective (hsource xs hx).1 (hsource ys hy).1 h
    simpa only [List.reverse_reverse] using congrArg List.reverse hinj

end LeanAndrews.GapBridge
