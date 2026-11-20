import LeanAndrews.GapBridge

namespace LeanAndrews.CoinBridge
open LeanAndrews.Lower
open LeanAndrews.GapBridge
open Andrews.Small

private def bump : List Nat → List Nat
  | [] => []
  | c :: cs => (c+1) :: cs

private theorem bump_inj {xs ys : List Nat} (h : bump xs = bump ys) : xs=ys := by
  cases xs <;> cases ys <;> simp_all [bump]

/-- Admitting coins of value k+1, prepending their multiplicity to an
existing enumeration for the coins of value at most k. -/
private def addCoin (k : Nat) (prev : Nat → List (List Nat)) (w : Nat) :
    List (List Nat) :=
  (prev w).map (0 :: ·) ++
    if h : k+1 ≤ w then (addCoin k prev (w-(k+1))).map bump else []
termination_by w
decreasing_by omega

def coinVectors : Nat → Nat → List (List Nat)
  | 0, w => if w=0 then [[]] else []
  | k+1, w => addCoin k (coinVectors k) w

private theorem mem_addCoin {k : Nat} {prev : Nat → List (List Nat)}
    (hprev : ∀ w xs, xs ∈ prev w ↔ xs.length = k ∧ columnWeight xs = w)
    (w : Nat) (xs : List Nat) :
    xs ∈ addCoin k prev w ↔ xs.length = k+1 ∧ columnWeight xs = w := by
  induction w using Nat.strongRecOn generalizing xs with
  | ind w ih =>
    rw [addCoin]
    simp only [List.mem_append, List.mem_map]
    constructor
    · rintro (⟨ys,hy,rfl⟩ | h)
      · obtain ⟨hl,hw⟩ := (hprev w ys).mp hy
        simp [columnWeight,hl,hw]
      · split at h
        next hle =>
          obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp h
          obtain ⟨hl,hw⟩ := (ih (w-(k+1)) (by omega) ys).mp hy
          cases ys with
          | nil => simp at hl
          | cons c cs =>
            simp only [List.length_cons] at hl
            have he : cs.length = k := by omega
            simp only [bump,List.length_cons,columnWeight,he,Nat.mul_add,Nat.mul_one] at hw ⊢
            exact ⟨trivial,by omega⟩
        next => simp at h
    · rintro ⟨hl,hw⟩
      cases xs with
      | nil => simp at hl
      | cons c cs =>
        simp only [List.length_cons] at hl
        have he : cs.length=k := by omega
        cases c with
        | zero =>
          left
          refine ⟨cs, (hprev w cs).mpr ⟨he,?_⟩,rfl⟩
          simpa only [columnWeight,Nat.mul_zero,Nat.zero_add] using hw
        | succ c =>
          right
          simp only [columnWeight,he,Nat.mul_succ] at hw
          have hg : k+1 ≤ w := by omega
          simp only [dif_pos hg,List.mem_map]
          refine ⟨c::cs,(ih (w-(k+1)) (by omega) _).mpr ⟨hl,?_⟩,rfl⟩
          simp only [columnWeight,he]
          omega

theorem mem_coinVectors (k w : Nat) (xs : List Nat) :
    xs ∈ coinVectors k w ↔ xs.length = k ∧ columnWeight xs = w := by
  induction k generalizing w xs with
  | zero =>
    cases xs with
    | nil => by_cases h : w=0 <;> simp [coinVectors,columnWeight,h,eq_comm]
    | cons x xs => by_cases h : w=0 <;> simp [coinVectors,h]
  | succ k ih => exact mem_addCoin ih w xs

private theorem addCoin_nodup {k : Nat} {prev : Nat → List (List Nat)}
    (hp : ∀ w, (prev w).Nodup) (w : Nat) : (addCoin k prev w).Nodup := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    rw [addCoin]
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr ((hp w).imp (by intro a b h e; exact h (List.cons.inj e).2)),?_,?_⟩
    · split
      next hle => exact List.pairwise_map.mpr ((ih _ (by omega)).imp
        (by intro a b h he; exact h (bump_inj he)))
      next => simp
    · intro a ha b hb
      obtain ⟨xs,_,rfl⟩ := List.mem_map.mp ha
      split at hb
      next =>
        obtain ⟨ys,_,rfl⟩ := List.mem_map.mp hb
        cases ys <;> simp [bump]
      next => simp at hb

theorem coinVectors_nodup (k w : Nat) : (coinVectors k w).Nodup := by
  induction k generalizing w with
  | zero => by_cases h : w=0 <;> simp [coinVectors,h]
  | succ k ih => exact addCoin_nodup ih w

def restricted (k w : Nat) : Nat := (coinVectors k w).length

theorem restricted_zero (w : Nat) : restricted 0 w = if w=0 then 1 else 0 := by
  by_cases h : w=0 <;> simp [restricted,coinVectors,h]

theorem restricted_succ (k w : Nat) :
    restricted (k+1) w = restricted k w +
      (if k+1 ≤ w then restricted (k+1) (w-(k+1)) else 0) := by
  unfold restricted
  change (addCoin k (coinVectors k) w).length = _ + _
  rw [addCoin]
  by_cases h : k+1 ≤ w <;> simp [h, coinVectors]

def shift (g k : Nat) := k + triangle k * g

theorem twice_triangle (k : Nat) : triangle k * 2 = k*(k-1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [triangle,Nat.add_mul,ih]
    cases k with
    | zero => rfl
    | succ j =>
      simp only [Nat.succ_sub_one,Nat.succ_mul,Nat.mul_succ]
      omega

theorem shift_eq (g k : Nat) : shift g k = k + g*k*(k-1)/2 := by
  have h : g*k*(k-1) = (triangle k*g)*2 := calc
    g*k*(k-1) = g*(k*(k-1)) := Nat.mul_assoc _ _ _
    _ = g*(triangle k*2) := by rw [twice_triangle]
    _ = (triangle k*g)*2 := by ac_rfl
  unfold shift
  rw [h,Nat.mul_div_cancel _ (by decide : 0<2)]

theorem triangle_mono {k j : Nat} (h : k ≤ j) : triangle k ≤ triangle j := by
  induction j with
  | zero =>
    have hk : k=0 := by omega
    simp [hk]
  | succ j ih =>
    by_cases h0 : k ≤ j
    · have hh := ih h0
      simp only [triangle]
      omega
    · have hk : k=j+1 := by omega
      simp [hk]

theorem shift_mono (g : Nat) {k j : Nat} (h : k ≤ j) : shift g k ≤ shift g j :=
  Nat.add_le_add h (Nat.mul_le_mul_right g (triangle_mono h))

private def shape (g : Nat) (cs : List Nat) := (dress g 1 (rowLengths 0 cs)).reverse

private def term (g n k : Nat) : List (List Nat) :=
  if shift g k ≤ n then (coinVectors k (n-shift g k)).map (shape g) else []

private def terms (g n K : Nat) := (List.range K).flatMap (term g n)

private theorem shape_length (g : Nat) (cs : List Nat) : (shape g cs).length = cs.length := by
  simp [shape]

private theorem shape_inj (g : Nat) {cs ds : List Nat} (h : shape g cs=shape g ds) : cs=ds := by
  have h' := congrArg (fun xs => columnCounts 0 (undress g 1 xs.reverse)) h
  simpa [shape] using h'

private theorem term_length (g n k : Nat) :
    (term g n k).length = if shift g k ≤ n then restricted k (n-shift g k) else 0 := by
  by_cases h : shift g k ≤ n <;> simp [term,restricted,h]

private theorem term_mem_length {g n k : Nat} {xs : List Nat} (h : xs ∈ term g n k) :
    xs.length=k := by
  unfold term at h
  split at h
  next =>
    obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp h
    exact (shape_length _ _).trans ((mem_coinVectors _ _ _).mp hcs).1
  next => simp at h

private theorem terms_nodup (g n K : Nat) : (terms g n K).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    unfold term
    split
    next => exact List.pairwise_map.mpr ((coinVectors_nodup _ _).imp
      (by intro a b h e; exact h (shape_inj _ e)))
    next => simp
  · apply List.nodup_range.imp
    intro k j h xs hx ys hy e
    have hs := term_mem_length hx
    have hs' := term_mem_length hy
    subst ys
    exact h (hs.symm.trans hs')

private theorem mem_terms_iff (g n K : Nat) (bound : ∀ k, K ≤ k → n < shift g k) (xs : List Nat) :
    xs ∈ terms g n K ↔ xs ∈ hParts g n := by
  simp only [terms,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨k,_,hterm⟩
    unfold term at hterm
    split at hterm
    next hle =>
      obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hterm
      obtain ⟨hlen,hw⟩ := (mem_coinVectors _ _ _).mp hcs
      apply (reverse_mem_hParts_iff _ _ _).mpr
      refine ⟨(spaced_dress_iff g 1 0 _).mpr (rowLengths_spaced 0 _),?_⟩
      simp only [sum_dress,length_rowLengths,Nat.mul_one,sum_rowLengths,Nat.mul_zero,Nat.zero_add,hlen,hw]
      unfold shift at *
      omega
    next => simp at hterm
  · intro hx
    let ys := xs.reverse
    have hg : Spaced g 1 ys ∧ ys.sum=n := (reverse_mem_hParts_iff g n ys).mp (by simpa [ys] using hx)
    let k := ys.length
    let rows := undress g 1 ys
    let cs := columnCounts 0 rows
    have hl : rows.length=k := length_undress _ _ _
    have hcl : cs.length=k := (length_columnCounts _ _).trans hl
    have hrows : Spaced 0 0 rows := spaced_undress hg.1
    have hback : dress g 1 rows=ys := dress_undress _ _ _ hg.1
    have hrowback : rowLengths 0 cs=rows := rowLengths_columnCounts _ _ hrows
    have hw : rows.sum + shift g k = n := by
      have hs := sum_dress g 1 rows
      rw [hback,hg.2,hl,Nat.mul_one] at hs
      unfold shift
      omega
    have hc : columnWeight cs = rows.sum := by
      have hh := sum_rowLengths 0 cs
      simpa only [hrowback,Nat.mul_zero,Nat.zero_add] using hh.symm
    have hfit : shift g k ≤ n := by omega
    have hk : k<K := by
      by_cases hlt : k<K
      · exact hlt
      · have h := bound k (by omega); omega
    refine ⟨k,hk,?_⟩
    simp only [term,if_pos hfit,List.mem_map]
    refine ⟨cs,(mem_coinVectors _ _ _).mpr ⟨hcl,by omega⟩,?_⟩
    simp [shape,hrowback,hback,ys]

/-- Exact staircase formula for the partition enumerator used in the final
theorem. K is an exclusive cutoff after which every staircase exceeds n. -/
theorem gapCount_eq_sum (g n K : Nat) (bound : ∀ k, K ≤ k → n < shift g k) :
    hCount g n = ((List.range K).map (fun k =>
      if shift g k ≤ n then restricted k (n-shift g k) else 0)).sum := by
  have hs := fun xs => mem_terms_iff g n K bound xs
  have hl : (hParts g n).length = (terms g n K).length := by
    apply Nat.le_antisymm
    · apply length_le_of_injection id (List.Pairwise.filter _ (partitions_nodup _))
      · exact fun x hx => (hs x).mpr hx
      · exact fun _ _ _ _ h => h
    · apply length_le_of_injection id (terms_nodup g n K)
      · exact fun x hx => (hs x).mp hx
      · exact fun _ _ _ _ h => h
  rw [hCount,hl,terms,List.length_flatMap]
  simp only [List.map_map,Function.comp_def,term_length]

theorem gapCount_eq_sum_cutoff (g n K : Nat) (cut : n < shift g K) :
    hCount g n = ((List.range K).map (fun k =>
      if shift g k ≤ n then restricted k (n-shift g k) else 0)).sum :=
  gapCount_eq_sum g n K (fun _ hk => Nat.lt_of_lt_of_le cut (shift_mono g hk))

end LeanAndrews.CoinBridge
