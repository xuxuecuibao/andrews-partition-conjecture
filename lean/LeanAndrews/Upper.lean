import Std

/-! The injection of Lemma 2.1. Lists of nonunit parts are in increasing
order with repetitions allowed. The number of ones is kept separately. -/

namespace LeanAndrews.Upper

/-- The positive nonunit allowed part with zero-based index `i`. -/
def residuePart (d i : Nat) : Nat :=
  d * (i + 1) + match i % 4 with
    | 0 => 2
    | 1 => d - 2
    | 2 => d - 1
    | _ => 1

/-- The four positive nonunit parts in block `j` of the residue classes
`±1, ±(d+2) mod 4d`. The part one is handled separately. -/
theorem residuePart_block (d j : Nat) (hd : 4 ≤ d) :
    residuePart d (4*j) = 4*j*d + d + 2 ∧
    residuePart d (4*j+1) = 4*j*d + 3*d - 2 ∧
    residuePart d (4*j+2) = 4*j*d + 4*d - 1 ∧
    residuePart d (4*j+3) = 4*j*d + 4*d + 1 := by
  have hsub2 := Nat.sub_add_cancel (show 2 ≤ d by omega)
  have hsub1 := Nat.sub_add_cancel (show 1 ≤ d by omega)
  have h0 : 4*j % 4 = 0 := by omega
  have h1 : (4*j+1) % 4 = 1 := by omega
  have h2 : (4*j+2) % 4 = 2 := by omega
  have h3 : (4*j+3) % 4 = 3 := by omega
  simp [residuePart, h0, h1, h2, h3, Nat.mul_add, Nat.mul_comm d (4*j)]
  omega

private theorem offset_lt (d i : Nat) (hd : 4 ≤ d) :
    (match i % 4 with | 0 => 2 | 1 => d - 2 | 2 => d - 1 | _ => 1) < d := by
  have hsub2 := Nat.sub_add_cancel (show 2 ≤ d by omega)
  have hsub1 := Nat.sub_add_cancel (show 1 ≤ d by omega)
  split <;> omega

/-- Division by `d` reads off the positive, one-based index of a part. -/
theorem residuePart_div (d i : Nat) (hd : 4 ≤ d) :
    residuePart d i / d = i + 1 := by
  let x := (match i % 4 with | 0 => 2 | 1 => d - 2 | 2 => d - 1 | _ => 1)
  have hx : x < d := offset_lt d i hd
  change (d * (i + 1) + x) / d = i + 1
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < d),
    Nat.div_eq_of_lt hx, Nat.zero_add]

theorem residuePart_lower (d i : Nat) : d * (i + 1) ≤ residuePart d i := by
  unfold residuePart
  omega

structure ResiduePartition (d n : Nat) where
  ones : Nat
  nonunits : List Nat
  ordered : nonunits.Pairwise (· ≤ ·)
  allowed : ∀ x ∈ nonunits, ∃ i, x = residuePart d i
  total : ones + nonunits.sum = n
  deriving DecidableEq

/-- This finite family is the disjoint union of the ordinary partition
families of weights `0, ..., m`. -/
structure OrdinaryAtMost (m : Nat) where
  parts : List Nat
  ordered : parts.Pairwise (· ≤ ·)
  positive : ∀ x ∈ parts, 0 < x
  bound : parts.sum ≤ m
  deriving DecidableEq

theorem div_sum_le (d : Nat) (xs : List Nat) :
    d * (xs.map (· / d)).sum ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (by simpa [Nat.mul_comm] using Nat.div_mul_le_self x d) ih

private theorem sum_bound {d n : Nat} (p : ResiduePartition d n) :
    d * (p.nonunits.map (· / d)).sum ≤ n :=
  Nat.le_trans (div_sum_le d p.nonunits) (by have := p.total; omega)

/-- Send each nonunit part to its one-based index and drop the ones. -/
def encode {d m r : Nat} (hd : 4 ≤ d) (hr : r < d)
    (p : ResiduePartition d (d*m+r)) : OrdinaryAtMost m where
  parts := p.nonunits.map (· / d)
  ordered := p.ordered.map (fun x => x / d) (fun x _ h =>
    (Nat.le_div_iff_mul_le (by omega : 0 < d)).2
      (Nat.le_trans (Nat.div_mul_le_self x d) h))
  positive := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := p.allowed a ha
    rw [residuePart_div d i hd]
    omega
  bound := by
    have upper := sum_bound p
    apply Classical.byContradiction
    intro h
    have ht : m+1 ≤ (p.nonunits.map (· / d)).sum := by omega
    have lower := Nat.mul_le_mul_left d ht
    rw [Nat.mul_succ] at lower
    omega

/-- Expand positive indices back into their original nonunit parts. -/
def expand (d : Nat) (indices : List Nat) : List Nat :=
  indices.map (fun k => residuePart d (k - 1))

theorem expand_mapped (d : Nat) (hd : 4 ≤ d) (xs : List Nat)
    (h : ∀ x ∈ xs, ∃ i, x = residuePart d i) :
    expand d (xs.map (· / d)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i, rfl⟩ := h x (by simp)
    have ht : ∀ y ∈ xs, ∃ i, y = residuePart d i := by
      intro y hy
      exact h y (by simp [hy])
    simpa [expand, residuePart_div d i hd] using ih ht

theorem recover_nonunits {d m r : Nat} (hd : 4 ≤ d) (hr : r < d)
    (p : ResiduePartition d (d*m+r)) :
    expand d (encode hd hr p).parts = p.nonunits :=
  expand_mapped d hd p.nonunits p.allowed

theorem recover_ones {d m r : Nat} (hd : 4 ≤ d) (hr : r < d)
    (p : ResiduePartition d (d*m+r)) :
    d*m+r - (expand d (encode hd hr p).parts).sum = p.ones := by
  rw [recover_nonunits]
  have := p.total
  omega

theorem encode_injective {d m r : Nat} (hd : 4 ≤ d) (hr : r < d)
    {p q : ResiduePartition d (d*m+r)} (h : encode hd hr p = encode hd hr q) : p = q := by
  have hparts : p.nonunits = q.nonunits := by
    rw [← recover_nonunits hd hr p, ← recover_nonunits hd hr q, h]
  have hones : p.ones = q.ones := by
    rw [← recover_ones hd hr p, ← recover_ones hd hr q, h]
  cases p
  cases q
  simp_all


theorem div_monotone {d a b : Nat} (hd : 0 < d) (hab : a ≤ b) :
    a / d ≤ b / d :=
  (Nat.le_div_iff_mul_le hd).2 (Nat.le_trans (Nat.div_mul_le_self a d) hab)

theorem residuePart_monotone {d i j : Nat} (hd : 4 ≤ d) (hij : i ≤ j) :
    residuePart d i ≤ residuePart d j := by
  by_cases he : i = j
  · simp [he]
  · apply Classical.byContradiction
    intro hn
    have hle : residuePart d j ≤ residuePart d i := by omega
    have hh := div_monotone (by omega : 0 < d) hle
    rw [residuePart_div d j hd, residuePart_div d i hd] at hh
    omega

private theorem encode_expanded {d : Nat} (hd : 4 ≤ d) (xs : List Nat)
    (hp : ∀ k ∈ xs, 0 < k) : (expand d xs).map (· / d) = xs := by
  induction xs with
  | nil => rfl
  | cons k xs ih =>
    have hk := hp k (by simp)
    have ht : ∀ a ∈ xs, 0 < a := fun a ha => hp a (by simp [ha])
    have pred : k - 1 + 1 = k := by omega
    simpa [expand, residuePart_div, hd, pred] using ih ht

/-- Inverse on the image. The slack in the expanded weight is exactly
the required multiplicity of the part one. -/
def decode {d m n : Nat} (hd : 4 ≤ d) (p : OrdinaryAtMost m)
    (hfit : (expand d p.parts).sum ≤ n) : ResiduePartition d n where
  ones := n - (expand d p.parts).sum
  nonunits := expand d p.parts
  ordered := p.ordered.map _ (fun _ _ h => residuePart_monotone hd (Nat.sub_le_sub_right h 1))
  allowed := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
    exact ⟨k-1, rfl⟩
  total := Nat.sub_add_cancel hfit

theorem encode_decode {d m r : Nat} (hd : 4 ≤ d) (hr : r < d) (p : OrdinaryAtMost m)
    (hfit : (expand d p.parts).sum ≤ d*m+r) :
    (encode hd hr (decode hd p hfit)).parts = p.parts :=
  encode_expanded hd p.parts p.positive

/-! To count the two families in core Lean, enumerate all lists with bounded
length and entries and retain the weakly increasing lists of positive parts.
The enumeration is deliberately independent of the fast table computations. -/

private def words (bound : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | fuel + 1 => [] :: (List.range (bound+1)).flatMap
      (fun a => (words bound fuel).map (a :: ·))

private theorem mem_words {bound fuel : Nat} {xs : List Nat} :
    xs ∈ words bound fuel ↔ xs.length ≤ fuel ∧ ∀ a ∈ xs, a ≤ bound := by
  induction fuel generalizing xs with
  | zero => cases xs <;> simp [words]
  | succ fuel ih =>
    cases xs with
    | nil => simp [words]
    | cons x xs =>
      simp [words, List.mem_flatMap, List.mem_map, ih, Nat.lt_succ_iff, and_left_comm]

private def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: xs => let ys := unique xs; if a ∈ ys then ys else a :: ys

private theorem mem_unique {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    x ∈ unique xs ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => simp [unique]
  | cons a xs ih =>
    by_cases ha : a ∈ unique xs
    · have he : a ∈ xs := (ih a).1 ha
      simp [unique, ha, ih]
      exact fun eq => eq ▸ he
    · simp [unique, ha, ih]

private theorem nodup_unique {α : Type} [DecidableEq α] (xs : List α) :
    (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons a xs ih => simp only [unique]; split <;> simp_all

def ordinaryRows (m : Nat) : List (List Nat) :=
  (unique (words m m)).filter (fun xs => decide
    (xs.Pairwise (· ≤ ·) ∧ (∀ a ∈ xs, 0 < a) ∧ xs.sum ≤ m))

private theorem le_sum_of_mem {xs : List Nat} {a : Nat} (ha : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp at ha
    cases ha with
    | inl h => simp [h]
    | inr h => have := ih h; simp; omega

private theorem length_le_sum {xs : List Nat} (hp : ∀ a ∈ xs, 0 < a) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hp x (by simp)
    have ht := ih (fun a ha => hp a (by simp [ha]))
    simp; omega

theorem mem_ordinaryRows {m : Nat} {xs : List Nat} : xs ∈ ordinaryRows m ↔
    xs.Pairwise (· ≤ ·) ∧ (∀ a ∈ xs, 0 < a) ∧ xs.sum ≤ m := by
  simp only [ordinaryRows, List.mem_filter, decide_eq_true_eq, mem_unique, mem_words]
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨Nat.le_trans (length_le_sum h.2.1) h.2.2,
      fun _ ha => Nat.le_trans (le_sum_of_mem ha) h.2.2⟩, h⟩

theorem nodup_ordinaryRows (m : Nat) : (ordinaryRows m).Nodup :=
  List.Pairwise.filter _ (nodup_unique _)

/-- Each code occurs once. Expanding its indices and appending ones gives
the corresponding partition of weight `n` into the four residue classes. -/
def residueRows (d n : Nat) : List (List Nat) :=
  (ordinaryRows (n / d)).filter (fun xs => decide ((expand d xs).sum ≤ n))

theorem nodup_residueRows (d n : Nat) : (residueRows d n).Nodup :=
  List.Pairwise.filter _ (nodup_ordinaryRows _)

private theorem quotient_weight {d m r : Nat} (hr : r < d) :
    (d*m+r) / d = m := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < d), Nat.div_eq_of_lt hr,
    Nat.zero_add]

/-- The finite row enumeration contains exactly the images of the residue
partitions. Together with `encode_injective` this identifies its cardinality. -/
theorem mem_residueRows_iff {d m r : Nat} (hd : 4 ≤ d) (hr : r < d) (xs : List Nat) :
    xs ∈ residueRows d (d*m+r) ↔
      ∃ p : ResiduePartition d (d*m+r), (encode hd hr p).parts = xs := by
  simp only [residueRows, List.mem_filter, decide_eq_true_eq, quotient_weight hr,
    mem_ordinaryRows]
  constructor
  · rintro ⟨⟨ho, hp, hb⟩, hfit⟩
    let op : OrdinaryAtMost m := ⟨xs, ho, hp, hb⟩
    exact ⟨decode hd op hfit, encode_decode hd hr op hfit⟩
  · rintro ⟨p, rfl⟩
    let op := encode hd hr p
    refine ⟨⟨op.ordered, op.positive, op.bound⟩, ?_⟩
    rw [recover_nonunits]
    have := p.total
    omega

/-- The cardinal version of Lemma 2.1. -/
theorem residue_count_le {d m r : Nat} (_hd : 4 ≤ d) (hr : r < d) :
    (residueRows d (d*m+r)).length ≤ (ordinaryRows m).length := by
  unfold residueRows
  rw [quotient_weight hr]
  exact List.length_filter_le _ _

end LeanAndrews.Upper
