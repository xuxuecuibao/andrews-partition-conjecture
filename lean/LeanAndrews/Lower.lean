import Std

namespace LeanAndrews.Lower

/-- Ascending parts with first part at least `lo` and adjacent gaps at least `g`. -/
def Spaced (g lo : Nat) : List Nat → Prop
  | [] => True
  | x :: xs => lo ≤ x ∧ Spaced g (x + g) xs

/-- Genuine partitions of the fixed weight, represented by their ascending parts. -/
abbrev Gap (g n : Nat) := {xs : List Nat // Spaced g 1 xs ∧ xs.sum = n}

def triangle : Nat → Nat
  | 0 => 0
  | k + 1 => triangle k + k

def dress (g base : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => (base + x) :: dress g (base + g) xs

def undress (g base : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => (x - base) :: undress g (base + g) xs

theorem spaced_weaken {g low high : Nat} {xs : List Nat} (hle : low ≤ high)
    (h : Spaced g high xs) : Spaced g low xs := by
  cases xs with
  | nil => trivial
  | cons x xs => exact ⟨Nat.le_trans hle h.1, h.2⟩

theorem spaced_dress_iff (g base low : Nat) (xs : List Nat) :
    Spaced g (base + low) (dress g base xs) ↔ Spaced 0 low xs := by
  induction xs generalizing base low with
  | nil => rfl
  | cons x xs ih =>
    simp only [dress, Spaced, Nat.add_zero]
    have heq : base + x + g = base + g + x := by omega
    rw [heq, ih]
    constructor
    · intro h
      exact ⟨by omega, h.2⟩
    · intro h
      exact ⟨by omega, h.2⟩

@[simp] theorem length_dress (g base : Nat) (xs : List Nat) :
    (dress g base xs).length = xs.length := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih => simp [dress, ih]

@[simp] theorem length_undress (g base : Nat) (xs : List Nat) :
    (undress g base xs).length = xs.length := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih => simp [undress, ih]

@[simp] theorem undress_dress (g base : Nat) (xs : List Nat) :
    undress g base (dress g base xs) = xs := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
    simp only [dress, undress, ih]
    exact congrArg (fun n => n :: xs) (show base + x - base = x by omega)

theorem dress_undress (g base : Nat) (xs : List Nat) (h : Spaced g base xs) :
    dress g base (undress g base xs) = xs := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
    have hp : base ≤ x := h.1
    have ht : Spaced g (base + g) xs := spaced_weaken (Nat.add_le_add_right hp g) h.2
    simp only [undress, dress, ih (base + g) ht]
    have eq : base + (x - base) = x := by omega
    rw [eq]

theorem spaced_undress {g base : Nat} {xs : List Nat} (h : Spaced g base xs) :
    Spaced 0 0 (undress g base xs) := by
  apply (spaced_dress_iff g base 0 _).mp
  simpa only [Nat.add_zero, dress_undress g base xs h] using h

theorem sum_dress (g base : Nat) (xs : List Nat) :
    (dress g base xs).sum = xs.sum + xs.length * base + triangle xs.length * g := by
  induction xs generalizing base with
  | nil => simp [dress, triangle]
  | cons x xs ih =>
    simp only [dress, List.sum_cons, List.length_cons, ih, triangle,
      Nat.succ_mul, Nat.mul_add, Nat.add_mul]
    ac_rfl

/-- The staircase gives mutually inverse maps between fixed-length positive gap
partitions and weakly increasing nonnegative lists of the residual weight. -/
theorem staircaseBijection (g k w : Nat) :
    let A := {xs : List Nat // Spaced 0 0 xs ∧ xs.length = k ∧ xs.sum = w}
    let B := {xs : List Nat // Spaced g 1 xs ∧ xs.length = k ∧
      xs.sum = w + k + triangle k * g}
    ∃ (f : A → B) (b : B → A),
      (∀ a, b (f a) = a) ∧ (∀ y, f (b y) = y) := by
  dsimp only
  let f := fun (x : {xs : List Nat // Spaced 0 0 xs ∧ xs.length = k ∧ xs.sum = w}) =>
    (⟨dress g 1 x.val, by
      refine ⟨(spaced_dress_iff g 1 0 _).mpr x.property.1, ?_, ?_⟩
      · simpa only [length_dress] using x.property.2.1
      · simp only [sum_dress, x.property.2.1, x.property.2.2, Nat.mul_one]⟩ :
      {xs : List Nat // Spaced g 1 xs ∧ xs.length = k ∧
        xs.sum = w + k + triangle k * g})
  let b := fun (x : {xs : List Nat // Spaced g 1 xs ∧ xs.length = k ∧
        xs.sum = w + k + triangle k * g}) =>
    (⟨undress g 1 x.val, by
      refine ⟨spaced_undress x.property.1, ?_, ?_⟩
      · simpa only [length_undress] using x.property.2.1
      · have hw := sum_dress g 1 (undress g 1 x.val)
        rw [dress_undress _ _ _ x.property.1, length_undress, x.property.2.1,
          Nat.mul_one, x.property.2.2] at hw
        omega⟩ : {xs : List Nat // Spaced 0 0 xs ∧ xs.length = k ∧ xs.sum = w})
  refine ⟨f, b, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact undress_dress g 1 x.val
  · intro x
    apply Subtype.ext
    exact dress_undress g 1 x.val x.property.1

/-- Multiplicities of the columns of heights k,k-1,...,1. -/
def columnCounts (prev : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => (x-prev) :: columnCounts x xs

def rowLengths (prev : Nat) : List Nat → List Nat
  | [] => []
  | c :: cs => (prev+c) :: rowLengths (prev+c) cs

/-- Weight of a partition in decreasing multiplicity-vector representation. -/
def columnWeight : List Nat → Nat
  | [] => 0
  | c :: cs => (cs.length+1)*c + columnWeight cs

@[simp] theorem length_columnCounts (prev : Nat) (xs : List Nat) :
    (columnCounts prev xs).length = xs.length := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [columnCounts, ih]

@[simp] theorem length_rowLengths (prev : Nat) (cs : List Nat) :
    (rowLengths prev cs).length = cs.length := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih => simp [rowLengths, ih]

theorem rowLengths_spaced (prev : Nat) (cs : List Nat) :
    Spaced 0 prev (rowLengths prev cs) := by
  induction cs generalizing prev with
  | nil => trivial
  | cons c cs ih => exact ⟨by omega, ih (prev+c)⟩

@[simp] theorem columnCounts_rowLengths (prev : Nat) (cs : List Nat) :
    columnCounts prev (rowLengths prev cs) = cs := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih =>
    simp only [rowLengths, columnCounts, ih]
    exact congrArg (fun a => a :: cs) (show prev+c-prev=c by omega)

theorem rowLengths_columnCounts (prev : Nat) (xs : List Nat) (h : Spaced 0 prev xs) :
    rowLengths prev (columnCounts prev xs) = xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    have hp := h.1
    have htail : Spaced 0 x xs := h.2
    have eq : prev + (x-prev) = x := by omega
    simp only [columnCounts, rowLengths, eq, ih x htail]

theorem sum_rowLengths (prev : Nat) (cs : List Nat) :
    (rowLengths prev cs).sum = cs.length*prev + columnWeight cs := by
  induction cs generalizing prev with
  | nil => simp [rowLengths,columnWeight]
  | cons c cs ih =>
    simp only [rowLengths,List.sum_cons,List.length_cons,columnWeight,ih,Nat.mul_add,
      Nat.succ_mul]
    ac_rfl

/-- Conjugation as a bijection from length-k weak rows to the multiplicities of
parts k,...,1 of a partition of w. -/
theorem conjugation (k w : Nat) :
    let A := {xs : List Nat // Spaced 0 0 xs ∧ xs.length = k ∧ xs.sum = w}
    let B := {cs : List Nat // cs.length = k ∧ columnWeight cs = w}
    ∃ (f : A → B) (b : B → A), (∀ x, b (f x) = x) ∧ (∀ y, f (b y) = y) := by
  dsimp only
  let f := fun (x : {xs : List Nat // Spaced 0 0 xs ∧ xs.length = k ∧ xs.sum = w}) =>
    (⟨columnCounts 0 x.val, by
      refine ⟨by simpa only [length_columnCounts] using x.property.2.1, ?_⟩
      have hw := sum_rowLengths 0 (columnCounts 0 x.val)
      simpa only [rowLengths_columnCounts 0 x.val x.property.1, Nat.mul_zero,
        Nat.zero_add, x.property.2.2] using hw.symm⟩ :
      {cs : List Nat // cs.length = k ∧ columnWeight cs = w})
  let b := fun (y : {cs : List Nat // cs.length = k ∧ columnWeight cs = w}) =>
    (⟨rowLengths 0 y.val, by
      exact ⟨rowLengths_spaced 0 y.val, by simpa only [length_rowLengths] using y.property.1,
        by simp only [sum_rowLengths, Nat.mul_zero, Nat.zero_add, y.property.2]⟩⟩ :
      {xs : List Nat // Spaced 0 0 xs ∧ xs.length = k ∧ xs.sum = w})
  refine ⟨f, b, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact rowLengths_columnCounts _ _ x.property.1
  · intro y
    apply Subtype.ext
    exact columnCounts_rowLengths _ _

/-- Change just the final part, leaving an empty list empty. -/
def mapLast (op : Nat → Nat) : List Nat → List Nat
  | [] => []
  | [x] => [op x]
  | x :: y :: ys => x :: mapLast op (y :: ys)

@[simp] theorem length_mapLast (op : Nat → Nat) (xs : List Nat) :
    (mapLast op xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => exact congrArg Nat.succ ih

theorem unbump_bump (t : Nat) (xs : List Nat) :
    mapLast (fun x => x - t) (mapLast (fun x => x + t) xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [mapLast]
    | cons y ys =>
      cases ys with
      | nil => simp [mapLast]
      | cons z zs => exact congrArg (List.cons x) ih

theorem spaced_bump (g low t : Nat) (xs : List Nat) (h : Spaced g low xs) :
    Spaced g low (mapLast (fun x => x + t) xs) := by
  induction xs generalizing low with
  | nil => trivial
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨Nat.le_trans h.1 (show x ≤ x+t by omega), trivial⟩
    | cons y ys => exact ⟨h.1, ih (x + g) h.2⟩

theorem sum_bump (t : Nat) (xs : List Nat) (h : xs ≠ []) :
    (mapLast (fun x => x + t) xs).sum = xs.sum + t := by
  induction xs with
  | nil => exact False.elim (h rfl)
  | cons x xs ih =>
    cases xs with
    | nil => simp [mapLast]
    | cons y ys =>
      have htail : y :: ys ≠ [] := by simp
      change x + (mapLast (fun x => x + t) (y :: ys)).sum = (x + (y :: ys).sum) + t
      rw [ih htail, Nat.add_assoc]

def scaleRaw (d e m r : Nat) (xs : List Nat) : List Nat :=
  let t := (d - e) * (m - triangle xs.length) + r
  dress (d + 1) 1 (mapLast (fun x => x + t) (undress (e + 1) 1 xs))

@[simp] theorem length_scaleRaw (d e m r : Nat) (xs : List Nat) :
    (scaleRaw d e m r xs).length = xs.length := by simp [scaleRaw]

theorem scaleRaw_valid {d e m r : Nat} (hed : e ≤ d) (he : 0 < e) (hm : 0 < m)
    (xs : Gap (e + 1) (e * m)) :
    Spaced (d + 1) 1 (scaleRaw d e m r xs.val) ∧ (scaleRaw d e m r xs.val).sum = d*m+r := by
  let ys := undress (e+1) 1 xs.val
  let k := xs.val.length
  let b := triangle k
  let t := (d-e)*(m-b)+r
  have hlen : ys.length = k := length_undress _ _ _
  have hst : Spaced 0 0 ys := spaced_undress xs.property.1
  have hback : dress (e+1) 1 ys = xs.val := dress_undress _ _ _ xs.property.1
  have hw : ys.sum + k + b*(e+1) = e*m := by
    have h := sum_dress (e+1) 1 ys
    rw [hback, xs.property.2, hlen, Nat.mul_one] at h
    exact h.symm
  have hbm : b ≤ m := by
    by_cases h : b ≤ m
    · exact h
    have him : m ≤ b := by omega
    have hem : e*m ≤ e*b := Nat.mul_le_mul_left e him
    have hprod : b*(e+1) = e*b + b := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm b e]
    omega
  have hne : ys ≠ [] := by
    intro h
    have hpos := Nat.mul_pos he hm
    have hx : xs.val = [] := by rw [← hback, h]; rfl
    have hz := xs.property.2
    rw [hx] at hz
    simp at hz
    omega
  have hscaledspace := (spaced_dress_iff (d+1) 1 0 _).mpr (spaced_bump 0 0 t ys hst)
  refine ⟨hscaledspace, ?_⟩
  change (dress (d+1) 1 (mapLast (fun x => x+t) ys)).sum = d*m+r
  rw [sum_dress, length_mapLast, hlen, Nat.mul_one, sum_bump _ _ hne]
  change ys.sum + t + k + b*(d+1) = d*m+r
  have hde : e+(d-e)=d := by omega
  have hmb : (m-b)+b=m := by omega
  have hsplit : (d-e)*(m-b) + (d-e)*b = (d-e)*m := by rw [← Nat.mul_add, hmb]
  have hsc : e*m+(d-e)*m = d*m := by rw [← Nat.add_mul, hde]
  have hgap : b*(d+1) = b*(e+1) + (d-e)*b := by
    have hr : d+1=(e+1)+(d-e) := by omega
    rw [hr, Nat.mul_add, Nat.mul_comm b (d-e)]
  dsimp only [t]
  omega

theorem scaleRaw_injective {d e m r : Nat} {xs zs : List Nat}
    (hx : Spaced (e+1) 1 xs) (hz : Spaced (e+1) 1 zs)
    (heq : scaleRaw d e m r xs = scaleRaw d e m r zs) : xs = zs := by
  have hk := congrArg List.length heq
  simp only [length_scaleRaw] at hk
  let t := (d-e)*(m-triangle zs.length)+r
  unfold scaleRaw at heq
  rw [hk] at heq
  have hb := congrArg (undress (d+1) 1) heq
  simp only [undress_dress] at hb
  have hu := congrArg (mapLast (fun x => x-t)) hb
  change mapLast (fun x => x-t) (mapLast (fun x => x+t) (undress (e+1) 1 xs)) =
    mapLast (fun x => x-t) (mapLast (fun x => x+t) (undress (e+1) 1 zs)) at hu
  simp only [unbump_bump] at hu
  have hd := congrArg (dress (e+1) 1) hu
  simpa only [dress_undress _ _ _ hx, dress_undress _ _ _ hz] using hd

/-- Explicit injection underlying Lemma 2.2. It also allows arbitrary remainders
and all positive e ≤ d. -/
theorem lowerScaling {d e m r : Nat} (hed : e ≤ d) (he : 0 < e) (hm : 0 < m) :
    ∃ f : Gap (e+1) (e*m) → Gap (d+1) (d*m+r), ∀ x y, f x = f y → x = y := by
  let f := fun (x : Gap (e+1) (e*m)) =>
    (⟨scaleRaw d e m r x.val, scaleRaw_valid hed he hm x⟩ : Gap (d+1) (d*m+r))
  refine ⟨f, ?_⟩
  intro x y heq
  apply Subtype.ext
  exact scaleRaw_injective x.property.1 y.property.1 (congrArg Subtype.val heq)

end LeanAndrews.Lower
