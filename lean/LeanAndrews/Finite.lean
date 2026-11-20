import Std

/-!
Exact computations for the finite table in the Andrews partition inequality.
The executable checks all rows. The soundness lemma and the small concrete
examples below are ordinary kernel proofs. No evaluated Boolean is imported
as a theorem.
-/

namespace LeanAndrews.Finite

-- A structurally recursive numeric range permits kernel reduction on small inputs
-- and a tight native loop on the full table.
private structure Span where
  start : Nat
  stop : Nat

private def span (start stop : Nat) : Span := ⟨start, stop⟩

private def iterate {β : Type} (range : Span) (init : β)
    (f : Nat → β → Id (ForInStep β)) : Id β :=
  let rec go (remaining i : Nat) (v : β) : Id β :=
    match remaining with
    | 0 => pure v
    | remaining + 1 => do
      match ← f i v with
      | .done w => return w
      | .yield w => go remaining (i + 1) w
  go (range.stop - range.start) range.start init

private instance : ForIn Id Span Nat where
  forIn := iterate


/-- Coefficients of 1/((1-q) ∏ (1-q^j)), using Euler's pentagonal recurrence. -/
def cumulativePartitions (limit : Nat) : Array Nat := Id.run do
  let mut reversed : List (Nat × Int) := []
  for j in span (1) (limit + 1) do
    let a := j * (3*j - 1) / 2
    if a > limit then break
    let sign : Int := if j % 2 = 1 then 1 else -1
    reversed := (a+j, sign) :: (a, sign) :: reversed
  let offsets := reversed.reverse
  let mut counts := (Array.replicate (limit+1) 0 : Array Nat)
  counts := counts.set! 0 1
  for n in span (1) (limit + 1) do
    let mut total : Int := 1
    for (offset, sign) in offsets do
      if n < offset then break
      let prev := (counts[n - offset]! : Int)
      total := if sign = 1 then total + prev else total - prev
    counts := counts.set! n total.toNat
  return counts

/-- Sample gap partitions using the staircase offset and partitions with parts ≤ k. -/
def gapSamples (gap stride limit : Nat) : Array Nat := Id.run do
  let bound := stride * limit
  let mut restricted := (Array.replicate (bound+1) 0 : Array Nat)
  let mut values := (Array.replicate (limit+1) 0 : Array Nat)
  restricted := restricted.set! 0 1
  values := values.set! 0 1
  if stride = 0 then return Array.replicate (limit+1) 1
  for k in span (1) (bound+1) do
    let shift := k + gap*k*(k-1)/2
    if bound < shift then break
    for w in span (k) (bound-shift+1) do
      restricted := restricted.set! w (restricted[w]! + restricted[w-k]!)
    let first := (shift+stride-1)/stride
    for i in span (first) (limit+1) do
      values := values.set! i (values[i]! + restricted[stride*i-shift]!)
  return values

/-- Coefficients obtained by admitting each allowed residue part with unlimited multiplicity. -/
def residueCounts (d limit : Nat) : Array Nat := Id.run do
  let mut counts := (Array.replicate (limit+1) 0 : Array Nat)
  counts := counts.set! 0 1
  for part in span (1) (limit+1) do
    let r := part % (4*d)
    if r = 1 ∨ r = 4*d-1 ∨ r = d+2 ∨ r = 3*d-2 then
      for w in span (part) (limit+1) do
        counts := counts.set! w (counts[w]! + counts[w-part]!)
  return counts

structure Claim where
  first : Nat
  last : Nat
  minimum : Nat
  firstMin : Nat
  zeros : List Nat
deriving Repr

/-- The first minimum is in range and all requested entries exist. -/
def fits (c : Claim) (left right : Array Nat) : Prop :=
  c.first ≤ c.firstMin ∧ c.firstMin ≤ c.last ∧
  c.last < left.size ∧ c.last < right.size

instance (c : Claim) (l r : Array Nat) : Decidable (fits c l r) := by
  unfold fits
  infer_instance

/-- Avoid truncated subtraction: compare left with right plus the proposed minimum. -/
def entryStatement (c : Claim) (i left right : Nat) : Prop :=
  right + c.minimum ≤ left ∧
  (i = c.firstMin → right + c.minimum = left) ∧
  (i < c.firstMin → right + c.minimum < left) ∧
  (i ∈ c.zeros ↔ left = right)

instance (c : Claim) (i l r : Nat) : Decidable (entryStatement c i l r) := by
  unfold entryStatement
  infer_instance

def checkRow (c : Claim) (left right : Array Nat) : Bool :=
  decide (fits c left right) &&
    (List.range (c.last+1)).all (fun i =>
      if c.first ≤ i then decide (entryStatement c i left[i]! right[i]!) else true)

theorem checkRow_sound {c : Claim} {left right : Array Nat}
    (h : checkRow c left right = true) :
    fits c left right ∧ ∀ i, c.first ≤ i → i ≤ c.last →
      entryStatement c i left[i]! right[i]! := by
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro i hlo hhi
  have hi : i ∈ List.range (c.last+1) := List.mem_range.mpr (Nat.lt_succ_of_le hhi)
  have ht := h.2 i hi
  simpa [hlo] using ht

-- Concrete small inputs are checked by definitional reduction in the kernel.
set_option maxRecDepth 4096 in
theorem cumulative_small : cumulativePartitions 5 = #[1, 2, 4, 7, 12, 19] := by decide +kernel

set_option maxRecDepth 4096 in
theorem residue_four_twelve : (residueCounts 4 12)[12]! = 4 := by decide +kernel

set_option maxRecDepth 4096 in
theorem gap_five_twelve : (gapSamples 5 1 12)[12]! = 4 := by decide +kernel

-- The certificate exercises first occurrence and the full zero set on a small row.
set_option maxRecDepth 8192 in
theorem low_four_eight_to_twelve :
    checkRow ⟨8, 12, 0, 8, [8, 10, 12]⟩ (gapSamples 5 1 12) (residueCounts 4 12) =
      true := by decide +kernel

def bigClaim : Claim := ⟨100, 65535, 22332733, 100, []⟩
def mediumClaim : Claim := ⟨2, 99, 1, 2, []⟩

def smallClaims : List (Nat × Claim) :=
  [(4, ⟨8, 399, 0, 8, [8, 10, 12, 16, 17, 18]⟩),
   (5, ⟨10, 499, 1, 10, []⟩), (6, ⟨12, 599, 1, 12, []⟩),
   (7, ⟨14, 699, 2, 14, []⟩), (8, ⟨16, 799, 2, 16, []⟩),
   (9, ⟨18, 899, 3, 18, []⟩)]

def report (label : String) (c : Claim) (l r : Array Nat) : IO Unit := do
  unless checkRow c l r do throw (IO.userError s!"Failed: {label}")
  IO.println s!"{label}, [{c.first}, {c.last}]: min {c.minimum} at {c.firstMin}, zeros {c.zeros}"

/-- Run from FiniteMain.lean. A failure terminates the executable with an error. -/
def runTable : IO Unit := do
  let p := cumulativePartitions bigClaim.last
  report "h5(4m) - P(m)" bigClaim (gapSamples 5 4 bigClaim.last) p
  report "h11(10m) - P(m)" mediumClaim (gapSamples 11 10 mediumClaim.last) p
  for (d, c) in smallClaims do
    report s!"h{d+1}(n) - Q*{d}(n)" c (gapSamples (d+1) 1 c.last) (residueCounts d c.last)

end LeanAndrews.Finite
