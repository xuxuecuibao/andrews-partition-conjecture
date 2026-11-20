import Std.Tactic

namespace LeanAndrews.VerifiedTable

def Matches (a : Array Nat) (f : Nat → Nat) : Prop :=
  ∀ i, i < a.size → a[i]! = f i

def fill (step : Nat → Array Nat → Nat) : Nat → Array Nat → Array Nat
  | 0, a => a
  | n+1, a => fill step n (a.push (step a.size a))

def row (len : Nat) (step : Nat → Array Nat → Nat) : Array Nat :=
  fill step len (Array.emptyWithCapacity len)

theorem fill_size (step) (n) (a) : (fill step n a).size = a.size + n := by
  induction n generalizing a with
  | zero => simp [fill]
  | succ n ih => simp [fill, ih]; omega

@[simp] theorem row_size (len step) : (row len step).size = len := by simp [row, fill_size]

theorem matches_push {a : Array Nat} {f : Nat → Nat} {x : Nat}
    (ha : Matches a f) (hx : x = f a.size) : Matches (a.push x) f := by
  intro i hi
  rw [getElem!_pos (a.push x) i hi]
  by_cases h : i < a.size
  · rw [Array.getElem_push_lt h, ← getElem!_pos a i h]
    exact ha i h
  · have he : i = a.size := by simp at hi; omega
    subst i
    simpa using hx

theorem fill_matches {len step f}
    (hs : ∀ a : Array Nat, a.size < len → Matches a f → step a.size a = f a.size)
    (n : Nat) (a : Array Nat) (hlen : a.size + n ≤ len) (ha : Matches a f) :
    Matches (fill step n a) f := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    apply ih
    · simp; omega
    · exact matches_push ha (hs a (by omega) ha)

theorem row_matches {len step f}
    (hs : ∀ a : Array Nat, a.size < len → Matches a f → step a.size a = f a.size) :
    Matches (row len step) f := by
  apply fill_matches hs
  · simp
  · intro i hi; simp at hi

def base (len : Nat) := row len fun i _ => if i = 0 then 1 else 0

@[simp] theorem base_size (len) : (base len).size = len := row_size _ _
theorem base_matches (len) : Matches (base len) (fun i => if i = 0 then 1 else 0) :=
  row_matches (fun _ _ _ => rfl)

def addCoin (p : Nat) (prev : Array Nat) :=
  row prev.size fun i cur => prev[i]! + if p ≤ i then cur[i-p]! else 0

@[simp] theorem addCoin_size (p prev) : (addCoin p prev).size = prev.size := row_size _ _
theorem addCoin_matches {p : Nat} {prev : Array Nat} {f g : Nat → Nat}
    (hp : 0 < p) (hprev : Matches prev f)
    (hg : ∀ w, g w = f w + if p ≤ w then g (w-p) else 0) :
    Matches (addCoin p prev) g := by
  apply row_matches
  intro a ha hmatch
  rw [hg a.size, hprev a.size ha]
  by_cases h : p ≤ a.size
  · simp only [if_pos h]; rw [hmatch _ (by omega)]
  · simp [h]

end LeanAndrews.VerifiedTable
