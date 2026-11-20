import LeanAndrews.UpperBridge

/-! The ordered-parts comparison in the introduction. Its two specializations
use moduli `d+1` and `d`, with the part one kept and the part `b-1` removed. -/

namespace LeanAndrews.Historical

open Andrews.Small LeanAndrews.Upper LeanAndrews.UpperBridge

/-- The ascending nonunit parts in ±1 modulo b after excluding b−1. -/
def target (b i : Nat) : Nat :=
  b*(i/2+1) + if i%2 = 0 then 1 else b-1

def indexOf (b x : Nat) : Nat :=
  2*(x/b-1) + if x%b = 1 then 0 else 1

private theorem quotient_remainder (b i : Nat) (hb : 4 ≤ b) :
    target b i / b = i/2+1 ∧
    target b i % b = (if i%2=0 then 1 else b-1) := by
  let e := if i%2=0 then 1 else b-1
  have he : e < b := by dsimp [e]; split <;> omega
  have bp : 0 < b := by omega
  constructor
  · change (b*(i/2+1) + e) / b = _
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ bp, Nat.div_eq_of_lt he, Nat.zero_add]
  · change (b*(i/2+1)+e) % b = e
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he]

theorem indexOf_target (b i : Nat) (hb : 4 ≤ b) : indexOf b (target b i) = i := by
  obtain ⟨hq,hr⟩ := quotient_remainder b i hb
  unfold indexOf
  rw [hq,hr]
  by_cases h : i%2=0 <;> simp [h, show b-1≠1 by omega] <;> omega

private theorem target_succ (b i : Nat) (hb : 4 ≤ b) : target b i ≤ target b (i+1) := by
  by_cases h : i%2=0
  · have h' : (i+1)%2 ≠ 0 := by omega
    have same : (i+1)/2=i/2 := by omega
    simp [target, h, h', same]; omega
  · have h' : (i+1)%2 = 0 := by omega
    have next : (i+1)/2 = i/2 + 1 := by omega
    simp [target, h, h', next, Nat.mul_succ]; omega

private theorem target_mono {b i j : Nat} (hb : 4 ≤ b) (h : i ≤ j) : target b i ≤ target b j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (target_succ b _ hb)

private theorem target_big (b i : Nat) (_hb : 4 ≤ b) : b ≤ target b i := by
  unfold target
  rw [Nat.mul_succ]
  omega

theorem target_block (b j : Nat) (hb : 4 ≤ b) :
    target b (4*j) = 2*j*b + b + 1 ∧
    target b (4*j+1) = 2*j*b + 2*b - 1 ∧
    target b (4*j+2) = 2*j*b + 2*b + 1 ∧
    target b (4*j+3) = 2*j*b + 3*b - 1 := by
  have q0 : (4*j)/2 = 2*j := by omega
  have q1 : (4*j+1)/2 = 2*j := by omega
  have q2 : (4*j+2)/2 = 2*j+1 := by omega
  have q3 : (4*j+3)/2 = 2*j+1 := by omega
  have r0 : (4*j)%2 = 0 := by omega
  have r1 : (4*j+1)%2 ≠ 0 := by omega
  have r2 : (4*j+2)%2 = 0 := by omega
  have r3 : (4*j+3)%2 ≠ 0 := by omega
  have hsub := Nat.sub_add_cancel (show 1 ≤ b by omega)
  simp [target,q0,q1,q2,q3,r0,r1,r2,r3,Nat.mul_succ,Nat.mul_comm b (2*j)]
  omega

theorem target_le_residuePart {b d : Nat} (hb : 4 ≤ b) (hd : 4 ≤ d) (hbd : b ≤ d+1)
    (i : Nat) : target b i ≤ residuePart d i := by
  let j := i/4
  have hspan : 2*j*b ≤ 4*j*d := calc
    2*j*b ≤ 2*j*(2*d) := Nat.mul_le_mul_left _ (by omega)
    _ = 4*j*d := by change 2*j*(2*d)=(2*2)*j*d; ac_rfl
  obtain ⟨t0,t1,t2,t3⟩ := target_block b j hb
  obtain ⟨s0,s1,s2,s3⟩ := residuePart_block d j hd
  have cases4 : i=4*j ∨ i=4*j+1 ∨ i=4*j+2 ∨ i=4*j+3 := by dsimp [j]; omega
  rcases cases4 with h | h | h | h <;> rw [h] <;> omega

/-- Literal congruence-side test for the Inagaki–Tamura comparison set. -/
def allowed (b x : Nat) : Bool := (x % b == 1 || x % b == b-1) && (x != b-1)

private theorem allowed_target (b i : Nat) (hb : 4 ≤ b) : allowed b (target b i) = true := by
  have hm := (quotient_remainder b i hb).2
  have hbig := target_big b i hb
  have hne : target b i ≠ b-1 := by omega
  by_cases h : i%2=0 <;> simp [allowed, hm, h, hne]

private theorem allowed_one (b : Nat) (hb : 4 ≤ b) : allowed b 1 = true := by
  simp [allowed, Nat.mod_eq_of_lt (show 1<b by omega), show 1≠b-1 by omega]

def targetParts (b n : Nat) : List (List Nat) := (partitions n).filter (fun xs => xs.all (allowed b))
def targetCount (b n : Nat) := (targetParts b n).length

private def move (d b : Nat) (xs : List Nat) :=
  (strip xs).map (fun x => target b (x/d-1))

private def pad (n : Nat) (ys : List Nat) := ys ++ List.replicate (n-ys.sum) 1

private theorem move_weight {d b n : Nat} (hd : 4 ≤ d) (hb : 4 ≤ b) (hbd : b ≤ d+1)
    {xs : List Nat} (hx : xs ∈ QParts d n) : (move d b xs).sum ≤ n := by
  obtain ⟨hp, ha⟩ := on_source hd hx
  have weight (ys : List Nat) (hy : ∀ x ∈ ys, ∃ i, x=residuePart d i) :
      (ys.map (fun x => target b (x/d-1))).sum ≤ ys.sum := by
    induction ys with
    | nil => simp
    | cons x ys ih =>
      obtain ⟨i,rfl⟩ := hy x (by simp)
      have ht := ih (fun y hm => hy y (by simp [hm]))
      simp only [List.map_cons, List.sum_cons, residuePart_div d i hd, Nat.add_sub_cancel]
      exact Nat.add_le_add (target_le_residuePart hb hd hbd i) ht
  exact Nat.le_trans (weight _ ha) (hp.1 ▸ strip_weight xs)

private theorem moved_mem {d b n : Nat} (hd : 4 ≤ d) (hb : 4 ≤ b) (hbd : b ≤ d+1)
    {xs : List Nat} (hx : xs ∈ QParts d n) : pad n (move d b xs) ∈ targetParts b n := by
  obtain ⟨hp,_⟩ := on_source hd hx
  have hw := move_weight hd hb hbd hx
  let ys := move d b xs
  have together (x : Nat) (hm : x ∈ ys) : b ≤ x ∧ allowed b x = true := by
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hm
    exact ⟨target_big b _ hb, allowed_target b _ hb⟩
  have horder : ys.Pairwise (· ≥ ·) := (hp.2.2.filter _).map _ (fun _ _ h =>
    target_mono hb (Nat.sub_le_sub_right (div_monotone (by omega : 0 < d) h) 1))
  apply List.mem_filter.mpr
  refine ⟨mem_partitions.mpr ⟨?_,?_,?_⟩,?_⟩
  · change (ys ++ List.replicate (n-ys.sum) 1).sum = n
    have addsum (xs zs : List Nat) : (xs++zs).sum=xs.sum+zs.sum := by
      induction xs with
      | nil => simp
      | cons a xs ih => simp [ih, Nat.add_assoc]
    rw [addsum, List.sum_replicate_nat, Nat.mul_one]
    change ys.sum ≤ n at hw
    omega
  · intro x hm
    rcases List.mem_append.mp hm with h | h
    · have := (together x h).1; omega
    · have := List.eq_of_mem_replicate h; omega
  · apply List.pairwise_append.mpr
    refine ⟨horder, ?_, ?_⟩
    · apply List.pairwise_replicate.mpr
      simp
    · intro x hx y hy
      have := (together x hx).1
      have := List.eq_of_mem_replicate hy
      omega
  · apply List.all_eq_true.mpr
    intro x hm
    rcases List.mem_append.mp hm with h | h
    · exact (together x h).2
    · rw [List.eq_of_mem_replicate h]; exact allowed_one b hb

private theorem strip_padded (d b n : Nat) (hb : 4 ≤ b) (xs : List Nat) :
    strip (pad n (move d b xs)) = move d b xs := by
  unfold strip pad
  rw [List.filter_append]
  have hk : (move d b xs).filter (fun x => decide (1 < x)) = move d b xs := by
    apply List.filter_eq_self.mpr
    intro a ha
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
    have := target_big b (v/d-1) hb
    simp; omega
  simp [hk]

private theorem move_injective_on {d b n : Nat} (hd : 4 ≤ d) (hb : 4 ≤ b)
    {xs ys : List Nat} (hx : xs ∈ QParts d n) (hy : ys ∈ QParts d n)
    (he : pad n (move d b xs) = pad n (move d b ys)) : xs = ys := by
  apply code_injective_on hd hx hy
  have hs := congrArg strip he
  rw [strip_padded _ _ _ hb, strip_padded _ _ _ hb] at hs
  have recover (ws : List Nat) (hw : ws ∈ QParts d n) :
      (move d b ws).map (fun x => indexOf b x + 1) = code d ws := by
    unfold move code
    rw [List.map_map]
    apply List.map_congr_left
    intro x h
    obtain ⟨i,rfl⟩ := (on_source hd hw).2 x h
    simp [Function.comp_def, indexOf_target _ _ hb, residuePart_div _ _ hd]
  rw [← recover xs hx, ← recover ys hy, hs]

/-- The four-residue count is dominated by the two-residue count at the same
weight, after deleting the part b−1. This includes b=d and b=d+1. -/
theorem ordered_parts_comparison {d b : Nat} (hd : 4 ≤ d) (hb : 4 ≤ b)
    (hbd : b ≤ d+1) (n : Nat) : QCount d n ≤ targetCount b n := by
  let f := fun xs => pad n (move d b xs)
  have hq := (partitions_nodup n).filter (residueOK d)
  have hn : ((QParts d n).map f).Nodup := by
    apply List.pairwise_map.mpr
    exact hq.imp_of_mem (fun hx hy h he => h (move_injective_on hd hb hx hy he))
  have ht : (QParts d n).map f ⊆ targetParts b n := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    exact moved_mem hd hb hbd hy
  simpa [QCount,targetCount] using length_le_of_subset hn ht

/-- Application of the exact numerical range of Inagaki–Tamura,
Proposition 3.1, after substituting their gap k=d+1. -/
theorem prior_large_range
    (IT : ∀ k n, (k = 31 ∨ 63 ≤ k) → k+2 ≤ n → targetCount k n ≤ hCount k n)
    {d n : Nat} (hd : d = 30 ∨ 62 ≤ d) (hn : d+3 ≤ n) :
    QCount d n ≤ hCount (d+1) n :=
  Nat.le_trans (ordered_parts_comparison (by omega) (by omega) (Nat.le_refl _) n)
    (IT (d+1) n (by omega) (by omega))

/-- Application of their Lemma 6.2 after the same gap substitution. -/
theorem prior_bounded_range
    (IT : ∀ k n, 12 ≤ k → k+2 ≤ n → n ≤ 5*k → targetCount (k-1) n ≤ hCount k n)
    {d n : Nat} (hd : 11 ≤ d) (hlo : d+3 ≤ n) (hhi : n ≤ 5*(d+1)) :
    QCount d n ≤ hCount (d+1) n := by
  have h := IT (d+1) n (by omega) (by omega) hhi
  simp only [Nat.add_sub_cancel] at h
  exact Nat.le_trans (ordered_parts_comparison (by omega) (by omega) (Nat.le_succ d) n) h

end LeanAndrews.Historical
