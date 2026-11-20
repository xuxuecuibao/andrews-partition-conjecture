import Std

namespace Andrews.Small

/-- Descending lists of positive parts of weight n, using only parts at most cap.
The first argument bounds the number of parts. -/
def enumerate : Nat → Nat → Nat → List (List Nat)
  | 0, n, _ => if n = 0 then [[]] else []
  | fuel+1, n, cap =>
    if n = 0 then [[]] else
      (List.range (min n cap)).flatMap fun j =>
        (enumerate fuel (n-(j+1)) (j+1)).map (List.cons (j+1))

def partitions (n : Nat) := enumerate n n n

def IsPartition (n : Nat) (xs : List Nat) : Prop :=
  xs.sum = n ∧ (∀ a ∈ xs, 0 < a) ∧ xs.Pairwise (· ≥ ·)

private theorem length_le_sum {xs : List Nat} (h : ∀ a ∈ xs, 0 < a) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have h' := ih (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem mem_enumerate {fuel n cap : Nat} {xs : List Nat} :
    xs ∈ enumerate fuel n cap ↔
    IsPartition n xs ∧ (∀ a ∈ xs, a ≤ cap) ∧ xs.length ≤ fuel := by
  induction fuel generalizing n cap xs with
  | zero =>
    cases xs with
    | nil => by_cases h : n = 0 <;> simp [enumerate, IsPartition, h, eq_comm]
    | cons a as => by_cases h : n = 0 <;> simp [enumerate, h]
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst n
      cases xs with
      | nil => simp [enumerate, IsPartition]
      | cons a as =>
        simp only [enumerate, if_true, List.mem_singleton, List.cons_ne_nil,
          false_iff, not_and]
        intro hp
        have h := hp.2.1 a (by simp)
        have hh := hp.1
        simp only [List.sum_cons] at hh
        omega
    · cases xs with
      | nil => simp [enumerate, hn, IsPartition, Ne.symm hn]
      | cons a as =>
        simp only [enumerate, if_neg hn, List.mem_flatMap, List.mem_map, List.mem_range]
        constructor
        · rintro ⟨j, hj, ys, hy, he⟩
          cases he
          obtain ⟨⟨hs, hpos, hord⟩, hbound, hlen⟩ := ih.mp hy
          have hjn : j < n := Nat.lt_of_lt_of_le hj (Nat.min_le_left ..)
          have hjc : j < cap := Nat.lt_of_lt_of_le hj (Nat.min_le_right ..)
          refine ⟨⟨?_, ?_, List.pairwise_cons.mpr ⟨hbound, hord⟩⟩, ?_, ?_⟩
          · simp only [List.sum_cons]; omega
          · simpa using And.intro (Nat.zero_lt_succ j) hpos
          · simp only [List.forall_mem_cons]
            exact ⟨by omega, fun b hb => Nat.le_trans (hbound b hb) (by omega)⟩
          · simp; omega
        · rintro ⟨⟨hs,hpos,hord⟩,hbound,hlen⟩
          have ha := hpos a (by simp)
          have hac := hbound a (by simp)
          simp only [List.sum_cons] at hs
          have hs' : as.sum = n - a := by omega
          obtain ⟨small, ord⟩ := List.pairwise_cons.mp hord
          cases a with
          | zero => omega
          | succ j =>
            refine ⟨j, ?_, as, ih.mpr ⟨⟨hs', ?_, ord⟩, small, ?_⟩, rfl⟩
            · exact Nat.lt_min.mpr ⟨by omega, by omega⟩
            · exact fun b hb => hpos b (by simp [hb])
            · simpa using hlen

theorem mem_partitions {n : Nat} {xs : List Nat} :
    xs ∈ partitions n ↔ IsPartition n xs := by
  rw [partitions, mem_enumerate]
  constructor
  · exact And.left
  · intro hp
    refine ⟨hp, ?_, hp.1 ▸ length_le_sum hp.2.1⟩
    intro a ha
    have elem_le_sum {ys : List Nat} (hm : a ∈ ys) : a ≤ ys.sum := by
      induction ys with
      | nil => contradiction
      | cons b bs ih =>
        simp only [List.mem_cons] at hm
        simp only [List.sum_cons]
        rcases hm with rfl | h
        · omega
        · have := ih h; omega
    exact hp.1 ▸ elem_le_sum ha

private theorem enumerate_nodup (fuel n cap : Nat) : (enumerate fuel n cap).Nodup := by
  induction fuel generalizing n cap with
  | zero => by_cases hn : n=0 <;> simp [enumerate,hn]
  | succ fuel ih =>
    by_cases hn : n = 0
    · simp [enumerate, hn]
    · simp only [enumerate, if_neg hn]
      apply List.pairwise_flatMap.mpr
      constructor
      · intro j _
        apply List.pairwise_map.mpr
        exact (ih (n-(j+1)) (j+1)).imp (by intro a b h e; exact h (List.cons.inj e).2)
      · apply List.nodup_range.imp
        intro a b hab x hx y hy
        obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ys, _, rfl⟩ := List.mem_map.mp hy
        intro heq
        have := (List.cons.inj heq).1
        omega

theorem partitions_nodup (n : Nat) : (partitions n).Nodup := enumerate_nodup n n n

def gapOK (g : Nat) : List Nat → Bool
  | a :: b :: rest => decide (b+g ≤ a) && gapOK g (b::rest)
  | _ => true

def originalGapOK (d : Nat) : List Nat → Bool
  | a :: b :: rest =>
    decide (b+d ≤ a) && (a % d != 0 || b % d != 0 || decide (b+2*d ≤ a)) &&
    originalGapOK d (b::rest)
  | _ => true

def allowed (d a : Nat) : Bool :=
  let r := a % (4*d)
  r == 1 || r == d+2 || r == 3*d-2 || r == 4*d-1

def residueOK (d : Nat) (xs : List Nat) := xs.all (allowed d)
def qParts (d n : Nat) := (partitions n).filter (originalGapOK d)
def QParts (d n : Nat) := (partitions n).filter (residueOK d)
def hParts (g n : Nat) := (partitions n).filter (gapOK g)
def qCount (d n : Nat) := (qParts d n).length
def QCount (d n : Nat) := (QParts d n).length
def hCount (g n : Nat) := (hParts g n).length

private theorem count_if_mem {α : Type} [DecidableEq α] (a : α) {xs : List α}
    (h : xs.Nodup) : xs.count a = if a ∈ xs then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp h
    by_cases hba : b = a
    · subst b; simp [List.count_eq_zero_of_not_mem hn]
    · simp [List.count_cons_of_ne hba, ih ht, Ne.symm hba]

theorem same_length {α : Type} [DecidableEq α] {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hm : ∀ a, a ∈ xs ↔ a ∈ ys) :
    xs.length = ys.length := by
  apply List.Perm.length_eq
  apply List.perm_iff_count.mpr
  intro a
  simp only [count_if_mem a hx, count_if_mem a hy, hm a]

private def pairList (g n : Nat) : List (List Nat) :=
  [n] :: (List.range ((n-g)/2)).map (fun j => [n-(j+1),j+1])

private theorem pairList_nodup (g n : Nat) : (pairList g n).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · simp
  · apply List.pairwise_map.mpr
    apply List.nodup_range.imp
    intro a b h he
    have := (List.cons.inj (List.cons.inj he).2).1
    omega

private theorem mem_hParts_small {g n : Nat} (hg : 1 ≤ g) (hn : 0 < n) (hs : n < 2*g)
    (xs : List Nat) : xs ∈ hParts g n ↔ xs ∈ pairList g n := by
  simp only [hParts, List.mem_filter, mem_partitions, pairList,
    List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨hp, hok⟩
    cases xs with
    | nil => have := hp.1; simp at this; omega
    | cons a as =>
      cases as with
      | nil => left; have := hp.1; simpa using this
      | cons b bs =>
        cases bs with
        | nil =>
          right
          have hb := hp.2.1 b (by simp)
          have hsum := hp.1
          simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
          simp [gapOK] at hok
          refine ⟨b-1, by omega, ?_⟩
          rw [show b-1+1=b by omega, show n-b=a by omega]
        | cons c cs =>
          have hsum := hp.1
          simp only [List.sum_cons] at hsum
          simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq] at hok
          have := hok.1
          have := hok.2.1
          omega
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · simp [IsPartition, gapOK, hn]
    · have hgap : (j+1)+g ≤ n-(j+1) := by omega
      have hsum : n-(j+1)+(j+1) = n := by omega
      simp [IsPartition, gapOK, hsum, hgap, show j+1 ≤ n-(j+1) by omega,
        show 0 < n-(j+1) by omega]

theorem hCount_small {g n : Nat} (hg : 1 ≤ g) (hn : 0 < n) (hs : n < 2*g) :
    hCount g n = 1 + (n-g)/2 := by
  have h := same_length (List.Pairwise.filter _ (partitions_nodup n)) (pairList_nodup g n)
    (mem_hParts_small hg hn hs)
  simpa [hCount, hParts, pairList, Nat.add_comm] using h

private theorem original_eq_gap {d : Nat} (xs : List Nat) (hsmall : xs.sum < 2*d)
    (hpos : ∀ a ∈ xs, 0 < a) (hord : xs.Pairwise (· ≥ ·)) :
    originalGapOK d xs = gapOK d xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      have hle := (List.pairwise_cons.mp hord).1 b (by simp)
      have hb := hpos b (by simp)
      simp only [List.sum_cons] at hsmall
      have hbd : b < d := by omega
      have ih' := ih (by simp only [List.sum_cons]; omega)
        (fun v hv => hpos v (by simp [hv])) (List.pairwise_cons.mp hord).2
      have bne : (b != 0) = true := by cases b <;> simp_all
      simp [originalGapOK, gapOK, Nat.mod_eq_of_lt hbd, bne, ih']

theorem qCount_small {d n : Nat} (hd : 1 ≤ d) (hn : 0 < n) (hs : n < 2*d) :
    qCount d n = 1 + (n-d)/2 := by
  have eqLists : qParts d n = hParts d n := by
    apply List.filter_congr
    intro xs hx
    obtain ⟨hw,hp,ho⟩ := mem_partitions.mp hx
    exact original_eq_gap xs (hw ▸ hs) hp ho
  simpa [qCount, hCount, eqLists] using hCount_small hd hn hs

private theorem allowed_small {d a : Nat} (hd : 4 ≤ d) (ha : a < 2*d) :
    allowed d a = true ↔ a = 1 ∨ a = d+2 := by
  have ha' : a < 4*d := by omega
  simp [allowed, Nat.mod_eq_of_lt ha']
  omega

private theorem ones_of_all {xs : List Nat} (h : ∀ a ∈ xs, a=1) :
    xs = List.replicate xs.sum 1 := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    subst a
    simp only [List.sum_cons, Nat.one_add, List.replicate_succ]
    exact congrArg _ ht

private theorem le_sum_of_mem {a : Nat} {xs : List Nat} (h : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => contradiction
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp
    · have := ih ht; simp only [List.sum_cons]; omega

private def residueList (d n : Nat) : List (List Nat) :=
  (List.replicate n 1) :: (if d+2 ≤ n then [(d+2) :: List.replicate (n-(d+2)) 1] else [])

private theorem residueList_nodup (d n : Nat) (hn : 0 < n) : (residueList d n).Nodup := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [residueList, List.replicate_succ, List.nodup_cons]
    split <;> simp <;> omega

private theorem mem_QParts_small {d n : Nat} (hd : 4 ≤ d) (hn : 0 < n) (hs : n < 2*d)
    (xs : List Nat) : xs ∈ QParts d n ↔ xs ∈ residueList d n := by
  simp only [QParts, List.mem_filter, mem_partitions, residueOK, List.all_eq_true,
    residueList, List.mem_cons]
  constructor
  · rintro ⟨⟨hw,hpos,hord⟩, hallow⟩
    have either : ∀ a ∈ xs, a=1 ∨ a=d+2 := by
      intro a ha
      have bound := le_sum_of_mem ha
      exact (allowed_small hd (by omega)).mp (hallow a ha)
    cases xs with
    | nil => simp at hw; omega
    | cons a as =>
      rcases either a (by simp) with rfl | rfl
      · left
        rw [← hw]
        apply ones_of_all
        intro b hb
        rcases List.mem_cons.mp hb with rfl | h
        · rfl
        · have hbo := (List.pairwise_cons.mp hord).1 b h
          have hbp := hpos b (by simp [h])
          omega
      · right
        simp only [List.sum_cons] at hw
        rw [if_pos (by omega : d+2 ≤ n), List.mem_singleton]
        have ht : as = List.replicate as.sum 1 := by
          apply ones_of_all
          intro b hb
          have hle := le_sum_of_mem hb
          rcases either b (by simp [hb]) with h | h <;> omega
        rw [show n-(d+2) = as.sum by omega]
        exact congrArg _ ht
  · rintro (rfl | h)
    · constructor
      · simp [IsPartition, List.mem_replicate]
      · intro a ha
        have heq := List.eq_of_mem_replicate ha
        exact (allowed_small hd (by omega)).mpr (Or.inl heq)
    · split at h
      next hdn =>
        obtain rfl := List.mem_singleton.mp h
        constructor
        · simp [IsPartition, List.mem_replicate, List.pairwise_cons,
            show d+2+(n-(d+2))=n by omega]
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | hm
          · exact (allowed_small hd (by omega)).mpr (Or.inr rfl)
          · have heq := List.eq_of_mem_replicate hm
            exact (allowed_small hd (by omega)).mpr (Or.inl heq)
      next _ => contradiction

theorem QCount_small {d n : Nat} (hd : 4 ≤ d) (hn : 0 < n) (hs : n < 2*d) :
    QCount d n = 1 + (if d+2 ≤ n then 1 else 0) := by
  have h := same_length (List.Pairwise.filter _ (partitions_nodup n)) (residueList_nodup d n hn)
    (mem_QParts_small hd hn hs)
  simp only [QCount, QParts, residueList, List.length_cons] at *
  by_cases hdn : d+2 ≤ n <;> simpa [hdn] using h

theorem small_counts (d n : Nat) (hd : 4 ≤ d) (hn : 1 ≤ n) (hs : n < 2*d) :
    qCount d n = 1+(n-d)/2 ∧
    QCount d n = 1+(if d+2 ≤ n then 1 else 0) ∧
    hCount (d+1) n = 1+(n-(d+1))/2 :=
  ⟨qCount_small (by omega) hn hs, QCount_small hd hn hs, hCount_small (by omega) hn (by omega)⟩

theorem small_equality (d n : Nat) (hd : 4 ≤ d) (hn : 1 ≤ n) (hs : n < 2*d) :
    qCount d n = QCount d n ↔ n ≤ d+3 := by
  obtain ⟨hq,hQ,_⟩ := small_counts d n hd hn hs
  rw [hq,hQ]
  split <;> omega

theorem small_domination (d n : Nat) (hd : 4 ≤ d) (hn : 1 ≤ n) (hs : n < 2*d) :
    QCount d n ≤ qCount d n := by
  obtain ⟨hq,hQ,_⟩ := small_counts d n hd hn hs
  rw [hq,hQ]
  split <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exceptional_counts :
    [8,10,12,16,17,18].map (fun n => (qCount 4 n,QCount 4 n,hCount 5 n)) =
    [(3,2,2),(4,3,3),(4,4,4),(8,6,6),(9,7,7),(11,8,8)] := by decide


private theorem observed_count {n i a b c : Nat}
    (h : [8,10,12,16,17,18][i]? = some n)
    (h' : [(3,2,2),(4,3,3),(4,4,4),(8,6,6),(9,7,7),(11,8,8)][i]? = some (a,b,c)) :
    (qCount 4 n,QCount 4 n,hCount 5 n) = (a,b,c) := by
  have e := congrArg (fun l : List (Nat × Nat × Nat) => l[i]?) exceptional_counts
  dsimp only at e
  rw [List.getElem?_map, h, h'] at e
  exact Option.some.inj e

theorem exceptional_equality : qCount 4 12 = 4 ∧ QCount 4 12 = 4 := by
  have h := observed_count (n:=12) (i:=2) (a:=4) (b:=4) (c:=4) rfl rfl
  exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj (Prod.mk.inj h).2).1⟩

theorem exceptional_comparison (n : Nat) (hn : n ∈ [8,10,12,16,17,18]) :
    QCount 4 n ≤ qCount 4 n ∧ (qCount 4 n = QCount 4 n ↔ n = 12) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | have h := observed_count (n:=8) (i:=0) (a:=3) (b:=2) (c:=2) rfl rfl
      obtain ⟨h₁,h'⟩ := Prod.mk.inj h
      rw [h₁, (Prod.mk.inj h').1]; decide
    | have h := observed_count (n:=10) (i:=1) (a:=4) (b:=3) (c:=3) rfl rfl
      obtain ⟨h₁,h'⟩ := Prod.mk.inj h
      rw [h₁, (Prod.mk.inj h').1]; decide
    | have h := observed_count (n:=12) (i:=2) (a:=4) (b:=4) (c:=4) rfl rfl
      obtain ⟨h₁,h'⟩ := Prod.mk.inj h
      rw [h₁, (Prod.mk.inj h').1]; decide
    | have h := observed_count (n:=16) (i:=3) (a:=8) (b:=6) (c:=6) rfl rfl
      obtain ⟨h₁,h'⟩ := Prod.mk.inj h
      rw [h₁, (Prod.mk.inj h').1]; decide
    | have h := observed_count (n:=17) (i:=4) (a:=9) (b:=7) (c:=7) rfl rfl
      obtain ⟨h₁,h'⟩ := Prod.mk.inj h
      rw [h₁, (Prod.mk.inj h').1]; decide
    | have h := observed_count (n:=18) (i:=5) (a:=11) (b:=8) (c:=8) rfl rfl
      obtain ⟨h₁,h'⟩ := Prod.mk.inj h
      rw [h₁, (Prod.mk.inj h').1]; decide

end Andrews.Small
