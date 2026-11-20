import LeanAndrews.GapBridge
import LeanAndrews.Reduction

namespace LeanAndrews.CountBasics
open Andrews.Small
open LeanAndrews.GapBridge

/-- The paper's pair condition on two parts written in descending order. -/
def StarPair (d upper lower : Nat) : Prop :=
  lower+d ≤ upper ∧ (upper % d = 0 → lower % d = 0 → lower+2*d ≤ upper)

theorem starPair_trans {d a b c : Nat} (h : StarPair d a b) (j : StarPair d b c) :
    StarPair d a c := by
  obtain ⟨hab,_⟩ := h
  obtain ⟨hbc,_⟩ := j
  exact ⟨by omega,by intros; omega⟩

theorem originalGapOK_iff (d : Nat) (xs : List Nat) :
    originalGapOK d xs = true ↔ xs.Pairwise (StarPair d) := by
  induction xs with
  | nil => simp [originalGapOK]
  | cons a xs ih =>
    cases xs with
    | nil => simp [originalGapOK]
    | cons b bs =>
      have hbool : (decide (b+d ≤ a) &&
        (a % d != 0 || b % d != 0 || decide (b+2*d ≤ a))) = true ↔ StarPair d a b := by
        simp only [StarPair,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq]
        omega
      change ((_ && _) && originalGapOK d (b::bs)) = true ↔ _
      rw [Bool.and_eq_true,hbool,ih]
      constructor
      · rintro ⟨hab,hrest⟩
        apply List.pairwise_cons.mpr
        refine ⟨?_,hrest⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · exact starPair_trans hab ((List.pairwise_cons.mp hrest).1 _ hc)
      · intro h
        obtain ⟨hfirst,hrest⟩ := List.pairwise_cons.mp h
        exact ⟨hfirst b (by simp),hrest⟩

theorem gap_implies_star {d a b : Nat} (h : b+(d+1) ≤ a) : StarPair d a b := by
  refine ⟨by omega,?_⟩
  intro ha hb
  have ha' := Nat.mod_add_div a d
  have hb' := Nat.mod_add_div b d
  rw [ha,Nat.zero_add] at ha'
  rw [hb,Nat.zero_add] at hb'
  have hg : b/d+2 ≤ a/d := by
    by_cases hg : b/d+2 ≤ a/d
    · exact hg
    · have hq : a/d ≤ b/d+1 := by omega
      have hh := Nat.mul_le_mul_left d hq
      rw [Nat.mul_add,Nat.mul_one,ha',hb'] at hh
      omega
  have hh := Nat.mul_le_mul_left d hg
  rw [Nat.mul_add,hb',ha',Nat.mul_comm d 2] at hh
  exact hh

/-- The inclusion of the ordinary-gap family into the refined-gap family. -/
theorem gapInclusion (d n : Nat) : hCount (d+1) n ≤ qCount d n := by
  apply length_le_of_injection id (List.Pairwise.filter _ (partitions_nodup _))
  · intro xs hx
    obtain ⟨hpar,hgap⟩ := List.mem_filter.mp hx
    apply List.mem_filter.mpr
    refine ⟨hpar,(originalGapOK_iff _ _).mpr ?_⟩
    exact ((gapOK_iff _ _).mp hgap).imp (fun h => gap_implies_star h)
  · exact fun _ _ _ _ h => h

theorem small (d n : Nat) (hd : 4 ≤ d) (hn : 1 ≤ n) (hs : n < 2*d) :
    qCount d n = 1+(n-d)/2 ∧ QCount d n = 1+(if d+2 ≤ n then 1 else 0) ∧
      hCount (d+1) n = 1+(n-d-1)/2 := by
  simpa only [Nat.sub_sub] using small_counts d n hd hn hs

theorem sixWeights (n : Nat) (hn : LeanAndrews.Reduction.exceptional n) :
    qCount 4 n = QCount 4 n ↔ n=12 := by
  apply (exceptional_comparison n ?_).2
  simpa only [List.mem_cons,List.not_mem_nil,or_false,LeanAndrews.Reduction.exceptional] using hn

/-- The first Göllnitz--Gordon identity uses the ordinary set of three classes
1,4,7 modulo 8. At d=2 the two signs of 4 represent the same class. -/
theorem allowed_two (a : Nat) :
    allowed 2 a = true ↔ a % 8 = 1 ∨ a % 8 = 4 ∨ a % 8 = 7 := by
  unfold allowed
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

/-- Schur's two classes modulo six are precisely the four allowed classes modulo twelve. -/
theorem allowed_three (a : Nat) :
    allowed 3 a = true ↔ a % 6 = 1 ∨ a % 6 = 5 := by
  unfold allowed
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

theorem mem_QParts_two {n : Nat} {xs : List Nat} :
    xs ∈ QParts 2 n ↔ IsPartition n xs ∧
      ∀ a ∈ xs, a % 8 = 1 ∨ a % 8 = 4 ∨ a % 8 = 7 := by
  simp only [QParts,List.mem_filter,mem_partitions,residueOK,List.all_eq_true,allowed_two]

theorem mem_QParts_three {n : Nat} {xs : List Nat} :
    xs ∈ QParts 3 n ↔ IsPartition n xs ∧
      ∀ a ∈ xs, a % 6 = 1 ∨ a % 6 = 5 := by
  simp only [QParts,List.mem_filter,mem_partitions,residueOK,List.all_eq_true,allowed_three]

theorem mem_qParts_iff {d n : Nat} {xs : List Nat} :
    xs ∈ qParts d n ↔ IsPartition n xs ∧ xs.Pairwise (StarPair d) := by
  simp only [qParts,List.mem_filter,mem_partitions,originalGapOK_iff]

theorem QCount_two (n : Nat) :
    QCount 2 n = ((partitions n).filter (fun xs => xs.all (fun a =>
      a % 8 == 1 || a % 8 == 4 || a % 8 == 7))).length := by
  unfold QCount QParts residueOK
  congr 1
  apply List.filter_congr
  intro xs _
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,allowed_two,Bool.or_eq_true,beq_iff_eq,or_assoc]

theorem QCount_three (n : Nat) :
    QCount 3 n = ((partitions n).filter (fun xs => xs.all (fun a =>
      a % 6 == 1 || a % 6 == 5))).length := by
  unfold QCount QParts residueOK
  congr 1
  apply List.filter_congr
  intro xs _
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,allowed_three,Bool.or_eq_true,beq_iff_eq]

end LeanAndrews.CountBasics
