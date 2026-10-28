module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Hints
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.NormalForm
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Checker

/-!
# Indexed solution-preserving row operations

A proposal gives a mask selecting rows, the index of a pivot, and its packed
value. The pivot index and its actual current value are checked. Adding that
pivot to any selected other row preserves homogeneous solutions; the selected
rows need not satisfy a prescribed bit test.

Keeping indices fixed allows each resulting row to be checked independently.
`steps_eq_xor` fuses all additions into a single XOR sum without constructing
intermediate row lists. Short checks of the pointwise identities assemble via
`checkRange_append`. The final reindexing compares the resulting rows with the
published normal form in both directions.

The concrete consumer is the degree-1408 table in the sibling `Data.lean`.
See `source/README.md` and `../source/README.md` for the calculation and source.
-/

@[expose] public section
namespace PackedBinaryRows.Indexed
open Thompson.BinaryMatrix
open Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

def solutions (m n : Nat) (rs : Nat → Nat) (w : Fin n → ZMod 2) : Prop :=
  ∀ i, i < m → (fun j : Fin n => bit (rs i) j.val) ⬝ᵥ w = 0

def step (q : PivotProposal) (rs : Nat → Nat) (i : Nat) : Nat :=
  if i == q.2.1 then rs i else
    if q.1 / 2^i % 2 == 1 then rs i ^^^ q.2.2 else rs i

def steps : List PivotProposal → (Nat → Nat) → (Nat → Nat)
  | [], rs => rs
  | q::qs, rs => steps qs (step q rs)

def valid (m : Nat) : List PivotProposal → (Nat → Nat) → Bool
  | [], _ => true
  | q::qs, rs => (q.2.1 < m && rs q.2.1 == q.2.2) && valid m qs (step q rs)

lemma step_dot_iff (n : Nat) (q : PivotProposal) (rs : Nat → Nat)
    (i : Nat) (w : Fin n → ZMod 2)
    (hp : (fun j : Fin n => bit q.2.2 j.val) ⬝ᵥ w = 0) :
    (fun j : Fin n => bit (step q rs i) j.val) ⬝ᵥ w = 0 ↔
      (fun j : Fin n => bit (rs i) j.val) ⬝ᵥ w = 0 := by
  unfold step
  split
  · rfl
  · split
    · rw [dot_xor, hp, add_zero]
    · rfl

lemma solutions_step (m n : Nat) (q : PivotProposal) (rs : Nat → Nat)
    (w : Fin n → ZMod 2) (hi : q.2.1 < m) (hp : rs q.2.1 = q.2.2) :
    solutions m n (step q rs) w ↔ solutions m n rs w := by
  constructor
  · intro h
    have hz : (fun j : Fin n => bit q.2.2 j.val) ⬝ᵥ w = 0 := by
      simpa only [step, beq_self_eq_true, ite_true, hp] using h q.2.1 hi
    intro i him
    exact (step_dot_iff n q rs i w hz).mp (h i him)
  · intro h
    have hz : (fun j : Fin n => bit q.2.2 j.val) ⬝ᵥ w = 0 := by
      simpa only [hp] using h q.2.1 hi
    intro i him
    exact (step_dot_iff n q rs i w hz).mpr (h i him)

lemma solutions_steps (m n : Nat) (ps : List PivotProposal) (rs : Nat → Nat)
    (w : Fin n → ZMod 2) (h : valid m ps rs = true) :
    solutions m n (steps ps rs) w ↔ solutions m n rs w := by
  induction ps generalizing rs with
  | nil => rfl
  | cons q qs ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact (ih (step q rs) h.2).trans (solutions_step m n q rs w h.1.1 h.1.2)

def contribution (q : PivotProposal) (i : Nat) : Nat :=
  if i == q.2.1 then 0 else if q.1 / 2^i % 2 == 1 then q.2.2 else 0

def delta (i : Nat) : List PivotProposal → Nat
  | [] => 0
  | q::qs => contribution q i ^^^ delta i qs

lemma step_eq_xor (q : PivotProposal) (rs : Nat → Nat) (i : Nat) :
    step q rs i = rs i ^^^ contribution q i := by
  unfold step contribution
  split
  · simp
  · split <;> simp

lemma steps_eq_xor (ps : List PivotProposal) (rs : Nat → Nat) (i : Nat) :
    steps ps rs i = rs i ^^^ delta i ps := by
  induction ps generalizing rs with
  | nil => simp [steps, delta]
  | cons q qs ih => rw [steps, ih, step_eq_xor, delta, Nat.xor_assoc]

lemma solutions_checked (m n : Nat) (ps : List PivotProposal) (rs ts : Nat → Nat)
    (hv : valid m ps rs = true)
    (hc : checkRange (fun i => steps ps rs i == ts i) 0 m = true)
    (w : Fin n → ZMod 2) : solutions m n ts w ↔ solutions m n rs w := by
  have he (i : Nat) (hi : i < m) : steps ps rs i = ts i := by
    simpa only [Nat.zero_add, beq_iff_eq] using (checkRange_spec _ _ _).mp hc i hi
  have hh : solutions m n ts w ↔ solutions m n (steps ps rs) w := by
    constructor
    · intro h i hi
      rw [he i hi]
      exact h i hi
    · intro h i hi
      rw [← he i hi]
      exact h i hi
  exact hh.trans (solutions_steps m n ps rs w hv)

lemma solutions_checked_delta (m n : Nat) (ps : List PivotProposal) (rs ts : Nat → Nat)
    (hv : valid m ps rs = true)
    (hc : checkRange (fun i => (rs i ^^^ delta i ps) == ts i) 0 m = true)
    (w : Fin n → ZMod 2) : solutions m n ts w ↔ solutions m n rs w := by
  apply solutions_checked m n ps rs ts hv _ w
  apply (checkRange_spec _ _ _).mpr
  intro i hi
  simpa only [Nat.zero_add, steps_eq_xor] using (checkRange_spec _ _ _).mp hc i hi

lemma solutions_array (m n : Nat) (rs : Array Nat) (hs : rs.size = m)
    (w : Fin n → ZMod 2) : solutions m n (fun i => rs[i]!) w ↔
      PackedBinaryRows.solutions n rs.toList w := by
  constructor
  · intro h r hr
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hr)
    subst r
    simpa only [getElem!_pos rs i hi] using h i (hs ▸ hi)
  · intro h i hi
    have his : i < rs.size := hs ▸ hi
    change (fun j : Fin n => bit rs[i]! j.val) ⬝ᵥ w = 0
    rw [getElem!_pos rs i his]
    exact h _ (Array.mem_toList_iff.mpr (Array.getElem_mem his))

def normalRows (n v i : Nat) : Nat := if i < n then normalRow v i else 0

lemma solutions_normal (n v : Nat) (w : Fin (n+1) → ZMod 2) :
    solutions (n+1) (n+1) (normalRows n v) w ↔
      stateSolutions (n+1) (normalState n v) w := by
  simp only [stateSolutions, normalState, solutions_zero_cons]
  have hn := solutions_nil (n+1) w
  simp only [hn, and_true]
  constructor
  · intro h r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hin := List.mem_range.mp (List.mem_reverse.mp hi)
    simpa only [normalRows, if_pos hin] using h i (Nat.lt_succ_of_lt hin)
  · intro h i hi
    by_cases hin : i < n
    · simp only [normalRows, if_pos hin]
      exact h _ (List.mem_map.mpr ⟨i, List.mem_reverse.mpr (List.mem_range.mpr hin), rfl⟩)
    · simp [normalRows, hin, bit]

lemma solutions_reindex (m n : Nat) (rs ts : Nat → Nat) (f g : Nat → Nat)
    (hf : checkRange (fun i => f i < m && rs (f i) == ts i) 0 m = true)
    (hg : checkRange (fun i => g i < m && ts (g i) == rs i) 0 m = true)
    (w : Fin n → ZMod 2) : solutions m n ts w ↔ solutions m n rs w := by
  have hff (i : Nat) (hi : i < m) : f i < m ∧ rs (f i) = ts i := by
    simpa only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      using (checkRange_spec _ _ _).mp hf i hi
  have hgg (i : Nat) (hi : i < m) : g i < m ∧ ts (g i) = rs i := by
    simpa only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      using (checkRange_spec _ _ _).mp hg i hi
  constructor
  · intro h i hi
    obtain ⟨hj, he⟩ := hgg i hi
    simpa only [he] using h (g i) hj
  · intro h i hi
    obtain ⟨hj, he⟩ := hff i hi
    simpa only [he] using h (f i) hj
end PackedBinaryRows.Indexed
