module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Elimination
/-!
# Separately checked pivot proposals for binary elimination

A proposal specifies a mask, a row position and a packed row. `pivotsValid`
checks each row against its actual position at that stage. The numerical
row update uses the literal proposal, and its soundness theorem consumes
this validation. Separating validation from the update avoids reevaluating
old checks when comparing the final row lists. No external arithmetic is trusted.
-/

@[expose] public section
namespace PackedBinaryRows

def pull : Nat → List Nat → Nat × List Nat
  | _, [] => (0, [])
  | 0, r::rs => (r, rs)
  | k+1, r::rs => let t := pull k rs; (t.1, r::t.2)

lemma solutions_pull (n k : Nat) (rs : List Nat) (w : Fin n → ZMod 2) :
    solutions n ((pull k rs).1 :: (pull k rs).2) w ↔ solutions n rs w := by
  induction rs generalizing k with
  | nil => simp [pull, solutions_zero_cons]
  | cons r rs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have h := ih k
      simp only [pull, solutions_cons] at h ⊢
      tauto

abbrev PivotProposal := Nat × Nat × Nat

def applyPivot (q : PivotProposal) (s : State) : State :=
  (q.2.2 :: s.1.map (clear q.1 q.2.2), (pull q.2.1 s.2).2.map (clear q.1 q.2.2))

lemma stateSolutions_applyPivot (n : Nat) (q : PivotProposal) (s : State)
    (w : Fin n → ZMod 2) (he : (pull q.2.1 s.2).1 = q.2.2) :
    stateSolutions n (applyPivot q s) w ↔ stateSolutions n s w := by
  have h := solutions_pull n q.2.1 s.2 w
  simp only [solutions_cons, he] at h
  simp only [stateSolutions, applyPivot, solutions_cons]
  constructor
  · rintro ⟨⟨hp, hd⟩, ht⟩
    exact ⟨(solutions_clear n q.1 _ _ w hp).mp hd,
      h.mp ⟨hp, (solutions_clear n q.1 _ _ w hp).mp ht⟩⟩
  · rintro ⟨hd, ht⟩
    obtain ⟨hp, ht⟩ := h.mpr ht
    exact ⟨⟨hp, (solutions_clear n q.1 _ _ w hp).mpr hd⟩,
      (solutions_clear n q.1 _ _ w hp).mpr ht⟩

def hintedSteps : List PivotProposal → State → State
  | [], s => s
  | q::qs, s => hintedSteps qs (applyPivot q s)

def pivotsValid : List PivotProposal → State → Bool
  | [], _ => true
  | q::qs, s => ((pull q.2.1 s.2).1 == q.2.2) &&
      pivotsValid qs (applyPivot q s)

lemma stateSolutions_hintedSteps (n : Nat) (ps : List PivotProposal) (s : State)
    (w : Fin n → ZMod 2) (h : pivotsValid ps s = true) :
    stateSolutions n (hintedSteps ps s) w ↔ stateSolutions n s w := by
  induction ps generalizing s with
  | nil => rfl
  | cons q qs ih =>
    simp only [pivotsValid, Bool.and_eq_true, beq_iff_eq] at h
    exact (ih (applyPivot q s) h.2).trans (stateSolutions_applyPivot n q s w h.1)

lemma stateSolutions_checked (n : Nat) (ps : List PivotProposal) (s t u : State)
    (h : pivotsValid ps s = true ∧ hintedSteps ps s = t) (w : Fin n → ZMod 2)
    (hs : stateSolutions n s w ↔ stateSolutions n u w) :
    stateSolutions n t w ↔ stateSolutions n u w := by
  rw [← h.2]
  exact (stateSolutions_hintedSteps n ps s w h.1).trans hs

end PackedBinaryRows
