module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.Witness

/-!
# Small Boolean checks for the finite HS table

A bounded Boolean scan avoids the dependent finite quantifiers in a concrete
kernel reduction. Its specification restores those quantifiers. The raw
predecessor checker is identified with the published table maps and word codes;
a complete certificate of it therefore supplies coordinate reachability.

Source application: GM02 Proposition 5.1, HS case; Aschbacher--Smith K.4 p.457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.FiniteCheck

def allRange (f : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => f start && allRange f (start+1) n

theorem allRange_eq_true (f : ℕ → Bool) (start n : ℕ) :
    allRange f start n = true ↔ ∀ j, j < n → f (start+j) = true := by
  induction n generalizing start with
  | zero => simp [allRange]
  | succ n ih =>
    rw [allRange, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hzero, hrest⟩ j hj
      cases j with
      | zero => simpa using hzero
      | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using hrest j (by omega)
    · intro h
      constructor
      · simpa using h 0 (by omega)
      · intro j hj
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using h (j+1) (by omega)

def rawTransition (s i : ℕ) : ℕ :=
  Tables.entry (if s = 0 then Tables.aBlocks else Tables.bBlocks) 17 i % 86625

theorem rawTransition_fin (s : Fin 2) (i : Tables.Index) :
    rawTransition s.val i.val = (Tables.transition s i).val := by
  simp only [rawTransition, Tables.transition, Fin.ext_iff, Fin.val_zero]

def predecessorCheck (i : ℕ) : Bool :=
  let p := Data.predecessors i % 86625
  let w := Tables.entry Tables.wordBlocks 32 i
  decide (Tables.entry Tables.wordBlocks 32 p < w) &&
    (rawTransition (w % 2) p == i)

theorem predecessorCheck_eq_true (i : Tables.Index) :
    predecessorCheck i.val = true ↔
      Tables.wordCode (predecessor i) < Tables.wordCode i ∧
        Tables.transition (lastLetter i) (predecessor i) = i := by
  change (decide (Tables.wordCode (predecessor i) < Tables.wordCode i) &&
    (rawTransition (lastLetter i).val (predecessor i).val == i.val)) = true ↔ _
  rw [rawTransition_fin]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Fin.ext_iff]

theorem predecessors_of_checks
    (h : ∀ i : Tables.Index, i ≠ 0 → predecessorCheck i.val = true) :
    PredecessorCondition := by
  intro i hi
  exact (predecessorCheck_eq_true i).mp (h i hi)

/-- Consumer: a completed raw certificate reaches every coordinate of the
same published transition table, with no HS-action assumption. -/
theorem reachable_of_checks
    (h : ∀ i : Tables.Index, i ≠ 0 → predecessorCheck i.val = true) :
    Reachable :=
  reachable_of_predecessors (predecessors_of_checks h)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.FiniteCheck

