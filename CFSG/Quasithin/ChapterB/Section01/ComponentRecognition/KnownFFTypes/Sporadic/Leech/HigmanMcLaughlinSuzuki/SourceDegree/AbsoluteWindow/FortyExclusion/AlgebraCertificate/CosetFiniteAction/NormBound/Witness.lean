module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Logic.Function.Iterate
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.Data

/-!
# Independent finite conditions for the sparse HS norm witness

These definitions use only the finite transition table and binary arithmetic.
The geometry, parity, and predecessor certificates can be checked separately
without importing the HS representation. Interpretation connects them to the
actual norm quotient and its universal-module consumer.

Source application: GM02 Proposition 5.1, HS case; Aschbacher--Smith K.4 p.457.
-/

@[expose] public section
open scoped BigOperators
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound

/-- Lists act by left composition, exactly as in the parent word action. -/
def pointWord (w : List (Fin 2)) (i : Tables.Index) : Tables.Index :=
  w.foldr (fun s j => Tables.transition s j) i

noncomputable def rowVector (r : Row) : (Tables.Index → ZMod 2) :=
  ∑ k : Fin 5, Pi.single (rowEntry r k) 1

noncomputable def selectedVector (c : ℕ) : (Tables.Index → ZMod 2) :=
  ∑ j : Fin 39, if c.testBit j.val then Pi.single (selected j) 1 else 0

noncomputable def columnVector (s : Fin 2) (j : Fin 39) : (Tables.Index → ZMod 2) :=
  Pi.single (Tables.transition s (selected j)) 1 - selectedVector (columnCode s j)

noncomputable def combinationVector (s : Fin 2) (j : Fin 39) : (Tables.Index → ZMod 2) :=
  ∑ r : Row, if (rowMask r).testBit (39*s.val+j.val) then rowVector r else 0

/-- Literal geometry of all five points of every published norm row.
The stored starting point is the preimage of the JSON start under c_step. -/
def SeedGeometry : Prop := ∀ (r : Row) (k : Fin 5),
  rowEntry r k =
    pointWord (conjugator (rowStep r)) ((Tables.transition 1)^[k.val] (rowStart r))

/-- Independent finite parity identities; they require no group interpretation. -/
def RowIdentities : Prop := ∀ (s : Fin 2) (j : Fin 39),
  columnVector s j = combinationVector s j

/-- The saved breadth-first predecessor has a smaller word code and reaches i
by its saved last letter. No full word evaluation is needed in this condition. -/
def PredecessorCondition : Prop := ∀ i : Tables.Index, i ≠ 0 →
  Tables.wordCode (predecessor i) < Tables.wordCode i ∧
    Tables.transition (lastLetter i) (predecessor i) = i

def Reachable : Prop := ∀ i : Tables.Index,
  ∃ w : List (Fin 2), pointWord w 0 = i

theorem reachable_of_predecessors (h : PredecessorCondition) : Reachable := by
  have aux : ∀ n (i : Tables.Index), Tables.wordCode i = n →
      ∃ w : List (Fin 2), pointWord w 0 = i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hn
      by_cases hi : i = 0
      · subst i
        exact ⟨[], rfl⟩
      · obtain ⟨hlt, hstep⟩ := h i hi
        obtain ⟨w, hw⟩ := ih (Tables.wordCode (predecessor i)) (hn ▸ hlt)
          (predecessor i) rfl
        refine ⟨lastLetter i :: w, ?_⟩
        change Tables.transition (lastLetter i) (pointWord w 0) = i
        rw [hw, hstep]
  intro i
  exact aux _ i rfl

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound
