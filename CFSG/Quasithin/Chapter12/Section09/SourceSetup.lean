module

public import CFSG.Quasithin.Chapter12.Section08.Setup.SourceData
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicRestrictions

/-!
# Entering the natural-module branch of Section 12.9

Theorems 12.5.1 and 12.6.34 must supply an actual marking of the original
chosen module. With that marking, the global exclusions in the counterexample
supply Hypothesis 12.8.1. For n=5 the missing PSL₆(2) exclusion follows from
the established quasithin degree bound, not from an extra model assumption.

This is only the setup implication. Neither of the two module reductions,
nor the subsequent local and fusion arguments of 12.9, is asserted here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Theorem 12.9.1 and its first reduction, printed p.857.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Natural coordinates retain the original chosen subgroup, its conjugation
action and the literal projection L → L/O₂(L). -/
def NaturalModule (D : ChosenModule T L V) (n : ℕ) : Prop :=
  let := D.elementary
  Nonempty (AmbientNaturalMarking L D.normalizes n)

/-- The exact 12.8.1 input from the two earlier module reductions and the
ambient exclusions used in the opening of 12.9. -/
theorem higherRank_of_natural
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (hn : n = 4 ∨ n = 5) (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2)
    (hnatural : NaturalModule D n)
    (hfive : ¬ ClassicalGroup.IsPSL G 5 2)
    (hnine : ¬ Nonempty (G ≃* alternatingGroup (Fin 9)))
    (hmathieu : ¬ Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    Nonempty (HigherRankHypothesis K T L V n) := by
  let := D.elementary
  obtain ⟨marking⟩ := hnatural
  refine ⟨{ source := h
            chosen := D
            rank := ?_
            quotient_model := hq
            natural := ⟨marking.quotientEquiv, marking.coordinates, marking.equivariant⟩
            no_nextLinear := ?_
            no_A9 := hnine
            no_M24 := hmathieu }⟩
  · rcases hn with rfl | rfl <;> omega
  · rcases hn with rfl | rfl
    · exact hfive
    · intro hmodel
      have hb := ChapterA.Section02.EvenLie.binary_linear_degree_le_five
        h.simpleQTKE.quasithin hmodel
      omega

end CFSG.Quasithin.Chapter12.Section09
