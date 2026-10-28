module
public import CFSG.Quasithin.ChapterC.Section01.ExtraspecialCoreObstruction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Quasithin.EvenCharacteristic
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core

/-!
# The first Janko-four centralizer as an alternating-five escape

The literal first involution centralizer has a self-centralizing extraspecial
two-core. The general short-component obstruction therefore excludes an
alternating-five block from its local C-components at every full Sylow.
No faithful projection through its solvable radical is required.

This is the native centralizer leaf used in Aschbacher--Smith 2.4.25,
printed p.543; transport of the original block to this centralizer is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal.JankoFour
open Janko4.InvolutionCentralizers.First
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
/-- The literal first centralizer needs no faithful image assumption on the block. -/
theorem first_not_local_alternating_five
    (A : Subgroup centralizer) (hA : ChapterC.IsAlternatingBlock A 5)
    (S : Sylow 2 centralizer) : A ∉ ChapterA.Section03.localCComponents S := by
  let : IsExtraspecial 2 (pCore 2 centralizer) := centralizer_twoCore_extraspecial
  apply ChapterC.not_local_short_of_extraspecial_twoCore ?_ S A hA.2.1
  exact (@Theory.Quasithin.centralizer_pCore_le_iff centralizer
    Janko4.OuterReduction.FixedGenerator.NormalizerSquares.involutionCentralizer
    inferInstance inferInstance 2 centralizerEquiv).mpr
    Janko4.OuterReduction.FixedGenerator.NormalizerSquares.localTwoCoreCentralizerControl.1
end CFSG.Quasithin.Chapter2.AlternatingTerminal.JankoFour
