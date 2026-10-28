module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Geometry
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Reduction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Exclusion

/-!
# The literal L₃ application of E.6.14 after stabilizer geometry

The original escaping U has a faithful cubic actor, and its normalizer in
LT is maximal of index eight. The common-normal input to E.6.13 is supplied
by known-simple 3.1.1 in Reduction. Exclusion now constructs single-block
selection and the C.5.7 index calculation for this same configuration and
exports the completed characteristicTwoExclusion. The conditional interfaces
below are retained for existing consumers.
Source: Aschbacher--Smith, E.6.14, printed p.251, and 12.4.8, p.815.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
open ChapterE ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- Pointwise E.6.14 application with the actual geometry discharged. -/
theorem false_of_block_inputs (c : Configuration T L V U)
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (selection : BlockSelection c) (index : BlockIndex c) : False :=
  false_of_inputs c hc c.stabilizer_geometry selection index

/-- The case contract now needs only its two local block arguments. -/
theorem characteristicTwoExclusion_of_block_inputs
    (selection : ∀ (G : Type u) [Group G] [Finite G]
      (T : Sylow 2 G) (L V U : Subgroup G) (c : Configuration T L V U), BlockSelection c)
    (index : ∀ (G : Type u) [Group G] [Finite G]
      (T : Sylow 2 G) (L V U : Subgroup G) (c : Configuration T L V U), BlockIndex c) :
    CharacteristicTwoExclusion.{u} := by
  intro G _ _ T L V U c hc
  exact false_of_block_inputs c hc (selection G T L V U c) (index G T L V U c)

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
