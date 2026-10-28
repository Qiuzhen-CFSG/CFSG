module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryFourSmallDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier

/-!
# Original degree-four exclusion with the earlier source discharged

The natural-plus-dual source residual has small displacement in its literal
central point line. The existing displacement exclusion therefore applies
once the original critical-path replacement has been constructed. That
construction is now proved by `Source44.Replacement.OriginalSource`, so the
degree-four branch of 15.3.24 has no remaining MS classification premise.

The argument keeps the full component quotient and the original natural and
dual summands. It does not identify the original two-core action with the
action of the characteristic replacement.

Source: Aschbacher--Smith 15.3.24, printed pp.1129--1130;
Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5).
-/

public section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearFourFive NaturalDualParabolic NaturalDualParabolic.Realization
open ChapterC ChapterC.BinaryMS ChapterC.BinaryMS.MS93
open ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {L I : Subgroup G}

/-- The actual natural-plus-dual residual is impossible, with its prescribed
replacement supplied by the proved earlier source argument. -/
theorem source_binaryFour_false_of_original_source
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : Input KnownSimple.IsKnownSimple (residualComponent h x) (sylowPart h x)) :
    False := by
  apply source_binaryFour_false_of_replacement h hx hS hθ input
  intro t common hb a a' p hp
  exact Source44.Replacement.OriginalSource.prescribedReplacement common hb p hp

/-- Original 15.3.24 in degree four, retaining only its original selection,
characteristic-two and full component-quotient hypotheses. -/
theorem source_lemma_15_3_24_four_of_original_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(4,ZMod 2)) : False := by
  apply source_lemma_15_3_24_four_of_replacement hG d hempty hM hu hmany hI htwo hf c e
  intro h x hx input t common hb a a' p hp
  exact Source44.Replacement.OriginalSource.prescribedReplacement common hb p hp

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
