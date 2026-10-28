module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneFour
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks

/-!
# The actual B.5 rank-one row in the original rank-two argument

The original C.2.7 geometry derives the literal Sylow and Borel markings
from the best offenders in the B.5 row. The source 15.3.18–19 exclusion
then applies to the original component, with no reconstructed module or
extra Sylow premise. This is the linear-two row consumer for 15.3.13.

Source: Aschbacher–Smith C.2.7(3)(a), pp.145–147, and 15.3.18–19,
printed pp.1126–1127.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The concrete linear-two action row, including its literal best offenders,
is impossible under the original source hypotheses. -/
theorem source_15_3_18_linearTwo_row
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (F : BinaryField),
      ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (linearNatural F 2) →
      quadraticRatio s.action = 1 →
      (∀ B, IsBestOffender s.action B → ∃ S : Sylow 2 (C.subgroupOf J),
        B = (S : Subgroup _).map (C.subgroupOf J).subtype) → False := by
  intro C J hCJ s F natural hratio hoff
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨_,hb,hs⟩ := ChapterC.C27Source.rankOne_row_geometry_from_source
    h hCJ s F natural hratio hoff
  exact source_rankOne_row_exclusion hG d hempty hM hu hmany hI htwo hf c hs hb
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
