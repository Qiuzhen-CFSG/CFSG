module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingFiveQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingFiveStarCover
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction

/-!
# Excluding the actual symmetric-five source row

The component marking in the original B.5 symmetric-five row identifies
its literal star image with A5. The proved A5 covering kernel has order two,
so the star map is injective on the component modulo its two-core. Original
15.3.12 then places a Sylow subgroup in the radical. The source C.1.29
recognition and the original 15.3.18–19 contradictions exclude this quotient.

This closes the raw symmetric-five row without a block reconstruction or
an extra condition on the kernel of the local module action. Source:
Aschbacher–Smith 15.3.16–19, printed pp.1126–1127; B.5.7 and C.1.29.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
include hG hempty hM hu hmany hI htwo hf

/-- Original source hypotheses exclude an A5 model of the literal star component. -/
theorem source_15_3_19_alternatingFive_star
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 5)) : False := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨a⟩ := core_quotient_alternatingFive_of_star d c h.normalizes e
  exact source_15_3_19_alternatingFive_quotient hG d hempty hM hu hmany hI htwo hf c a

/-- The actual symmetric-five marked row is impossible. Its component marking
alone supplies the star model; all cover and block premises are discharged. -/
theorem source_15_3_19_symmetricFive_row :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      MarkedActionEquiv s.action (offenderSubgroup s.action) (C.subgroupOf J)
        (BinaryPermutation.naturalRepresentation (Fin 5))
        (alternatingGroup (Fin 5)) → False := by
  intro C J hCJ s e
  exact source_15_3_19_alternatingFive_star hG d hempty hM hu hmany hI htwo hf c
    ((subgroupOfEquivOfLe hCJ).symm.trans e.subgroupEquiv)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
