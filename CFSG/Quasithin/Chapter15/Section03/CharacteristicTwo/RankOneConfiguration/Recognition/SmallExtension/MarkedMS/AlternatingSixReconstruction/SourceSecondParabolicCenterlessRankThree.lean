module

public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.MSBridge
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Exhaustion.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# The original centerless A₆ second-parabolic branch

The actual generated component and first radical satisfy the MS hypotheses.
For a centerless two-core quotient, the proved natural exhaustion theorem
reconstructs the entire commutator core. This gives an alternating-six block
on the same component, so the original source crossing argument computes
rank three for the second-parabolic span.

No whole-core reconstruction input or Sylow premise on the first radical
is assumed. The cubic-center branch remains separate.
Source: Aschbacher--Smith 14.6.10(5), pp.1029--1030, and C.1.31--32,
pp.135--136; MS93 (3.6), (5.12), and Section 7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The actual centerless A₆ source row has second-parabolic rank three,
with natural whole-core reconstruction discharged by the proved MS argument. -/
theorem source_second_parabolic_a6_centerless_rank_three :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ centralPreimage (pCore 2 C)) ≃*
        alternatingGroup (Fin 6)) ∧ center (C ⧸ pCore 2 C) = ⊥) := by
  intro H hH d I hI hpreferred he
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hi,hr,_⟩ := source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  let es := he.1.some.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  have hms := smallMSPair_from_c27 hi hr (Or.inr (Or.inl ⟨es⟩))
  obtain ⟨hel,hcentral,hmodel⟩ :=
    Natural.Exhaustion.LargeDistance.naturalCore_of_distanceFour_knownSimple
      Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.distanceFourInput_knownSimple
      G _ _ hms es he.2
  have hblock : ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 6 :=
    ⟨by decide,hms.short_of_core hel hcentral hi.quasisimple
      hmodel.alternating_six_irreducible,hmodel⟩
  exact source_second_parabolic_rank_three_of_alternating_block
    hG T hempty hM hunique hmany hcard e hab H hH d I hI hpreferred hblock

end CFSG.Quasithin.Chapter14.Section06
