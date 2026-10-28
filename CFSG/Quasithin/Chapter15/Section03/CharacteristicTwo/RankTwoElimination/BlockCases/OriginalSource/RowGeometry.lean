module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry

/-!
# Marked row geometry in the original rank-two source configuration

The literal original hypotheses produce the C.2.7 input on I and M intersect I.
The actual B.5 rank-one row then supplies the Sylow and concrete block premises
for 15.3.18–19. A symplectic star marking supplies the full point-or-plane
parabolic for 15.3.20. These are applications to the original component and
quotient maps; the remaining B.5 rows and eliminations remain separate.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
include hG hempty hM hu hmany hI htwo hf

/-- The original C-component and actual Sylow conclusion leave exactly
 the two concrete block cases used by 15.3.18–19. -/
theorem source_15_3_16_blocks_of_radical_sylow
    (hs : Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R)) :
    (∃ n, ChapterC.IsL2EvenBlock c.L n) ∨ ChapterC.IsAlternatingBlock c.L 5 := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  exact ChapterC.C27Source.source_rankOne_blocks_of_sylow h hs

/-- The source symplectic marking determines the actual full parabolic in M*. -/
theorem source_15_3_16_symplectic_parabolic
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage c.L d.R c.L ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hq : 4 ≤ Nat.card F) :
    ∃ g : Theory.SpecificGroups.SymplecticFour.Sp F,
      (((starM c.L d.R (d.MI I)).subgroupOf (starImage c.L d.R c.L)).map
          e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
          Theory.SpecificGroups.SymplecticFour.pointParabolic ∨
      (((starM c.L d.R (d.MI I)).subgroupOf (starImage c.L d.R c.L)).map
          e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
          Theory.SpecificGroups.SymplecticFour.planeParabolic := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  exact ChapterC.C27Source.star_symplectic_marked_parabolic_from_source h e hq
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
