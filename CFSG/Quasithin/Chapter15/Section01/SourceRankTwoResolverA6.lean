module
public import CFSG.Quasithin.Chapter15.Section01.SourceRankTwoResolverSolvable
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction

/-!
# Rank-two resolver with the checked A₆ rank-three branch

The nonabelian branch is consumed through the solvability-only adapter.  The
independent rank-three premise is reduced to the literal alternating-six
whole-core reconstruction, while the terminal witness remains explicit for
14.6.25.  All selected subgroups, the singleton-centralizer hypothesis and
the original conjugate span are retained.

Source: Aschbacher--Smith, 14.6.10(5), 14.6.25 and 15.1.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 ChapterA.Section05To06 Chapter12.Section08 Chapter14.SourcePreliminaries
open Chapter14.Section06
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal resolver after composing the checked nonabelian assembly with
the completed binary/seven/G₂ rank-three branches.  The only rank-three
source input left here is the genuine A₆ whole-core reconstruction; terminal
solvability and the terminal witness remain independent premises. -/
theorem source_rankTwoResolver_of_solvable_a6_source_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hsolvable : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      (¬ ClassificationModels.IsTheoremEModel G →
        ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
        ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot))
    (hwitness : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
      ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab) :
    RankTwoResolver T Mc := by
  apply source_rankTwoResolver_of_solvable_source_inputs hG T hempty hunique hmany
    (fun M hM hne hrank => hsolvable M hM hne hrank)
    ?_ hwitness
  intro M hM hne hcard e hab
  exact source_second_parabolic_rank_three_of_a6_reconstruction
    hG T hempty hM hunique hmany hcard e hab ha

end CFSG.Quasithin.Chapter15.Section01
