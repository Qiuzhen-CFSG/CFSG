module

public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625TerminalComplete
public import CFSG.Quasithin.Chapter15.Section01.SourceTheorem1513

/-!
# Original rank-two resolution after terminal completion

The genuine nonabelian terminal solvability theorem removes that premise
from the original 15.1.3 resolver. The actual alternating-six reconstruction,
exchanged-factor family, and separate centralizing resolver remain explicit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 ChapterA.Section05To06 Chapter12.Section08 Chapter14.SourcePreliminaries
open Chapter14.Section06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact rank-two resolver consumed by the 15.1.3 branch, with the original
mixed-size bound supplied and the earlier source families retained. -/
theorem source_rankTwoResolver_after_terminal_completion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (h12 : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
        SourceExchangedFactorFamily T M) :
    RankTwoResolver T Mc := by
  intro M hM hne hrank
  exact Chapter14.Section06.source_theorem_14_6_25_after_terminal_completion
    hG T hempty hM hunique hmany hrank ha
    (h12 M hM hne hrank)

/- The rank-two adapter feeds the literal 15.1.3 branch boundary.  Keeping
the centralizing resolver explicit records the one independent Baumann branch
that this source family does not discharge. -/
theorem source_lemma_15_1_3_after_rank_two_terminal_completion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (h12 : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
        SourceExchangedFactorFamily T M)
    (hcentral : CentralizingResolver T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  apply source_lemma_15_1_3_of_branch_resolvers hG T hempty hunique hmany
    (source_rankTwoResolver_after_terminal_completion hG T hempty hunique hmany
      ha h12)
    hcentral

end CFSG.Quasithin.Chapter15.Section01
