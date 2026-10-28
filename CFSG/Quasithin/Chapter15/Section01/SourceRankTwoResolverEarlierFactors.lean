module

public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625EarlierFactors
public import CFSG.Quasithin.Chapter15.Section01.SourceTheorem1513

/-!
# The literal 15.1.3 resolver after the original solvable-containment argument

Apply the fixed-M 14.6.25 theorem to each actual ordering-maximal subgroup
in RankTwoResolver. The earlier exchanged factors supply 14.6.18 on that same
M; the independent A6, nonabelian and mixed-size source premises are retained.
The final application feeds the literal 15.1.3 branch-resolver theorem.
Source: Aschbacher--Smith, 14.6.25 and 15.1.3, printed pp.1042,1086--1089.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 ChapterA.Section05To06 Chapter12.Section08 Chapter14.SourcePreliminaries
open Chapter14.Section06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact rank-two resolver consumed by the 15.1.3 branch, with the earlier
factor family replacing the proved solvable-containment premise. -/
theorem source_rankTwoResolver_of_earlier_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hterminal : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      (¬ ClassificationModels.IsTheoremEModel G →
        ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
        ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
          Group.IsSolvable F.TerminalHdot))
    (h12 : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
        SourceExchangedFactorFamily T M)
    (size : Chapter10.MixedZeroCore.MixedSizeInput G) :
    RankTwoResolver T Mc := by
  intro M hM hne hrank
  exact Chapter14.Section06.source_theorem_14_6_25_of_earlier_factors
    hG T hempty hM hunique hmany hrank ha
    (hterminal M hM hne hrank) (h12 M hM hne hrank) size

/- The rank-two adapter feeds the literal 15.1.3 branch boundary.  Keeping
the centralizing resolver explicit records the one independent Baumann branch
that this source family does not discharge. -/
theorem source_lemma_15_1_3_of_earlier_rank_two_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hterminal : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      (¬ ClassificationModels.IsTheoremEModel G →
        ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
        ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
          Group.IsSolvable F.TerminalHdot))
    (h12 : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
        SourceExchangedFactorFamily T M)
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (hcentral : CentralizingResolver T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  apply source_lemma_15_1_3_of_branch_resolvers hG T hempty hunique hmany
    (source_rankTwoResolver_of_earlier_factors hG T hempty hunique hmany
      ha hterminal h12 size)
    hcentral

end CFSG.Quasithin.Chapter15.Section01
