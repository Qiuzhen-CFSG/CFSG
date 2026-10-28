module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual.ProperImageTwoDischarged
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SmallActionDischarged

/-!
# The original resolver after the proper-support Thompson branch

The prior-free Omega contradiction supplies normalization for the actual
proper chosen support. Together with the proved equal-image cases, this
leaves only the full local module in the global Thompson residual input.
The completed small-action theorem then feeds the original 15.1.3 resolver.
The full-module image gap, rank-two resolver and large-action exclusion
remain explicit source obligations.

Source: Aschbacher--Smith 15.1.3, 15.1.13--15 and 15.2.1--28,
printed pp.1086--1092 and 1104--1120, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The proper-support branch is discharged at the original singleton
centralizer, leaving precisely the full-module normalization input. -/
theorem source_counterexample_thompson_residual_of_full_image_gap
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : SourceFullThompsonImageGapInput T Mc) :
    SourceCounterexampleThompsonResidualInput hG T Mc :=
  source_counterexample_thompson_residual_of_image_gaps hG T hempty hmany hfull
    (source_proper_thompson_image_two hG T hempty hu hmany)

/-- The actual centralizing resolver with the small-action and
proper-support Thompson inputs constructed from the source hypotheses. -/
theorem source_centralizing_resolver_of_full_image_gap_and_large_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hfull : SourceFullThompsonImageGapInput T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc) :
    CentralizingResolver T Mc :=
  source_centralizing_resolver_of_residual_and_large_exclusion hG T hempty hu hmany
    hrank (source_counterexample_thompson_residual_of_full_image_gap
      hG T hempty hu hmany hfull) hlarge

/-- The original 15.1.3 alternatives, with only the full-module Thompson
gap, rank-two and large-action producers still required. -/
theorem source_lemma_15_1_3_of_full_image_gap_and_large_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hfull : SourceFullThompsonImageGapInput T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) :=
  source_lemma_15_1_3_of_branch_resolvers hG T hempty hu hmany hrank
    (source_centralizing_resolver_of_full_image_gap_and_large_exclusion
      hG T hempty hu hmany hrank hfull hlarge)

end CFSG.Quasithin.Chapter15.Section01
