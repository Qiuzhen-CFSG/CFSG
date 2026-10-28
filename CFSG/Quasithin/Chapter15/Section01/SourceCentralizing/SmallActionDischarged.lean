module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.SmallSourceDirect
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual

/-!
# The 15.1.3 resolver after the small-action contradiction

The completed Section 15.2 argument supplies the small-action exclusion for
the same chosen module, including a proper support. Substituting it into
the prepared partition leaves the Thompson residual input under the original
counterexample hypotheses, the large-action exclusion and the rank-two resolver.
The source model and natural-orthogonal alternatives are preserved.

Source: Aschbacher--Smith 15.1.3, 15.1.14--15 and 15.2.1--28,
printed pp.1086--1092 and 1104--1120, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The completed small-action source supplies the corresponding branch of
the centralizing resolver at its original singleton centralizer. -/
theorem source_centralizing_resolver_of_residual_and_large_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hres : SourceCounterexampleThompsonResidualInput hG T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc) :
    CentralizingResolver T Mc :=
  source_centralizing_resolver_of_counterexample_residual hG T hempty hu hmany
    hrank hres hlarge (Section02.source_smallChosenExclusion hG T hempty hu hmany)

/-- The literal 15.1.3 endpoint after discharging its small-action premise.
The three remaining source inputs retain their independent producers. -/
theorem source_lemma_15_1_3_of_residual_and_large_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hres : SourceCounterexampleThompsonResidualInput hG T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) :=
  source_lemma_15_1_3_of_branch_resolvers hG T hempty hu hmany hrank
    (source_centralizing_resolver_of_residual_and_large_exclusion
      hG T hempty hu hmany hrank hres hlarge)

end CFSG.Quasithin.Chapter15.Section01
