module

public import CFSG.Quasithin.Chapter15.Section01.SourceReduction

/-!
# The 15.1.3 assembly boundary

The selected-source reduction already constructs the three literal branches of
15.1.3.  This adapter packages the two remaining mathematical obligations at
that boundary: classification of the original rank-two hypothesis (the
14.6.25 input), and resolution of the centralizing Baumann branch.  It does
not weaken either branch to an abstract action or replace the original
centralizer data.

Source: Aschbacher--Smith 15.1.3 and 14.6.25, printed pp.1086--1089.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
open Chapter14.SourcePreliminaries Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact branch resolver needed to turn the selected rank-two branch into
the model conclusion used by the final Theorem E assembly. -/
abbrev RankTwoResolver (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ∀ M : Subgroup G, IsOrderingMaximal T M → M ≠ Mc →
    RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
    ClassificationModels.IsTheoremEModel G

/-- The exact centralizing resolver needed at the other 15.1.3 boundary.  The
Baumann tuple is the one constructed by `source_selected_reduction`; keeping
it explicit prevents a later consumer from silently strengthening the source
to a two-group or dropping the minimal-parabolic clauses. -/
abbrev CentralizingResolver (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ∀ M : Subgroup G, IsOrderingMaximal T M → M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    localModule T M ≤ thompsonAlpha (T : Subgroup G) →
    baumann (T : Subgroup G) =
      baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) →
    (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M →
    (∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      ChapterB.IsMinimalParabolicOver T H ∧
      IsSQTK KnownSimple.IsKnownSimple H ∧ generalizedFitting H = pCore 2 H) →
    ClassificationModels.IsTheoremEModel G ∨
      ∃ N : Subgroup G, IsOrderingMaximal T N ∧
        Nonempty (NaturalOrthogonalAction N (localModule T N))

private theorem selected_branch_resolver
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hcentral : CentralizingResolver T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  obtain ⟨M, hM, hne, _, hcases⟩ :=
    source_selected_reduction hG T hempty hu hmany
  rcases hcases with hr | ho | hc
  · exact Or.inl (hrank M hM hne hr.2.2)
  · exact Or.inr ⟨M, hM, ho⟩
  · rcases hc with ⟨hJ, hV, hB, hcontrol, hparabolic⟩
    exact hcentral M hM hne hJ hV hB hcontrol hparabolic

/-- Source 15.1.3 with its two genuine unresolved source obligations exposed.
The output is exactly the `h1513` contract consumed by
`Chapter15.source_theoremE_of_original_reductions`. -/
theorem source_lemma_15_1_3_of_branch_resolvers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hcentral : CentralizingResolver T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  exact selected_branch_resolver hG T hempty hu hmany hrank hcentral

/-- The universally quantified form needed by the final Theorem E source
assembly. -/
theorem source_lemma_15_1_3_h1513
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : ∀ Mc : Subgroup G, RankTwoResolver T Mc)
    (hcentral : ∀ Mc : Subgroup G, CentralizingResolver T Mc) :
    ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  intro Mc hu
  exact source_lemma_15_1_3_of_branch_resolvers hG T hempty hu hmany
    (hrank Mc) (hcentral Mc)

end CFSG.Quasithin.Chapter15.Section01
