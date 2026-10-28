module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.PreparedExits
public import CFSG.Quasithin.Chapter15.Section01.SourceTheorem1513

/-!
# Conditional assembly of the centralizing branch of 15.1.3

The prepared source partition leaves the rank-two and natural orthogonal
conclusions, the three large actions of 15.1.15, and the chosen small actions
of Section 15.2. The latter two branches retain the original chosen subgroup
and its literal conjugation image. The residual input is precisely 15.1.14(1);
its normalizer consequences are proved by the existing chosen-module theorem.

The proofs of global residual centralization, the large-action exclusion,
and the small-action contradiction remain explicit inputs. This module proves
their conditional assembly. The final application uses 15.1.3 only at the
actual singleton centralizer, with its rank-two resolver.

Source: Aschbacher--Smith 15.1.3--4, 15.1.14--15, and Section 15.2,
printed pp.1086--1087, 1091--1092, and 1104ff.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The remaining global residual assertion on each literal source choice. -/
abbrev SourceGlobalThompsonResidualInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Mc : Subgroup G) : Prop :=
  ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    ∀ W : Subgroup G, SourceChosenOrigin T M Mc W → PreparedChosenModule T M W →
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T W : Set G)

/-- The large-action contradiction of 15.1.15 under the source counterexample
assumptions and the explicit preceding 15.1.14 conclusions. -/
abbrev SourceLargeChosenExclusionInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    ∀ hp : PreparedChosenModule T M (localModule T M),
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T (localModule T M) : Set G) →
      (M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
          normalizer (thompsonFixed T (localModule T M) : Set G) ∧
        normalizer (thompsonFixed T (localModule T M) : Set G) ≤ Mc ∧
        normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc) →
      ¬ LargeChosenAction T M (localModule T M) hp.normalized

/-- The Section 15.2 contradiction on the same chosen module and action,
under the source counterexample assumptions and preceding 15.1.14 conclusions. -/
abbrev SourceSmallChosenExclusionInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    ∀ W : Subgroup G, SourceChosenOrigin T M Mc W →
    ∀ hp : PreparedChosenModule T M W,
      letI := hp.elementary
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T W : Set G) →
      (M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
          normalizer (thompsonFixed T W : Set G) ∧
        normalizer (thompsonFixed T W : Set G) ≤ Mc ∧
        normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc) →
      ¬ SmallChosenAction M W hp.normalized

/-- Assemble the actual centralizing resolver from the prepared partition,
the rank-two resolver, and the three independently produced source inputs. -/
theorem source_centralizing_resolver_of_chosen_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hres : SourceGlobalThompsonResidualInput hG T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc)
    (hsmall : SourceSmallChosenExclusionInput hG T Mc) :
    CentralizingResolver T Mc := by
  classical
  intro M hM hne hJ _ _ _ _
  by_cases hmodel : ClassificationModels.IsTheoremEModel G
  · exact Or.inl hmodel
  by_cases hn : ∃ N : Subgroup G, IsOrderingMaximal T N ∧
      Nonempty (NaturalOrthogonalAction N (localModule T N))
  · exact Or.inr hn
  have hno : ∀ N : Subgroup G, IsOrderingMaximal T N →
      ¬ Nonempty (NaturalOrthogonalAction N (localModule T N)) :=
    fun N hN ho => hn ⟨N,hN,ho⟩
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  rcases source_prepared_chosen_exits hG T hempty hM hmany hJ hu hne with
    hr | ho | ⟨hp,hl⟩ | ⟨W,hW,hp,hs⟩
  · exact Or.inl (hrank M hM hne hr)
  · exact Or.inr ⟨M,hM,ho⟩
  · have hglobal := hres M hM hne hJ (localModule T M) (Or.inl rfl) hp
    have hnorm := hp.thompsonFixed_normalizers hG T hM hJ hu hglobal
    exact (hlarge hmodel hno M hM hne hJ hp hglobal hnorm hl).elim
  · have hglobal := hres M hM hne hJ W hW hp
    have hnorm := hp.thompsonFixed_normalizers hG T hM hJ hu hglobal
    exact (hsmall hmodel hno M hM hne hJ W hW hp hglobal hnorm hs).elim

/-- Apply the conditional centralizing resolver to the literal pointwise
15.1.3 consumer, after retaining its singleton-centralizer hypothesis. -/
theorem source_lemma_15_1_3_of_chosen_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hres : SourceGlobalThompsonResidualInput hG T Mc)
    (hlarge : SourceLargeChosenExclusionInput hG T Mc)
    (hsmall : SourceSmallChosenExclusionInput hG T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) :=
  source_lemma_15_1_3_of_branch_resolvers hG T hempty hu hmany hrank
    (source_centralizing_resolver_of_chosen_exclusions hG T hempty hu hmany
      hrank hres hlarge hsmall)

end CFSG.Quasithin.Chapter15.Section01
