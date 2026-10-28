module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFifteenExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionConsumer

/-!
# Removing the cyclic-fifteen row from the original full residual gap

The full marked-five row is contradictory by the original third-local
fixed-plane and rank argument. Thus any failure of the global Thompson
residual assertion on the full chosen module has one of the original
three large actions. The final original 15.1.3 consumer consequently
requires normalization only in those large rows, retaining the unchanged
full/proper source producers, rank-two duty, and large-action exclusion.

This removes the marked cyclic-fifteen duty. It does not prove the remaining
large-row normalization duties or the classification conclusion outright.
Source: Aschbacher--Smith 15.1.3, 15.1.14 and Section 15.2,
printed pp.1086--1091 and 1104--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- Only the genuine large actions can support a full-module failure of
original 15.1.14. The marked cyclic-fifteen row is independently excluded. -/
theorem source_full_residual_failure_large
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hno : ¬ Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (hp : PreparedChosenModule T M (localModule T M))
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T (localModule T M) : Set G)) :
    letI := hp.elementary
    LargeChosenAction T M (localModule T M) hp.normalized := by
  let := hp.elementary
  rcases source_full_residual_failure_large_or_fifteen hG T hempty hM hmany hJ hu hne hno hp hnot
      with hlarge | ⟨l,hl,hs,_⟩
  · exact hlarge
  · have hpm : PrimeDimensionOptions 5 2 :=
      (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
    let h : Section02.ChosenSmallSource T M Mc (localModule T M) :=
      ⟨hG,hempty,hM,hmany,hJ,hu,hne,hp,Or.inl rfl,Or.inl ⟨l,5,2,hpm,hl⟩⟩
    have hfour : Nat.card (((T : Subgroup G).subgroupOf M).map
        (actionHom M (localModule T M) hp.normalized).rangeRestrict) = 4 := by
      rw [Nat.card_congr hs.some.toEquiv]
      norm_num [Nat.card_eq_fintype_card]
    exact (Section02.source_chosen_full_marked_five_contradiction h ⟨l,hl⟩ hfour rfl).elim

/-- Apply the reduced source rows to the literal original full/proper
counterexample resolver, preserving both original classification exits. -/
theorem source_lemma_15_1_3_of_large_full_normalization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hremaining : ¬ ClassificationModels.IsTheoremEModel G →
      (∀ N : Subgroup G, IsOrderingMaximal T N →
        ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
      ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
        elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
        ∀ hp : PreparedChosenModule T M (localModule T M),
          letI := hp.elementary
          let V := localModule T M
          let D := internalActionImage M V hp.normalized
          let S := ((T : Subgroup G).subgroupOf M).map
            (actionHom M V hp.normalized).rangeRestrict
          4 ∣ Nat.card D →
          ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
            (actionHom M V hp.normalized).rangeRestrict < S →
          LargeChosenAction T M V hp.normalized →
          centralizer (centralInvolutions T : Set G) ≤
            normalizer (thompsonFixed T V : Set G))
    (hlarge : SourceLargeChosenExclusionInput hG T Mc) :
    ClassificationModels.IsTheoremEModel G ∨
      ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  have hfull : SourceFullThompsonImageGapInput T Mc := by
    intro hmodel hno M hM hne hJ hp hfour hlt
    by_contra hn
    have hnot := mt (hp.thompsonFixed_residual_iff_normalizes hG T hM hJ).mp hn
    exact hn (hremaining hmodel hno M hM hne hJ hp hfour hlt
      (source_full_residual_failure_large hG T hempty hM hmany hJ hu hne
        (hno M hM) hp hnot))
  have hres : SourceCounterexampleThompsonResidualInput hG T Mc :=
    source_counterexample_thompson_residual_of_full_image_gap hG T hempty hu hmany hfull
  exact source_lemma_15_1_3_of_residual_and_large_exclusion hG T hempty hu hmany hrank hres hlarge

end CFSG.Quasithin.Chapter15.Section01
