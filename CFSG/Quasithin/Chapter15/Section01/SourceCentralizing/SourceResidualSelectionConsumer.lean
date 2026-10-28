module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFive

/-!
# The original resolver with only the surviving full-action normalization duties

The source row theorem removes full and proper Omega, both cubic whole
actions, the order-two Sylow-image cases and the Fitting-five quintic row.
Its surviving full-module alternatives suffice for the unchanged
counterexample Thompson residual input. The original proper-support
producer and small-action contradiction then supply the actual 15.1.3
consumer. Rank two and the subsequent large-action exclusion are retained.

The normalization duty below is restricted to the genuine large actions
and the marked quintic action with cyclic-four Sylow and cyclic-fifteen
Fitting subgroup. It is not a proof of those duties or of 15.1.3.

Source: Aschbacher--Smith 15.1.3, 15.1.7, 15.1.14--15 and Section 15.2,
printed pp.1086--1092 and 1104--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- Apply the reduced source rows to the literal original full/proper
counterexample resolver, preserving both original classification exits. -/
theorem source_lemma_15_1_3_of_remaining_full_normalization
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
          let ρ := imageRepresentation M V hp.normalized
          let S := ((T : Subgroup G).subgroupOf M).map
            (actionHom M V hp.normalized).rangeRestrict
          4 ∣ Nat.card D →
          ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
            (actionHom M V hp.normalized).rangeRestrict < S →
          (LargeChosenAction T M V hp.normalized ∨
            ∃ l : LocalGeneration (ρ.comp (Jhat ρ).subtype), DihedralMarking l 5 2 ∧
              Nonempty (S ≃* Multiplicative (ZMod 4)) ∧
              Nonempty (fittingSubgroup D ≃* Multiplicative (ZMod 15))) →
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
      (source_full_residual_failure_large_or_fifteen hG T hempty hM hmany hJ hu hne
        (hno M hM) hp hnot))
  have hres : SourceCounterexampleThompsonResidualInput hG T Mc :=
    source_counterexample_thompson_residual_of_full_image_gap hG T hempty hu hmany hfull
  exact source_lemma_15_1_3_of_residual_and_large_exclusion hG T hempty hu hmany hrank hres hlarge

end CFSG.Quasithin.Chapter15.Section01
