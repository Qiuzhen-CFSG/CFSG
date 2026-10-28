module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicReduction

/-!
# Original 15.1.14 for the full Nine action

For the literal four-dimensional Nine action, strict inclusion of the
Thompson image produces the original cubic six-point source. Its marked
four-group identifies M_Z with the full fixed-group centralizer, so the
proved cubic exclusion applies. The Thompson and Sylow images consequently
agree. Their fixed group is the original central seed intersected with V;
the seed centralizer fixes it pointwise, giving the requested normalization
and all four original 15.1.14 clauses.

Every hypothesis is original source data. There is no residual, strict-image,
whole-core reconstruction, or Sylow-radical premise.

Source: Aschbacher--Smith 15.1.14--26, printed pp.1091--1102.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Strict Thompson-image inclusion is impossible for the original full
Nine source, by the actual marked cubic-component exclusion. -/
theorem PreparedChosenModule.nine_thompson_image_eq_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict := by
  have hle : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict ≤
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict :=
    map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))
  rcases hle.eq_or_lt with he | hs
  · exact he
  obtain ⟨d,hr,_,s,g,_,_,_,hz,hi,hms,_,_,t,_⟩ :=
    h.nine_cubic_source_without_residual hG T hempty hM hmany hJ hu hne hfull h9 hs
  obtain ⟨_,_,_,hMZ,_⟩ :=
    h.nine_marked_core_geometry hG T hempty hM hmany hJ hu hne hfull h9 hs d hr g
  let := h.elementary
  let : IsElementaryAbelian 2 (thompsonFixed T V) := IsElementaryAbelian.of_le inf_le_left
  exact (s.false_of_cubic_marked_source (h := h) hG hM hu hi hms
    (thompsonFixed T V) hMZ t hz).elim

/-- The full original centralizer normalizes the actual Thompson fixed
group in the Nine row, without a residual-centralization assumption. -/
theorem PreparedChosenModule.nine_full_centralizer_normalizes_thompsonFixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T V : Set G) := by
  rw [h.thompsonFixed_eq_seed_of_image_eq T hM
    (h.nine_thompson_image_eq_sylow hG T hempty hM hmany hJ hu hne hfull h9)]
  exact (centralizer_le inf_le_left).trans (centralizer_le_normalizer _)

/-- All four clauses of original 15.1.14 for the literal full Nine row. -/
theorem PreparedChosenModule.source_lemma_15_1_14_of_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T V : Set G) ∧
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
      normalizer (thompsonFixed T V : Set G) ∧
    normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
    normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc :=
  h.source_lemma_15_1_14_of_image_eq hG T hM hJ hu
    (h.nine_thompson_image_eq_sylow hG T hempty hM hmany hJ hu hne hfull h9)

end CFSG.Quasithin.Chapter15.Section01
