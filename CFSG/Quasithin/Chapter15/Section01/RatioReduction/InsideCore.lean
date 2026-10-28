module
public import CFSG.Quasithin.Chapter3.Section01.ReducedModuleSylow
public import CFSG.Quasithin.ChapterD.Section01.SourceMultiple
public import CFSG.Quasithin.Chapter15.Section01.NormalizerSource
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SmallRatio
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.LocalAction

/-!
# The original inside-core ratio bound in the centralizing branch

The normalizer of C_T(V(M)) has solvable action on V(M), by the actual
empty faithful-component hypothesis and 14.1.6. Thus its dual-FF branch
has quadratic ratio at most two. The actual SQTK right-hand local group
supplies the multiple-chief-factor bound; the remaining unique-factor
branch contradicts the common-normal theorem through its reduced module.
No solvability assumption is made on that right-hand local group.
Source: Aschbacher--Smith 3.1.6 and 15.1.1(2), pp.573--575,1083--1084.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]
theorem sourceNormalizer_actionImage_isSolvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hn : sourceNormalizer T M ≤ normalizer (localModule T M : Set G)) :
    Group.IsSolvable (internalActionImage (sourceNormalizer T M) (localModule T M) hn) := by
  let f := actionHom (sourceNormalizer T M) (localModule T M) hn
  have hr := residual_le_centralizer_localModule
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty (sourceNormalizer_mem_H hG T hM.1)
  rw [sourceNormalizer_module_eq T hM.1.2] at hr
  have hk : solvableResidual (sourceNormalizer T M) ≤ f.ker := by
    rw [actionHom_ker]
    exact fun _ hx => hr (mem_map_of_mem _ hx)
  have hz : solvableResidual f.range = ⊥ := by
    rw [←map_solvableResidual_eq f.rangeRestrict f.rangeRestrict_surjective]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [MonoidHom.ker_rangeRestrict] using hk)
  obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := f.range)
  exact ⟨n,hn.trans hz⟩

theorem source_insideCore_quadraticRatio_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : localModule T M ≤ twoCoreIn H) :
    let d := source_15_1_1_qrcConfiguration hG T hM hH
    letI := d.module_elementary
    quadraticRatio (imageRepresentation (sourceNormalizer T M) (localModule T M)
      d.module_normalized) ≤ 2 := by
  let h := source_lemma_15_1_1_1 hG T hM hH
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  let ρ := imageRepresentation (sourceNormalizer T M) (localModule T M) d.module_normalized
  have hne : localModule T M ≠ ⊥ := by
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1
      (bot_unique ((le_conjugateSpanBy _ _).trans he.le))
  by_cases hff : IsFFModule ρ
  · exact ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff).trans (by norm_num)
  let := source_elementary_span_of_notFF d hV hff
  let U := (conjugateSpan H (localModule T M)).subgroupOf H
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hn := noncentralCount_ne_zero d hne hV s
  by_cases hc : s.noncentralCount = 1
  · have hu : HasUniqueNoncentralChiefFactor H (localModule T M) := ⟨s,hc⟩
    rcases source_dualFF_or_coreClosure_centralizes d hV hu with hd | hc
    · exact ChapterB.SolvableDualFF.quadraticRatio_le_two ρ
        (sourceNormalizer_actionImage_isSolvable hG T hempty hM _)
        (sourceNormalizer_actionImage_reduced hG T hM.1)
        (imageRepresentation_injective _ _ _) hd
    · apply (h.not_uniqueFactor_coreClosure_centralizes hG hM.1.1 ?_ hJ hV hu hc).elim
      intro L hL hNL
      exact (ChapterA.Section05To06.lemma_A_5_7_1 hM h.sylow_le inf_le_left
        (sourceNormalizer_covers_action T hM.1.2) L hL).mp hNL
  · exact source_sqtk_multiple_ratio d hne hV
      (Chapter3.sqtk_of_mem_H hG hH.1.1.1) s (by omega)
end CFSG.Quasithin.Chapter15.Section01


