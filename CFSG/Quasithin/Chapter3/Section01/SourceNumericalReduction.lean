module
public import CFSG.Quasithin.Chapter3.Section01.ReducedModuleSylow
public import CFSG.Quasithin.Chapter3.Section01.OffenderBranch
public import CFSG.Quasithin.ChapterD.Section01.SourceMultiple
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
/-!
# The two remaining numerical branches of the source qrc theorem

An original reduced qrc configuration with unique maximal two-local
has quadratic ratio at most two in the inside-core case, unless its
literal conjugation action is dual-FF. Thompson movement gives an FF
actor. Otherwise, a chief series has either multiple noncentral factors,
where the proved SQTK ratio bound applies, or exactly one. In the latter
case the reduced-module Sylow argument excludes a centralizing closure.

The resulting cubic alternative isolates precisely the separate B.5.13
and outside-core E.2.13 numerical inputs. It does not assert either input
or the complete 3.1.6--8 ratio theorem. Source: Aschbacher--Smith 3.1.6,
printed pp.573--575.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.quadraticRatio_le_two_or_dualFF
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H) :
    letI := h.module_elementary
    quadraticRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      DualFF (h.toQRCConfiguration (h.no_common_normal hu)) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := h.module_elementary
  let ρ := imageRepresentation M₀ V h.module_normalized
  by_cases hff : IsFFModule ρ
  · exact Or.inl (((isFFModule_iff_quadraticRatio_le_one ρ).mp hff).trans (by norm_num))
  have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
    by_contra hj
    apply hff
    exact internalActionImage_isFFModule_of_thompson_not_le T M₀ V h.sylow_le
      (d.module_le_core.trans (left_core_le_sylow d)) h.module_normalized hj
  let := source_elementary_span_of_notFF d hV hff
  let U := (conjugateSpan H V).subgroupOf H
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hn := noncentralCount_ne_zero d hne hV s
  by_cases hc : s.noncentralCount = 1
  · have huf : HasUniqueNoncentralChiefFactor H V := ⟨s,hc⟩
    rcases source_dualFF_or_coreClosure_centralizes d hV huf with hd | hcentral
    · exact Or.inr hd
    · exact (h.not_uniqueFactor_coreClosure_centralizes hG hM hu hJ hV huf hcentral).elim
  · exact Or.inl (source_sqtk_multiple_ratio d hne hV
      (sqtk_of_mem_H hG h.right_mem.1.1.1) s (by omega))

theorem QrcHypotheses.cubicRatio_le_two_or_source_branch
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      (¬ V ≤ twoCoreIn H) ∨ DualFF (h.toQRCConfiguration (h.no_common_normal hu)) := by
  let := h.module_elementary
  by_cases hV : V ≤ twoCoreIn H
  · rcases h.quadraticRatio_le_two_or_dualFF hG hM hu hne hV with hq | hd
    · exact Or.inl ((cubicRatio_le_quadraticRatio _).trans hq)
    · exact Or.inr (Or.inr hd)
  · exact Or.inr (Or.inl hV)
end CFSG.Quasithin.Chapter3
