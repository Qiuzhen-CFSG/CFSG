module
public import CFSG.Quasithin.Chapter3.Section01.ReducedModuleSylow
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.StrictChief

/-!
# A small-ratio chief factor in the original qrc configuration

The common-normal source theorem excludes a unique noncentral chief factor
when the original action is not dual-FF. Nontriviality excludes zero factors.
If the original quadratic ratio is at least four thirds, the strict D.1.3
estimate then supplies an actual noncentral chief factor with ratio at most
two. The span, series, actions, and local uniqueness are the original ones.

Source: Aschbacher--Smith3.1.6 and D.1.3, printed pp.573--575 and173--175.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.two_le_noncentralCount_of_not_dualFF
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) : 2 ≤ s.noncentralCount := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  have hn := noncentralCount_ne_zero d hne hV s
  have hnotone : s.noncentralCount ≠ 1 := by
    intro hc
    have hh : HasUniqueNoncentralChiefFactor H V := ⟨s,hc⟩
    rcases source_dualFF_or_coreClosure_centralizes d hV hh with hd | hc
    · exact hdual hd
    · exact h.not_uniqueFactor_coreClosure_centralizes hG hM hu hJ hV hh hc
  omega

theorem QrcHypotheses.exists_noncentral_chief_ratio_le_two_of_four_thirds
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hnf : letI := h.module_elementary
      ¬ IsFFModule (imageRepresentation M₀ V h.module_normalized))
    (hq : letI := h.module_elementary
      (4 / 3 : ℝ≥0∞) ≤ quadraticRatio (imageRepresentation M₀ V h.module_normalized))
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu))) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := source_elementary_span_of_notFF d hV hnf
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∃ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i ∧
      quadraticRatio (Representation.BinaryOffender.imageRepresentation
        (s.factorRepresentation i)) ≤ 2 := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let U := (conjugateSpan H V).subgroupOf H
  let := source_elementary_span_of_notFF d hV hnf
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  dsimp only
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hc := h.two_le_noncentralCount_of_not_dualFF hG hM hu hJ hne hV hdual s
  obtain ⟨i,hi,hr⟩ := source_exists_chief_ratio_le_two_of_four_thirds
    d hne hV hnf hq s (by omega)
  exact ⟨s,i,hi,hr⟩

end CFSG.Quasithin.Chapter3
