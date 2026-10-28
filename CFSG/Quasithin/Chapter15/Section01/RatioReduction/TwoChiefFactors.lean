module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.InsideCore
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SQTKEquality
/-!
# The selected two-chief-factor consequence in 15.1.12

The original normalizer and outside local group give the literal qrc
configuration. Zero noncentral factors are impossible; one factor gives the
dual-FF alternative or contradicts the genuine common-normal theorem through
the reduced residual module. The SQTK equality theorem then forces exactly
two factors in every actual chief series.

The earlier inside-core, nondual-FF and ratio-two source conclusions remain
explicit: these are supplied by 15.1.7--8 and 15.1.11 in the final centralizing
branch, whose classification is separate from this numerical theorem.
Source: Aschbacher--Smith 15.1.12(1), printed pp.1089--1090.
-/
public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal

namespace CFSG.Quasithin.Chapter15.Section01
open Theory.GroupTheory Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The genuine numerical part of 15.1.12, with the earlier inside-core and
nondual-FF source conclusions left explicit. -/
theorem source_centralizing_noncentral_count_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : localModule T M ≤ twoCoreIn H)
    (hdual : ¬ DualFF (source_15_1_1_qrcConfiguration hG T hM hH))
    (hq : let d := source_15_1_1_qrcConfiguration hG T hM hH
      letI := d.module_elementary
      quadraticRatio (imageRepresentation (sourceNormalizer T M) (localModule T M)
        d.module_normalized) = 2)
    (s : SeriesOn ((conjugateSpan H (localModule T M)).subgroupOf H)) :
    s.noncentralCount = 2 := by
  let h := source_lemma_15_1_1_1 hG T hM hH
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  have hne : localModule T M ≠ ⊥ := by
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1
      (bot_unique ((le_conjugateSpanBy _ _).trans he.le))
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H (localModule T M)).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  have hn := noncentralCount_ne_zero d hne hV s
  have hnotone : s.noncentralCount ≠ 1 := by
    intro hc
    have hu : HasUniqueNoncentralChiefFactor H (localModule T M) := ⟨s,hc⟩
    rcases source_dualFF_or_coreClosure_centralizes d hV hu with hd | hc
    · exact hdual hd
    · apply h.not_uniqueFactor_coreClosure_centralizes hG hM.1.1 ?_ hJ hV hu hc
      intro L hL hNL
      exact (ChapterA.Section05To06.lemma_A_5_7_1 hM h.sylow_le inf_le_left
        (sourceNormalizer_covers_action T hM.1.2) L hL).mp hNL
  have hc : 1 < s.noncentralCount := by omega
  let S := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  obtain ⟨A,hA,hAR,hquad⟩ := source_quadratic_max_actor d hne hV hnf S hS
  have hnc : ¬ A ≤ centralizer (U : Set H) := by
    intro ha
    exact hAR ((le_inf hA.1 ha).trans
      (source_span_centralizer_sylow_le_core d hne hV hnf S hS))
  exact (source_sqtk_multiple_equalities d hne hV
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) hq S hS s hc A hA hquad hnc).1
end CFSG.Quasithin.Chapter15.Section01