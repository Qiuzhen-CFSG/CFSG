module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LinearThree.CubicLengthIndependent
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.LinearThree.CubicLength
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.MSIndependentApplication


/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.LinearThree.CubicLengthIndependent`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open Atlas.G2.Natural.BinaryNondegeneratePlane
open NoncentralChiefRefinement.CubicComparison
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.msCore_cubic_index_le_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (A : Subgroup G)
    (hA : A ≤ J) (h3 : IsPGroup 3 A) :
    (centralizer (A : Set G)).relIndex (msQ J ((L ⊔ T).pCoreIn 2)) ≤ 16 := by
  obtain ⟨S,_,_,e,he,_⟩ := s.exists_component_doubled_natural_without_ms d J j
  exact doubled_section_cubic_index_le J _ A (linearThreeActor e)
    (Representation.specialLinearNatural (k := ZMod 2) 3) (by simp) hA h3 he

theorem Context.joinCore_cubic_length_le_two_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (A : Subgroup G)
    (hA : A ≤ J) (h3 : IsPGroup 3 A) :
    conjugationCubicLength A ((J ⊔ (L ⊔ T).pCoreIn 2).pCoreIn 2) ≤ 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let P := D.pCoreIn 2
  let U := msQ J Q
  have hDP : D ≤ normalizer (P : Set G) :=
    D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  have hUP : U ≤ P := le_normalizer_iff_commutator_le_left.mp
    ((le_sup_left : J ≤ D).trans hDP)
  have hJP : J ≤ normalizer (P : Set G) := le_sup_left.trans hDP
  have hJU : J ≤ normalizer (U : Set G) := normalizer_commutator_ge_right P J
  let : (U.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_left P J)
  have he := length_eq_of_commutator_le A P U h3
    (pCore_isPGroup.map D.subtype) hUP (hA.trans hJP) (hA.trans hJU)
      (commutator_mono le_rfl hA)
  have hb := Nat.log_mono_right (b := 4) (s.msCore_cubic_index_le_without_ms d J j A hA h3)
  change conjugationCubicLength A U ≤ Nat.log 4 16 at hb
  norm_num at hb
  rwa [he] at hb

theorem Context.core_cubic_length_le_three_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (A : Subgroup G)
    (hA : A ≤ J) (h3 : IsPGroup 3 A)
    (hAQ : A ≤ normalizer (((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G)) :
    conjugationCubicLength A ((L ⊔ T).pCoreIn 2) ≤ 3 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let P := D.pCoreIn 2
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  have hPQ : P ≤ Q := by
    have h := map_mono (f := D.subtype) i.radical.twoCore_le
    change P ≤ (Q.subgroupOf D).map D.subtype at h
    rwa [map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)] at h
  have hAP : A ≤ normalizer (P : Set G) :=
    (hA.trans le_sup_left).trans (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  obtain ⟨hn,hcard⟩ := s.core_quotient_card_le_eight d J j
  let := hn
  have hs := (section_length_le_log_card A Q P h3
    (pCore_isPGroup.map (L ⊔ (T : Subgroup G)).subtype) hPQ hAQ hAP).trans
      (Nat.log_mono_right hcard)
  norm_num at hs
  have hp := s.joinCore_cubic_length_le_two_without_ms d J j A hA h3
  change conjugationCubicLength A P ≤ 2 at hp
  unfold sectionCubicLength at hs
  change conjugationCubicLength A Q ≤ 3
  omega

theorem Context.core_mod_module_cubic_length_le_one_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (n : normalizer (V : Set G)) (hnJ : n.val ∈ J) (hnL : n.val ∈ L)
    (horder : orderOf n.val = 3)
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    sectionCubicLength (zpowers n.val) V ((L ⊔ T).pCoreIn 2) ≤ 1 := by
  have h3 : IsPGroup 3 (zpowers n.val) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,horder,pow_one])
  have hAQ : zpowers n.val ≤ normalizer (((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) :=
    zpowers_le.mpr (normalizer_le_normalizer_characteristic_image
      (L ⊔ (T : Subgroup G)) (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hnL)))
  have hQ := s.core_cubic_length_le_three_without_ms d J j (zpowers n.val)
    (zpowers_le.mpr hnJ) h3 hAQ
  have hV := conjugationCubicLength_mono (zpowers n.val) (perpendicular_le d.coordinates)
  rw [perpendicular_cubic_length d n hn] at hV
  unfold sectionCubicLength
  omega

theorem Context.core_mod_module_cubic_length_eq_one_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (n : normalizer (V : Set G)) (hnJ : n.val ∈ J) (hnL : n.val ∈ L)
    (ho : orderOf n.val = 3)
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    sectionCubicLength (zpowers n.val) V ((L ⊔ T).pCoreIn 2) = 1 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQ : IsPGroup 2 Q := pCore_isPGroup.map (L ⊔ (T : Subgroup G)).subtype
  have hA : IsPGroup 3 (zpowers n.val) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ho,pow_one])
  have hAQ : zpowers n.val ≤ normalizer (Q : Set G) :=
    zpowers_le.mpr (normalizer_le_normalizer_characteristic_image
      (L ⊔ (T : Subgroup G)) (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hnL)))
  have hAV : zpowers n.val ≤ normalizer (V : Set G) := zpowers_le.mpr n.property
  let : (V.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    (s.chosen.core_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hlo := sectionCubicLength_pos_of_commutator_not_le (zpowers n.val) Q V
    hA hQ s.chosen.le_core hAQ hAV (s.cubic_moves_core_mod_module d J j n hnJ hnL ho)
  exact le_antisymm (s.core_mod_module_cubic_length_le_one_without_ms d J j n hnJ hnL ho hn) hlo

theorem Context.core_and_module_cubic_lengths_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (n : normalizer (V : Set G)) (hnJ : n.val ∈ J) (hnL : n.val ∈ L)
    (ho : orderOf n.val = 3)
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    conjugationCubicLength (zpowers n.val) ((L ⊔ T).pCoreIn 2) = 3 ∧
      conjugationCubicLength (zpowers n.val) V = 2 := by
  have h3 : IsPGroup 3 (zpowers n.val) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ho,pow_one])
  have hAQ : zpowers n.val ≤ normalizer (((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) :=
    zpowers_le.mpr (normalizer_le_normalizer_characteristic_image
      (L ⊔ (T : Subgroup G)) (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hnL)))
  have hQ := s.core_cubic_length_le_three_without_ms d J j (zpowers n.val)
    (zpowers_le.mpr hnJ) h3 hAQ
  have hV := conjugationCubicLength_mono (zpowers n.val) (perpendicular_le d.coordinates)
  rw [perpendicular_cubic_length d n hn] at hV
  have hq := s.core_mod_module_cubic_length_eq_one_without_ms d J j n hnJ hnL ho hn
  unfold sectionCubicLength at hq
  omega

theorem Context.exists_cubic_quotient_index_four_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    ∃ n : normalizer (V : Set G), n.val ∈ J ∧ n.val ∈ L ∧ orderOf n.val = 3 ∧
      d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic ∧
      ∃ hAQ : zpowers n.val ≤ normalizer (Q : Set G),
      ∃ hn : (V.subgroupOf Q).Normal, letI := hn
        letI := quotientConjugationAction (zpowers n.val) Q V hAQ (zpowers_le.mpr n.property)
        (FixedPoints.subgroup (zpowers n.val) (Q ⧸ V.subgroupOf Q)).index = 4 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨n,hnJ,hnL,ho,hn⟩ := s.component_marked_cubic_order_three d J j
  have hAQ : zpowers n.val ≤ normalizer (Q : Set G) :=
    zpowers_le.mpr (normalizer_le_normalizer_characteristic_image
      (L ⊔ (T : Subgroup G)) (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hnL)))
  let hnormal : (V.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    (s.chosen.core_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  let := hnormal
  refine ⟨n,hnJ,hnL,ho,hn,hAQ,hnormal,?_⟩
  let := quotientConjugationAction (zpowers n.val) Q V hAQ (zpowers_le.mpr n.property)
  have hA : IsPGroup 3 (zpowers n.val) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ho,pow_one])
  have hQ : IsPGroup 2 Q := pCore_isPGroup.map (L ⊔ (T : Subgroup G)).subtype
  have hl := s.core_mod_module_cubic_length_eq_one_without_ms d J j n hnJ hnL ho hn
  rw [sectionCubicLength_eq_quotient_of_twoGroup (zpowers n.val) Q V hA hQ
    s.chosen.le_core hAQ (zpowers_le.mpr n.property)] at hl
  have hi := FixedPoints.index_eq_four_pow_cubicLength
    (V := Q ⧸ V.subgroupOf Q) hA (hQ.to_quotient _)
  rw [hl] at hi
  exact hi

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
