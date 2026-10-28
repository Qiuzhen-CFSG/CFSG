module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LinearThree.CubicLength
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.LinearThree.DoubledNatural

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.LinearThree.CubicLength`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Representation.BinaryFixedPoints
variable {G B W : Type*} [Group G] [Group B] [AddCommGroup W] [Module (ZMod 2) W]

/-- The fixed index in a fully marked section is the literal relative centralizer index. -/
theorem full_section_fixed_index (J U A : Subgroup G) (a : J →* B)
    (ρ : Representation (ZMod 2) B W) (hA : A ≤ J)
    (h : HasSectionModel J U ⊥ a ρ) :
    (centralizer (A : Set G)).relIndex U = fixedIndex (ρ.comp (a.comp (inclusion hA))) := by
  obtain ⟨_,hJU,_,hn,e,he⟩ := h
  let := hn
  have hb : (⊥ : Subgroup G).subgroupOf U = ⊥ := bot_subgroupOf U
  let b : (U ⧸ (⊥ : Subgroup G).subgroupOf U) ≃* U :=
    (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
  let c : U ≃* Multiplicative W := b.symm.trans e
  let hAU := hA.trans hJU
  let := conjMulDistribMulActionOfLeNormalizer A U hAU
  have hc : FixedPoints.subgroup A U = (centralizer (A : Set G)).subgroupOf U := by
    ext u
    constructor
    · intro hu x hx
      have hh := congrArg Subtype.val (hu ⟨x,hx⟩)
      change x * u.val * x⁻¹ = u.val at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hu x
      apply Subtype.ext
      change x.val * u.val * x.val⁻¹ = u.val
      have hh : x.val * u.val = u.val * x.val := hu x x.property
      rw [hh,mul_inv_cancel_right]
  change ((centralizer (A : Set G)).subgroupOf U).index = _
  rw [←hc]
  apply fixedIndex_eq_of_equivariant (ρ.comp (a.comp (inclusion hA)))
    (MonoidHom.id A) Function.surjective_id c
  intro x u
  apply Multiplicative.toAdd.injective
  exact he (inclusion hA x) u (x • u) rfl


/-- A doubled three-dimensional binary module has cubic displacement at most four dimensions. -/
theorem doubled_section_cubic_index_le (J U A : Subgroup G) (a : J →* B)
    (ρ : Representation (ZMod 2) B W) [Finite W] (hW : Nat.card W = 8)
    (hA : A ≤ J) (h3 : IsPGroup 3 A)
    (h : HasSectionModel J U ⊥ a (ρ.prod ρ)) :
    (centralizer (A : Set G)).relIndex U ≤ 16 := by
  rw [full_section_fixed_index J U A a (ρ.prod ρ) hA h]
  have hp : (ρ.prod ρ).comp (a.comp (inclusion hA)) =
      Representation.prod (ρ.comp (a.comp (inclusion hA))) (ρ.comp (a.comp (inclusion hA))) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    rfl
  rw [hp]
  rw [fixedIndex_prod]
  have hi := fixedIndex_le_four_of_card_eight (ρ.comp (a.comp (inclusion hA))) h3 hW
  nlinarith

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Atlas.G2.Natural.BinaryNondegeneratePlane
open NoncentralChiefRefinement.CubicComparison
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.msCore_cubic_index_le (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G) (A : Subgroup G)
    (hA : A ≤ J) (h3 : IsPGroup 3 A) :
    (centralizer (A : Set G)).relIndex (msQ J ((L ⊔ T).pCoreIn 2)) ≤ 16 := by
  obtain ⟨S,_,_,e,he,_⟩ := s.exists_component_doubled_natural d J j earlier
  exact doubled_section_cubic_index_le J _ A (linearThreeActor e)
    (Representation.specialLinearNatural (k := ZMod 2) 3) (by simp) hA h3 he

theorem Context.joinCore_cubic_length_le_two (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G) (A : Subgroup G)
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
  have hb := Nat.log_mono_right (b := 4) (s.msCore_cubic_index_le d J j earlier A hA h3)
  change conjugationCubicLength A U ≤ Nat.log 4 16 at hb
  norm_num at hb
  rwa [he] at hb

private theorem binary_two_subgroup_card_le_eight (P : Subgroup Matrix.PSL3Two.SL)
    (hp : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hc : Nat.card (S : Subgroup Matrix.PSL3Two.SL) = 8 := by
    rw [S.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  exact (Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective _)).trans_eq hc

/-- The exact quotient of the original Q by the full join core has order at most eight. -/
theorem Context.core_quotient_card_le_eight (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let P := (J ⊔ Q).pCoreIn 2
    ∃ hn : (P.subgroupOf Q).Normal, letI := hn
      Nat.card (Q ⧸ P.subgroupOf Q) ≤ 8 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let P := D.pCoreIn 2
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  let f : Q →* Matrix.PSL3Two.SL := i.coreProjection.comp (inclusion (show Q ≤ D from le_sup_right))
  have hk : f.ker = P.subgroupOf Q := by
    ext x
    change i.coreProjection (inclusion (show Q ≤ D from le_sup_right) x) = 1 ↔ x.val ∈ P
    change inclusion (show Q ≤ D from le_sup_right) x ∈ i.coreProjection.ker ↔ _
    rw [i.coreProjection_kernel]
    constructor
    · intro hx
      exact mem_map_of_mem D.subtype hx
    · rintro ⟨y,hy,he⟩
      have hyx : y = inclusion (show Q ≤ D from le_sup_right) x := Subtype.ext he
      exact hyx ▸ hy
  let hn : (P.subgroupOf Q).Normal := hk ▸ inferInstance
  let := hn
  refine ⟨hn,?_⟩
  rw [←hk,Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact binary_two_subgroup_card_le_eight f.range
    ((pCore_isPGroup.map (L ⊔ (T : Subgroup G)).subtype).of_surjective
      f.rangeRestrict f.rangeRestrict_surjective)

/-- At most three cubic layers occur in the original Q, with its full join core retained. -/
theorem Context.core_cubic_length_le_three (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G) (A : Subgroup G)
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
  have hp := s.joinCore_cubic_length_le_two d J j earlier A hA h3
  change conjugationCubicLength A P ≤ 2 at hp
  unfold sectionCubicLength at hs
  change conjugationCubicLength A Q ≤ 3
  omega

omit [Finite G] in
/-- The fixed-free perpendicular four-space supplies two actual cubic layers. -/
theorem perpendicular_cubic_index (d : MarkedPlane V)
    (n : normalizer (V : Set G))
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    (centralizer (zpowers n.val : Set G)).relIndex (perpendicular d.coordinates) = 16 := by
  have hb : (centralizer (zpowers n.val : Set G)).subgroupOf
      (perpendicular d.coordinates) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    apply (perpendicular_inf_cubic_centralizer_eq_bot d n hn).le
    refine ⟨x.property,?_⟩
    intro y hy
    have hy' : y = n.val := Set.mem_singleton_iff.mp hy
    subst y
    exact hx n.val (mem_zpowers n.val)
  change ((centralizer (zpowers n.val : Set G)).subgroupOf
    (perpendicular d.coordinates)).index = _
  rw [hb,index_bot,perpendicular_card]

omit [Finite G] in
theorem perpendicular_cubic_length (d : MarkedPlane V)
    (n : normalizer (V : Set G))
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    conjugationCubicLength (zpowers n.val) (perpendicular d.coordinates) = 2 := by
  rw [conjugationCubicLength,perpendicular_cubic_index d n hn]
  decide

/-- The original cubic has at most one noncentral binary layer above V in Q. -/
theorem Context.core_mod_module_cubic_length_le_one (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G)
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
  have hQ := s.core_cubic_length_le_three d J j earlier (zpowers n.val)
    (zpowers_le.mpr hnJ) h3 hAQ
  have hV := conjugationCubicLength_mono (zpowers n.val) (perpendicular_le d.coordinates)
  rw [perpendicular_cubic_length d n hn] at hV
  unfold sectionCubicLength
  omega

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

-- The context-independent cubic radical-image lemma is reused from the original module.


namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Atlas.G2.Natural.BinaryNondegeneratePlane
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- All of V, not only its perpendicular four-space, lies in the full join core. -/
theorem Context.module_le_joinCore (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    V ≤ (J ⊔ (L ⊔ T).pCoreIn 2).pCoreIn 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  have hpQ : D.pCoreIn 2 ≤ Q := by
    have h := map_mono (f := D.subtype) i.radical.twoCore_le
    change D.pCoreIn 2 ≤ (Q.subgroupOf D).map D.subtype at h
    rwa [map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)] at h
  intro v hv
  refine ⟨⟨v,mem_sup_right (s.chosen.le_core hv)⟩,i.core_selfCentralizing ?_,rfl⟩
  intro x hx
  exact Subtype.ext ((s.chosen.core_centralizes
    (⟨x.val,hpQ (mem_map_of_mem D.subtype hx)⟩ : Q).property) v hv).symm

/-- The actual marked cubic acts nontrivially on Q/V. -/
theorem Context.cubic_moves_core_mod_module (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (n : normalizer (V : Set G)) (hnJ : n.val ∈ J) (hnL : n.val ∈ L)
    (ho : orderOf n.val = 3) :
    ¬ ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,zpowers n.val⁆ ≤ V := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let R := Q.subgroupOf D
  let c : D := ⟨n.val,mem_sup_left hnJ⟩
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  have hnQ : n.val ∈ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
      (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hnL))
  have hcR : c ∈ normalizer (R : Set D) := by
    rw [←subgroupOf_normalizer_eq (show Q ≤ D from le_sup_right)]
    exact hnQ
  have ho' : orderOf c = 3 := (Subgroup.orderOf_coe c).symm.trans ho
  intro hmov
  apply i.cubic_moves_radical_image c hcR ho'
  rintro _ ⟨r,hr,rfl⟩
  have hm : ⁅r,c⁆ ∈ pCore 2 D := by
    have hh : (⁅r,c⁆ : D).val ∈ D.pCoreIn 2 :=
      s.module_le_joinCore d J j (hmov
        (commutator_mem_commutator hr (mem_zpowers n.val)))
    obtain ⟨x,hx,he⟩ := hh
    exact (show x = ⁅r,c⁆ from Subtype.ext he) ▸ hx
  have he : i.coreProjection ⁅r,c⁆ = 1 := by
    change ⁅r,c⁆ ∈ i.coreProjection.ker
    rwa [i.coreProjection_kernel]
  rw [map_commutatorElement] at he
  exact commutatorElement_eq_one_iff_mul_comm.mp he

/-- Exactly one cubic layer remains in the literal relative quotient Q/V. -/
theorem Context.core_mod_module_cubic_length_eq_one (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G)
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
  exact le_antisymm (s.core_mod_module_cubic_length_le_one d J j earlier n hnJ hnL ho hn) hlo

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Atlas.G2.Natural.BinaryNondegeneratePlane
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The source's three/two/one count, for the original marked cubic and original Q and V. -/
theorem Context.core_and_module_cubic_lengths (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G)
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
  have hQ := s.core_cubic_length_le_three d J j earlier (zpowers n.val)
    (zpowers_le.mpr hnJ) h3 hAQ
  have hV := conjugationCubicLength_mono (zpowers n.val) (perpendicular_le d.coordinates)
  rw [perpendicular_cubic_length d n hn] at hV
  have hq := s.core_mod_module_cubic_length_eq_one d J j earlier n hnJ hnL ho hn
  unfold sectionCubicLength at hq
  omega

/-- The actual relative quotient Q/V has fixed subgroup of index four for
an order-three lift of the specified cubic lying in both original components. -/
theorem Context.exists_cubic_quotient_index_four (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G) :
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
  have hl := s.core_mod_module_cubic_length_eq_one d J j earlier n hnJ hnL ho hn
  rw [sectionCubicLength_eq_quotient_of_twoGroup (zpowers n.val) Q V hA hQ
    s.chosen.le_core hAQ (zpowers_le.mpr n.property)] at hl
  have hi := FixedPoints.index_eq_four_pow_cubicLength
    (V := Q ⧸ V.subgroupOf Q) hA (hQ.to_quotient _)
  rw [hl] at hi
  exact hi

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
