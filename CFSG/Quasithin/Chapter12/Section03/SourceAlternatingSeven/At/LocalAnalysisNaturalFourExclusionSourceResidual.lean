module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionSourceResidual
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionPointQuotient

/-!
# LocalAnalysisNaturalFourExclusionSourceResidual at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionSourceResidual`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

private theorem source_point_le_at (z : G) : S.fourComponentPointPerfect z ≤ L ⊓ centralizer ({z} : Set G) :=
  map_subtype_le _

private theorem source_point_local_at (z : G) : S.fourComponentPointPerfect z ≤ S.fourPointLocal z :=
  (S.source_point_le_at z).trans (inf_le_inf_right _ L.le_normalizer)

private theorem source_faithful_projection_action_at
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (l : L) : S.fourFaithfulAction e (S.fourFaithfulProjection e l) =
      S.chosen.chosenAction l := by
  let := S.chosen.actionCentralizer_normal
  change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
  rw [e.symm_apply_apply]
  rfl

private theorem source_pointVector_val_at (z : V) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) : G) = z :=
  congrArg Subtype.val (S.chosen.spaceEquiv.apply_symm_apply z)

private theorem source_chosenAction_val_at (l : L) (w : S.chosen.space) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l w)) : G) =
      l * (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G) * (l : G)⁻¹ := by
  rw [S.chosen.spaceEquiv_apply, S.chosen.spaceEquiv_apply]
  rfl

private theorem source_pointVector_ne_zero_at {z : V} (hz : z ≠ 1) : S.fourPointVector z ≠ 0 := by
  intro he
  have h := congrArg (fun w => S.chosen.spaceEquiv (Multiplicative.ofAdd w)) he
  apply hz
  simpa only [fourPointVector, ofAdd_toAdd, MulEquiv.apply_symm_apply, ofAdd_zero, map_one] using h

private theorem source_covers_at
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1)
    (g : BinaryAlternatingSevenControl.pointStabilizer
      (S.fourFaithfulAction e) (S.fourPointVector z)) :
    ∃ l : L, (l : G) ∈ S.fourComponentPointPerfect z ∧ S.fourFaithfulProjection e l = g := by
  obtain ⟨l,hl,he⟩ := (S.four_componentPointPerfect_image e hd z hz).ge g.property
  exact ⟨l,hl,he⟩

private theorem source_point_join_le_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (z : G) :
    S.fourComponentPointPerfect z ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
  sup_le ((S.source_point_le_at z).trans (inf_le_left.trans S.chosen.normalizes))
    ((structural L S.hypothesis).2.2 V S.chosen).1

private theorem source_point_join_le_centralizer_at {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointPerfect z ⊔ (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  apply sup_le ((S.source_point_le_at z).trans inf_le_right)
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

private theorem source_normalizerProjection_fixes_point_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (n : normalizer (V : Set G))
    (hn : (n : G) ∈ centralizer ({(z : G)} : Set G)) :
    S.fourNormalizerProjection_at structural e hd n ∈
      BinaryAlternatingSevenControl.pointStabilizer (S.fourFaithfulAction e)
        (S.fourPointVector z) := by
  apply (BinaryAlternatingSevenControl.mem_pointStabilizer _ _ _).mpr
  apply Multiplicative.ofAdd.injective
  apply S.chosen.spaceEquiv.injective
  apply Subtype.ext
  rw [S.fourNormalizerProjection_action_at]
  have hv : S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) = z :=
    S.chosen.spaceEquiv.apply_symm_apply z
  rw [hv]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hn)

private def source_pointJoinProjection_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hzT : (z : G) ∈ omegaCenterIn (T : Subgroup G)) :
    (S.fourComponentPointPerfect z ⊔ (T : Subgroup G) : Subgroup G) →*
      BinaryAlternatingSevenControl.pointStabilizer (S.fourFaithfulAction e)
        (S.fourPointVector z) :=
  ((S.fourNormalizerProjection_at structural e hd).comp
    (inclusion (S.source_point_join_le_normalizer_at structural z))).codRestrict _
      (fun x => S.source_normalizerProjection_fixes_point_at structural e hd z _
        (S.source_point_join_le_centralizer_at hzT x.property))

private theorem source_source_pointJoinProjection_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) (hzT : (z : G) ∈ omegaCenterIn (T : Subgroup G)) :
    Function.Surjective (S.source_pointJoinProjection_at structural e hd z hzT) := by
  intro a
  obtain ⟨l,hl,he⟩ := S.source_covers_at e hd z hz a
  have hlJ : (l : G) ∈ S.fourComponentPointPerfect z ⊔ (T : Subgroup G) := mem_sup_left hl
  refine ⟨⟨l,hlJ⟩,?_⟩
  apply Subtype.ext
  change S.fourNormalizerProjection_at structural e hd
    ⟨l,S.source_point_join_le_normalizer_at structural z hlJ⟩ = a
  rw [S.fourNormalizerProjection_component_at]
  exact he

theorem four_componentPointCore_centralizes_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointCore z ≤ centralizer (V : Set G) := by
  let := S.chosen.actionCentralizer_normal
  let z' : V := ⟨z,hz⟩
  have hz' : z' ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  have hv : S.fourPointVector z' ≠ 0 := by
    intro he
    apply hz'
    have h := congrArg (fun v => S.chosen.spaceEquiv (Multiplicative.ofAdd v)) he
    simpa only [fourPointVector,ofAdd_toAdd,MulEquiv.apply_symm_apply,
      ofAdd_zero,map_one] using h
  let f := S.source_pointJoinProjection_at structural e hd z' hzT
  have hf := S.source_source_pointJoinProjection_surjective_at structural e hd z' hz' hzT
  let A := BinaryAlternatingSevenControl.pointStabilizer
    (S.fourFaithfulAction e) (S.fourPointVector z')
  let a := BinaryAlternatingSevenControl.pointStabilizerEquivLinear
    (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective) hd hv
  have hA : pCore 2 A = ⊥ := by
    apply (map_eq_bot_iff_of_injective (pCore 2 A) (f := a.toMonoidHom) a.injective).mp
    rw [pCore_map_iso,BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot]
  have hm : (pCore 2 (S.fourComponentPointPerfect z ⊔ (T : Subgroup G) : Subgroup G)).map f ≤
      pCore 2 A :=
    le_sSup ⟨(inferInstance : (pCore 2 _).Normal).map f hf, pCore_isPGroup.map f⟩
  rintro q ⟨x,hx,rfl⟩
  have hx0 : f x = 1 := mem_bot.mp (hA ▸ hm (mem_map_of_mem f hx))
  have hxproj : S.fourNormalizerProjection_at structural e hd
      ⟨x,S.source_point_join_le_normalizer_at structural z x.property⟩ = 1 :=
    congrArg Subtype.val hx0
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨w,hw⟩ := S.chosen.spaceEquiv.surjective ⟨v,hv⟩
  have h := S.fourNormalizerProjection_action_at structural e hd
    ⟨x,S.source_point_join_le_normalizer_at structural z x.property⟩ w.toAdd
  rw [hxproj,map_one] at h
  have hval : (S.chosen.spaceEquiv w : G) = v := congrArg Subtype.val hw
  change (S.chosen.spaceEquiv w : G) =
    (x : G) * (S.chosen.spaceEquiv w : G) * (x : G)⁻¹ at h
  rw [hval] at h
  exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm

theorem four_componentPointCore_eq_chosenCore_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointCore z = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := S.fourComponentPointPerfect z ⊔ (T : Subgroup G)
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : S.fourComponentPointCore z ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  apply le_antisymm
  · rw [← S.chosen_sylowCentralizer_eq_core_at structural]
    exact le_inf hQT (S.four_componentPointCore_centralizes_at structural e hd hz hz1 hzT)
  · have hRT : R ≤ (T : Subgroup G) := by
      dsimp only [R]
      rw [← S.chosen_sylowCentralizer_eq_core_at structural]
      exact inf_le_left
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (hRT.trans le_sup_right)
    have hJ : J ≤ L ⊔ (T : Subgroup G) :=
      sup_le_sup ((S.source_point_le_at z).trans inf_le_left) le_rfl
    exact hJ.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))

private theorem source_sylow_le_local_at {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (T : Subgroup G) ≤ S.fourPointLocal z := by
  refine le_inf S.chosen.sylow_normalizes_component ?_
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

private theorem source_core_control_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ((S.fourComponentPointCore z).subgroupOf (S.fourPointCentralizer z)).characteristicNormalizerClosure ≤
      (S.fourPointLocal z).subgroupOf (S.fourPointCentralizer z) := by
  have hc : (S.fourComponentPointCore z).characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
    rw [S.four_componentPointCore_eq_chosenCore_at structural e hd hz hz1 hzT]
    exact S.chosen_core_characteristicControl_at structural
  have hQH := (Chapter1.isSylowIn_iff.mp
    (S.four_componentPointCore_section_sylow hzT)).2.1.trans
      (ChapterA.Section04.twoSectionCentralizer_le _ _)
  have hh := characteristicNormalizerClosure_subgroupOf_le hQH hc
  intro g hg
  exact ⟨hh hg, g.property⟩

private theorem source_point_span_at (z : G) :
    conjugateSpanBy (S.fourComponentPointPerfect z) (S.fourPointLocal z) =
      S.fourComponentPointPerfect z :=
  le_antisymm (conjugateSpanBy_le le_rfl S.four_componentPointPerfect_normalized)
    (le_conjugateSpanBy _ _)

private theorem source_point_join_core_at {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (S.fourComponentPointPerfect z ⊔ S.fourComponentPointCore z).pCoreIn 2 =
      S.fourComponentPointCore z := by
  let J := S.fourComponentPointPerfect z ⊔ (T : Subgroup G)
  have hJK : J ≤ normalizer (S.fourComponentPointPerfect z : Set G) :=
    sup_le (S.fourComponentPointPerfect z).le_normalizer
      ((S.source_sylow_le_local_at hzT).trans S.four_componentPointPerfect_normalized)
  have hJQ : J ≤ normalizer (S.fourComponentPointCore z : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hKQJ : S.fourComponentPointPerfect z ⊔ S.fourComponentPointCore z ≤ J :=
    sup_le le_sup_left (pCoreIn_le 2 J)
  refine le_antisymm (pCoreIn_mono_of_normalizes hKQJ ?_) ?_
  · exact (le_inf hJK hJQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) le_sup_right (hKQJ.trans hJQ)

private theorem source_module_central_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ (center (S.fourComponentPointCore z)).map (S.fourComponentPointCore z).subtype := by
  have hVQ : V ≤ S.fourComponentPointCore z := by
    rw [S.four_componentPointCore_eq_chosenCore_at structural e hd hz hz1 hzT]
    exact S.chosen.le_core
  have hQV := S.four_componentPointCore_centralizes_at structural e hd hz hz1 hzT
  intro v hv
  refine ⟨⟨v,hVQ hv⟩,mem_center_iff.mpr ?_,rfl⟩
  intro q
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (hQV q.property) v hv).symm

theorem four_component_pushingUp_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
      (S.fourPointCentralizer z) (S.fourPointLocal z) (S.fourComponentPointPerfect z)
      (S.fourComponentPointCore z) V := by
  have hTM := S.source_sylow_le_local_at hzT
  have hQT : S.fourComponentPointCore z ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (S.fourComponentPointPerfect z ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hQM := hQT.trans hTM
  have hsection := S.four_componentPointCore_section_sylow hzT
  have hsectionM : Chapter1.IsSylowIn 2 (S.fourComponentPointCore z)
      (ChapterA.Section04.twoSectionCentralizer (S.fourComponentPointPerfect z) (S.fourPointLocal z)) := by
    apply hsection.restrict
    · intro q hq
      exact ⟨hQM hq,((Chapter1.isSylowIn_iff.mp hsection).2.1 hq).2⟩
    · intro y hy
      exact ⟨hy.1.2,hy.2⟩
  refine {
    sqtk := S.hypothesis.simpleQTKE.involution_centralizer_sqtk
      (orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1)
    radical_isTwoGroup := isPGroup_pCoreIn 2 _
    radical_le := hQM
    local_le := inf_le_right
    local_fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (S.four_pointLocal_characteristicTwo hz hz1 hzT))
    core_nontrivial := ?_
    component_le := S.source_point_local_at z
    component := S.four_componentPointPerfect_component e hd ⟨z,hz⟩
      (fun he => hz1 (congrArg Subtype.val he))
    section_sylow := by rw [S.source_point_span_at]; exact hsectionM
    characteristic_control := S.source_core_control_at structural e hd hz hz1 hzT
    module_nontrivial := S.chosen.ne_bot
    module_elementary := S.chosen.elementary
    module_le := by rw [S.source_point_span_at]; exact S.four_module_le_componentPointPerfect e hd hz hz1
    module_commutator := by rw [S.source_point_span_at]; exact S.four_componentPointPerfect_moved e hd hz hz1
    module_central := by
      rw [S.source_point_span_at,S.source_point_join_core_at hzT]
      exact S.source_module_central_at structural e hd hz hz1 hzT
    module_normalizer := ?_ }
  · have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,pow_one]
      exact orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1)
    have hle : zpowers z ≤ (S.fourPointCentralizer z).pCoreIn 2 :=
      le_pCoreIn_of_normalizes hp (zpowers_le.mpr (by simp [mem_centralizer_singleton_iff]))
        (by change centralizer ({z} : Set G) ≤ _
            rw [← centralizer_closure,← zpowers_eq_closure]
            exact Subgroup.centralizer_le_normalizer _)
    exact fun he => hz1 (mem_bot.mp (he ▸ hle (mem_zpowers z)))
  · rw [S.four_pointLocal_eq_at structural hz hz1]
    exact inf_comm _ _ |>.le

private theorem source_point_twoPerfect_at (z : G) : IsPPerfect 2 (S.fourComponentPointPerfect z) := by
  intro N hn hq
  let := hn
  let := hq.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)

theorem four_module_le_componentPerfectCore_omegaCenter_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ omegaCenterIn ((S.fourComponentPointPerfect z).pCoreIn 2) := by
  let := S.chosen.elementary
  have hKN : S.fourComponentPointPerfect z ≤ normalizer (V : Set G) :=
    (S.source_point_le_at z).trans (inf_le_left.trans S.chosen.normalizes)
  have hVK : V ≤ S.fourComponentPointPerfect z := S.four_module_le_componentPointPerfect e hd hz hz1
  have hVc : V ≤ (S.fourComponentPointPerfect z).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVK hKN
  have hTJ : (S.fourComponentPointPerfect z ⊔ (T : Subgroup G) : Subgroup G) ≤
      normalizer (S.fourComponentPointPerfect z : Set G) :=
    sup_le (S.fourComponentPointPerfect z).le_normalizer
      ((S.source_sylow_le_local_at hzT).trans
        (S.four_componentPointPerfect_normalized))
  have hcQ : (S.fourComponentPointPerfect z).pCoreIn 2 ≤ S.fourComponentPointCore z :=
    pCoreIn_mono_of_normalizes le_sup_left hTJ
  have hVcC : V ≤ centralizer ((S.fourComponentPointPerfect z).pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (hcQ.trans (S.four_componentPointCore_centralizes_at structural e hd hz hz1 hzT))
  intro v hv
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hVc hv, hVcC hv, elemPow_eq_one_of_isElementaryAbelian v hv⟩

theorem four_componentModule_le_intrinsicSignalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ ChapterA.Section04.intrinsicSignalizerModule (S.fourComponentPointPerfect z) := by
  rw [ChapterA.Section04.intrinsicSignalizerModule,
    ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter, commutator_comm]
  exact (S.four_componentPointPerfect_moved e hd hz hz1).le.trans
    (commutator_mono (S.four_module_le_componentPerfectCore_omegaCenter_at structural e hd hz hz1 hzT) le_rfl)

theorem four_componentPointPerfect_faithful_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ChapterA.Section04.IsFaithfulSignalizerType (S.fourComponentPointPerfect z) := by
  refine ⟨⟨?_, S.source_point_twoPerfect_at z, ?_⟩, ?_⟩
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_componentPointPerfect e hd hz hz1).trans he.le))
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (S.four_componentPointPerfect_characteristicTwo e hd hz hz1 hzT))
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_componentModule_le_intrinsicSignalizer_at structural e hd hz hz1 hzT).trans he.le))

theorem four_component_exists_unique_overcomponent_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z) ∧
      S.fourComponentPointPerfect z ≤ K ∧
      (∀ J : Subgroup G, J ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z) →
        S.fourComponentPointPerfect z ≤ J → J = K) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      ChapterA.Section04.IsFaithfulSignalizerType K ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) := by
  have hb := S.four_componentPointPerfect_local hz hz1 hzT e hd
  have hfaith := S.four_componentPointPerfect_faithful_at structural e hd hz hz1 hzT
  have hTH := (S.source_sylow_le_local_at hzT).trans inf_le_right
  have hBH : S.fourComponentPointPerfect z ≤ S.fourPointCentralizer z :=
    (S.source_point_le_at z).trans inf_le_right
  have hH : S.fourPointCentralizer z ∈ Chapter1.HOver G (T : Set G) :=
    ⟨(S.four_component_pushingUp_at structural e hd hz hz1 hzT).core_nontrivial,hTH⟩
  have hbH : (S.fourComponentPointPerfect z).subgroupOf (S.fourPointCentralizer z) ∈
      Chapter1.L (S.fourPointCentralizer z) ((T.subtype hTH) : Subgroup (S.fourPointCentralizer z)) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTH hBH).mp ⟨hBH,hb⟩
  obtain ⟨K,⟨hK,hBK⟩,hu⟩ := (Chapter1.existsUnique_cComponentsIn_iff hBH).mp
    (Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
      (Chapter1.Section02.containment_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      (Chapter1.Section02.uniqueness_local_quotient_sqtk S.hypothesis.simpleQTKE hH.1)
      (T.subtype hTH) hbH)
  have hKL := ((Chapter1.lemma_1_2_6 T hH).1 hK).2
  have hKf := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (S.hypothesis.simpleQTKE.evenCharacteristic T)
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr ⟨hb,hfaith⟩)
    hKL hBK
  exact ⟨K,hK,hBK,fun J hJ hj => hu J ⟨hJ,hj⟩,hKL,
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hKf).2,
    Chapter1.Section02.Adequate.local_chain_normalizes hb hKL hBK
      ((S.source_sylow_le_local_at hzT).trans S.four_componentPointPerfect_normalized)⟩

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

