module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionCore
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionCentralLine

/-!
# LocalAnalysisNaturalFourExclusionCore at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionCore`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

private def modelAutomorphism_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) :
    alternatingGroup (Fin 7) →* MulAut V :=
  (MulAut.congr S.chosen.spaceEquiv).toMonoidHom.comp
    { toFun a := ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S.chosen.space)
        ((S.fourFaithfulAction e).asGroupHom a)).toAddEquiv.toMultiplicative
      map_one' := by
        apply MulEquiv.ext
        intro v
        change Multiplicative.ofAdd (S.fourFaithfulAction e 1 v.toAdd) = v
        rw [map_one]
        rfl
      map_mul' a b := by
        apply MulEquiv.ext
        intro v
        change Multiplicative.ofAdd (S.fourFaithfulAction e (a*b) v.toAdd) = _
        rw [map_mul]
        rfl }

private theorem modelAutomorphism_apply_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (a : alternatingGroup (Fin 7)) (v : S.chosen.space) :
    S.modelAutomorphism_at e a (S.chosen.spaceEquiv (Multiplicative.ofAdd v)) =
      S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourFaithfulAction e a v)) := by
  change S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourFaithfulAction e a
    (S.chosen.spaceEquiv.symm (S.chosen.spaceEquiv (Multiplicative.ofAdd v))).toAdd)) = _
  rw [S.chosen.spaceEquiv.symm_apply_apply, toAdd_ofAdd]

private theorem modelAutomorphism_injective_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) :
    Function.Injective (S.modelAutomorphism_at e) := by
  let := S.chosen.actionCentralizer_normal
  intro a b hab
  apply S.chosen.faithfulAction_injective.comp e.symm.injective
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : MulAut V => f (S.chosen.spaceEquiv (Multiplicative.ofAdd v))) hab
  rw [S.modelAutomorphism_apply_at, S.modelAutomorphism_apply_at] at h
  exact Multiplicative.ofAdd.injective (S.chosen.spaceEquiv.injective h)

private theorem modelAutomorphism_component_at
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) (l : L) :
    S.modelAutomorphism_at e (S.fourFaithfulProjection e l) =
      V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ := by
  let := S.chosen.actionCentralizer_normal
  apply MulEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := S.chosen.spaceEquiv.surjective v
  have hw := S.modelAutomorphism_apply_at e (S.fourFaithfulProjection e l) w.toAdd
  simp only [ofAdd_toAdd] at hw
  rw [hw]
  have hact : S.fourFaithfulAction e (S.fourFaithfulProjection e l) = S.chosen.chosenAction l := by
    change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
    rw [e.symm_apply_apply]
    rfl
  rw [hact]
  apply Subtype.ext
  change (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l w.toAdd)) : G) =
    (l : G) * (S.chosen.spaceEquiv (Multiplicative.ofAdd w.toAdd) : G) * (l : G)⁻¹
  rw [S.chosen.spaceEquiv_apply, S.chosen.spaceEquiv_apply]
  rfl

private theorem normalizer_action_mem_model_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (n : normalizer (V : Set G)) :
    V.normalizerMonoidHom n ∈ (S.modelAutomorphism_at e).range := by
  obtain ⟨l,hl,c,hc,he⟩ := S.four_normalizer_factorization_at structural e hd n n.property
  refine ⟨S.fourFaithfulProjection e ⟨l,hl⟩, ?_⟩
  rw [S.modelAutomorphism_component_at]
  have hn : n = (⟨l,S.chosen.normalizes hl⟩ : normalizer (V : Set G)) *
      ⟨c,Subgroup.centralizer_le_normalizer _ hc⟩ := Subtype.ext he
  have hck : (⟨c,Subgroup.centralizer_le_normalizer _ hc⟩ : normalizer (V : Set G)) ∈
      V.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact hc
  rw [hn,map_mul,show V.normalizerMonoidHom ⟨c,Subgroup.centralizer_le_normalizer _ hc⟩ = 1 from hck,
    mul_one]

def fourNormalizerProjection_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    normalizer (V : Set G) →* alternatingGroup (Fin 7) :=
  (MonoidHom.ofInjective (S.modelAutomorphism_injective_at e)).symm.toMonoidHom.comp
    (V.normalizerMonoidHom.codRestrict (S.modelAutomorphism_at e).range
      (S.normalizer_action_mem_model_at structural e hd))

private theorem fourNormalizerProjection_model_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (n : normalizer (V : Set G)) :
    S.modelAutomorphism_at e (S.fourNormalizerProjection_at structural e hd n) =
      V.normalizerMonoidHom n :=
  MonoidHom.apply_ofInjective_symm (S.modelAutomorphism_injective_at e) _

theorem fourNormalizerProjection_action_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (n : normalizer (V : Set G)) (v : S.chosen.space) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd
      (S.fourFaithfulAction e (S.fourNormalizerProjection_at structural e hd n) v)) : G) =
      n * (S.chosen.spaceEquiv (Multiplicative.ofAdd v) : G) * (n : G)⁻¹ := by
  rw [← S.modelAutomorphism_apply_at, S.fourNormalizerProjection_model_at]
  rfl

theorem fourNormalizerProjection_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) (l : L) :
    S.fourNormalizerProjection_at structural e hd ⟨l,S.chosen.normalizes l.property⟩ =
      S.fourFaithfulProjection e l := by
  apply S.modelAutomorphism_injective_at e
  rw [S.fourNormalizerProjection_model_at,S.modelAutomorphism_component_at]

private theorem point_join_le_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (z : G) :
    S.fourPointPerfect z ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
  sup_le ((map_subtype_le _).trans ((map_subtype_le _).trans inf_le_left))
    ((structural L S.hypothesis).2.2 V S.chosen).1

private theorem point_join_le_centralizer_at {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourPointPerfect z ⊔ (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  apply sup_le ((map_subtype_le _).trans ((map_subtype_le _).trans inf_le_right))
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

private theorem normalizerProjection_fixes_point_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
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

private def pointJoinProjection_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hzT : (z : G) ∈ omegaCenterIn (T : Subgroup G)) :
    (S.fourPointPerfect z ⊔ (T : Subgroup G) : Subgroup G) →*
      BinaryAlternatingSevenControl.pointStabilizer (S.fourFaithfulAction e)
        (S.fourPointVector z) :=
  ((S.fourNormalizerProjection_at structural e hd).comp
    (inclusion (S.point_join_le_normalizer_at structural z))).codRestrict _
      (fun x => S.normalizerProjection_fixes_point_at structural e hd z _
        (S.point_join_le_centralizer_at hzT x.property))

private theorem pointJoinProjection_surjective_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) (hzT : (z : G) ∈ omegaCenterIn (T : Subgroup G)) :
    Function.Surjective (S.pointJoinProjection_at structural e hd z hzT) := by
  intro a
  obtain ⟨l,hl,he⟩ := S.four_pointPerfect_covers_pointAction e hd z hz a
  have hlJ : (l : G) ∈ S.fourPointPerfect z ⊔ (T : Subgroup G) := mem_sup_left hl
  refine ⟨⟨l,hlJ⟩,?_⟩
  apply Subtype.ext
  change S.fourNormalizerProjection_at structural e hd
    ⟨l,S.point_join_le_normalizer_at structural z hlJ⟩ = a
  rw [S.fourNormalizerProjection_component_at]
  exact he

theorem four_pointCore_centralizes_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourPointCore z ≤ centralizer (V : Set G) := by
  let := S.chosen.actionCentralizer_normal
  let z' : V := ⟨z,hz⟩
  have hz' : z' ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  have hv : S.fourPointVector z' ≠ 0 := by
    intro he
    apply hz'
    have h := congrArg (fun v => S.chosen.spaceEquiv (Multiplicative.ofAdd v)) he
    simpa only [fourPointVector,ofAdd_toAdd,MulEquiv.apply_symm_apply,
      ofAdd_zero,map_one] using h
  let f := S.pointJoinProjection_at structural e hd z' hzT
  have hf := S.pointJoinProjection_surjective_at structural e hd z' hz' hzT
  let A := BinaryAlternatingSevenControl.pointStabilizer
    (S.fourFaithfulAction e) (S.fourPointVector z')
  let a := BinaryAlternatingSevenControl.pointStabilizerEquivLinear
    (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective) hd hv
  have hA : pCore 2 A = ⊥ := by
    apply (map_eq_bot_iff_of_injective (pCore 2 A) (f := a.toMonoidHom) a.injective).mp
    rw [pCore_map_iso,BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot]
  have hm : (pCore 2 (S.fourPointPerfect z ⊔ (T : Subgroup G) : Subgroup G)).map f ≤
      pCore 2 A :=
    le_sSup ⟨(inferInstance : (pCore 2 _).Normal).map f hf, pCore_isPGroup.map f⟩
  rintro q ⟨x,hx,rfl⟩
  have hx0 : f x = 1 := mem_bot.mp (hA ▸ hm (mem_map_of_mem f hx))
  have hxproj : S.fourNormalizerProjection_at structural e hd
      ⟨x,S.point_join_le_normalizer_at structural z x.property⟩ = 1 :=
    congrArg Subtype.val hx0
  have hker : V.normalizerMonoidHom
      ⟨x,S.point_join_le_normalizer_at structural z x.property⟩ = 1 := by
    rw [← S.fourNormalizerProjection_model_at structural e hd,hxproj,map_one]
  change (⟨x,S.point_join_le_normalizer_at structural z x.property⟩ :
    normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker at hker
  rwa [normalizerMonoidHom_ker] at hker

private theorem pointCore_le_sylow_at (z : G) :
    S.fourPointCore z ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (S.fourPointPerfect z ⊔ (T : Subgroup G))
      (T.subtype le_sup_right)

private theorem sylow_le_pointLocal_at {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (T : Subgroup G) ≤ S.fourPointLocal z := by
  refine le_inf S.chosen.sylow_normalizes_component ?_
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

theorem four_pointPerfect_span_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    conjugateSpanBy (S.fourPointPerfect z) (S.fourPointLocal z) =
      S.fourPointPerfect z :=
  le_antisymm (conjugateSpanBy_le le_rfl
    (S.four_pointLocal_normalizes_perfect_at structural hz hz1))
    (le_conjugateSpanBy _ _)

theorem four_pointPerfect_join_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (S.fourPointPerfect z ⊔ S.fourPointCore z).pCoreIn 2 = S.fourPointCore z := by
  let J := S.fourPointPerfect z ⊔ (T : Subgroup G)
  have hJK : J ≤ normalizer (S.fourPointPerfect z : Set G) :=
    sup_le (S.fourPointPerfect z).le_normalizer
      ((S.sylow_le_pointLocal_at hzT).trans
        (S.four_pointLocal_normalizes_perfect_at structural hz hz1))
  have hJQ : J ≤ normalizer (S.fourPointCore z : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hKQJ : S.fourPointPerfect z ⊔ S.fourPointCore z ≤ J :=
    sup_le le_sup_left (pCoreIn_le 2 J)
  refine le_antisymm (pCoreIn_mono_of_normalizes hKQJ ?_) ?_
  · exact (le_inf hJK hJQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) le_sup_right (hKQJ.trans hJQ)

theorem four_module_le_pointCore_center_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ (center (S.fourPointCore z)).map (S.fourPointCore z).subtype := by
  let := S.chosen.elementary
  have hVQ : V ≤ S.fourPointCore z :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      ((S.four_module_le_pointPerfect_at structural e hd hz hz1).trans le_sup_left)
      (S.point_join_le_normalizer_at structural z)
  have hQV := S.four_pointCore_centralizes_at structural e hd hz hz1 hzT
  intro v hv
  refine ⟨⟨v,hVQ hv⟩,mem_center_iff.mpr ?_,rfl⟩
  intro q
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (hQV q.property) v hv).symm

omit [Finite G] in

private theorem point_core_ne_bot_at {z : G} (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHC : H ≤ centralizer ({z} : Set G)) : H.pCoreIn 2 ≠ ⊥ := by
  have ho : orderOf z = 2 := orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1
  have hp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using ho)
  have hzH : zpowers z ≤ H := zpowers_le.mpr
    (hTH ((mem_omegaCenterIn_iff _ _).mp hzT).1)
  have hn : H ≤ normalizer (zpowers z : Set G) := by
    apply hHC.trans
    rw [← centralizer_closure,← zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hcore := le_pCoreIn_of_normalizes hp hzH hn
  intro he
  exact hz1 (mem_bot.mp (he ▸ hcore (mem_zpowers z)))

theorem four_pushingUp_of_component_control_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (component : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent)
    (control : ((S.fourPointCore z).subgroupOf (S.fourPointCentralizer z)).characteristicNormalizerClosure ≤
      (S.fourPointLocal z).subgroupOf (S.fourPointCentralizer z)) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
      (S.fourPointCentralizer z) (S.fourPointLocal z) (S.fourPointPerfect z)
      (S.fourPointCore z) V := by
  have hTM := S.sylow_le_pointLocal_at hzT
  have hQM := (S.pointCore_le_sylow_at z).trans hTM
  have hTH : (T : Subgroup G) ≤ S.fourPointCentralizer z := hTM.trans inf_le_right
  have hspan := S.four_pointPerfect_span_at structural hz hz1
  have hsection := S.four_pointCore_section_sylow_at structural hz hz1 hzT
  have hsectionM : Chapter1.IsSylowIn 2 (S.fourPointCore z)
      (ChapterA.Section04.twoSectionCentralizer (S.fourPointPerfect z) (S.fourPointLocal z)) := by
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
    local_fitting := ?_
    core_nontrivial := point_core_ne_bot_at hz1 hzT hTH le_rfl
    component_le := ?_
    component := component
    section_sylow := by rw [hspan]; exact hsectionM
    characteristic_control := control
    module_nontrivial := S.chosen.ne_bot
    module_elementary := S.chosen.elementary
    module_le := by rw [hspan]; exact S.four_module_le_pointPerfect_at structural e hd hz hz1
    module_commutator := by rw [hspan]; exact S.four_pointPerfect_moved e hd hz hz1
    module_central := ?_
    module_normalizer := ?_ }
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (S.hypothesis.simpleQTKE.evenCharacteristic T)
        ⟨point_core_ne_bot_at hz1 hzT hTM inf_le_right,hTM⟩))
  · rw [S.four_pointLocal_eq_at structural hz hz1]
    exact (map_subtype_le _).trans (map_subtype_le _)
  · rw [hspan,S.four_pointPerfect_join_core_at structural hz hz1 hzT]
    exact S.four_module_le_pointCore_center_at structural e hd hz hz1 hzT
  · rw [S.four_pointLocal_eq_at structural hz hz1]
    exact inf_comm _ _ |>.le

theorem fourResidualData_of_component_control_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (component : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent)
    (control : ((S.fourPointCore z).subgroupOf (S.fourPointCentralizer z)).characteristicNormalizerClosure ≤
      (S.fourPointLocal z).subgroupOf (S.fourPointCentralizer z))
    (faithful : ChapterA.Section04.IsFaithfulSignalizerType (S.fourPointPerfect z))
    (local_member : S.fourPointPerfect z ∈ Chapter1.L G (T : Subgroup G))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.FourResidualData z :=
  S.fourResidualData_of_local_structure_at structural e hd hz hz1 hzT
    (S.four_pushingUp_of_component_control_at structural e hd hz hz1 hzT component control)
    faithful local_member quotient

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

