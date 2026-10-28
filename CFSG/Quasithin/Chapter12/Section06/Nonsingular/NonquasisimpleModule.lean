module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleGlobalFixed
public import CFSG.Quasithin.ChapterA.Section04.SourceChains
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.ReducedNormal.SimpleCoreOmega
public import Theory.Frattini.OmegaProducts

/-!
# The canonical module of the nonquasisimple nonsingular component

The literal V_v is reduced in L_v and fully moved by L_v, so it lies in
its nontrivial intrinsic module. The recognized simple two-core quotients
make nonquasisimple L_v and K_v characteristic-two groups. The original
Sylow and normalizer geometry supplies every premise of A.4.10, which
transfers intrinsic-module movement from L_v to K_v.

A.4.8 detects this movement on U=Omega_1 Z(O_2(K_vS)). The simple head
and the normal-kernel theorem give C_(K_vS)(U)=O_2(K_vS); the same bound
makes U reduced and hence equal to R_2(K_vS). Thus 12.6.13(1) holds once
K_v is not quasisimple. At the actual preferred escaping point, the
previous original-fixed-space exclusion discharges that condition when
C_V(L) is nontrivial. The original V, fixed line and Sylow position are
retained throughout.

The HS and J4 exclusions with trivial original fixed space, the separate
containment 12.6.13(3), blocks, splitting and general fixed-space elimination
remain open. Neither 12.6.2 nor 12.6.23 is asserted. Earlier T-invariance
and TI retain producer qt-d-1222-source and final discharge owner
qt-d-12634-source.

Source: Aschbacher--Smith, Lemma 12.6.13, printed p.826;
A.4.8 and A.4.10, printed pp.59--60.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section06
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
/-- The original reduced moved subgroup witnesses membership of L_v in X_f. -/
theorem SourceHypothesis.nonsingular_local_faithful_signalizer
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    Vv L V (v : G) ≤ intrinsicSignalizerModule (Lv L (v : G)) ∧
      IsFaithfulSignalizerType (Lv L (v : G)) := by
  let A := Lv L (v : G)
  let W := Vv L V (v : G)
  have hWA : W ≤ A := Vv_le_Lv H.chosen v
  have hr := D.local_residual_moved_isReduced H.chosen H.source.quasisimple v hv
  have hWne : W ≠ ⊥ := by
    intro he
    have hc := D.nonsingular_moved_card H.chosen v hv
    rw [show Vv L V (v : G) = ⊥ from he,card_bot] at hc
    norm_num at hc
  have hWomega : W ≤ omegaOneCenterAmbient (A.pCoreIn 2) := by
    intro w hw
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨Vv_le_core_Lv H.chosen v hw,?_,?_⟩
    · exact elemPow_eq_one_of_isElementaryAbelian w (Vv_le_V H.chosen.normalizes _ hw)
    · rintro r ⟨r,hrcore,rfl⟩
      exact congrArg A.subtype (hr.le_centralizer_pCore
        (show (⟨w,hWA hw⟩ : A) ∈ W.subgroupOf A from hw) r hrcore)
  have hmove := D.local_moved_generated H.chosen v hv
  have hWI : W ≤ intrinsicSignalizerModule A := by
    change W ≤ signalizerModule A (A.pCoreIn 2)
    rw [signalizerModule_eq_commutator_omegaCenter, commutator_comm A]
    calc
      W = ⁅W,A⁆ := hmove.symm
      _ ≤ ⁅omegaOneCenterAmbient (A.pCoreIn 2), A⁆ := commutator_mono hWomega le_rfl
  refine ⟨hWI,⟨?_,fun he => hWne (bot_unique (hWI.trans he.le))⟩⟩
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let : Group.IsPerfect A := Lv_isPerfect_of_A6 L (v : G) e
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := e.isSimpleGroup
  let : IsQuasisimple (A ⧸ pCore 2 A) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) e)).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hp : IsPPerfect 2 A := isPPerfect_embedded_pResidual 2 (CLv L (v : G))
  refine ⟨fun he => hWne (bot_unique (hWA.trans he.le)),hp,?_⟩
  apply constrained_of_simple_core_not_quasisimple hp
  intro hq
  let := hq
  apply (H.nonsingular_local_core_moved D v hv).1
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro _ ⟨a,ha,rfl⟩ b hb
  exact congrArg A.subtype (mem_center_iff.mp (IsQuasisimple.pCore_le_center 2 ha) ⟨b,hb⟩)

/-- The recognized simple two-core quotient puts nonquasisimple K_v in X. -/
theorem SourceHypothesis.nonsingular_nonquasisimple_signalizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hnot : ¬ IsQuasisimple (Kv (v : G))) :
    IsSignalizerType (Kv (v : G)) := by
  obtain ⟨hc,_,_,hq,hs⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star (Kv (v : G))) := hq
  let : IsSimpleGroup (Star (Kv (v : G))) := hs
  let : Group.IsPerfect ((Kv (v : G)).subgroupOf (Gv (v : G))) := hc.perfect
  let : Group.IsPerfect (Kv (v : G)) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (Kv_le_Gv (v : G))).toMonoidHom)
    (subgroupOfEquivOfLe (Kv_le_Gv (v : G))).surjective
  refine ⟨?_,Kv_isPPerfect (v : G),
    constrained_of_simple_core_not_quasisimple (Kv_isPPerfect (v : G)) hnot⟩
  intro he
  have hne := (H.nonsingular_local_faithful_signalizer D v hv).2.1.1
  exact hne (bot_unique ((Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))).trans he.le))
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
/-- Apply A.4.10 to the literal L_v, K_v and selected Sylow subgroup of G_v. -/
theorem SourceHypothesis.nonsingular_nonquasisimple_faithful_signalizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      Tv T (v : G) ≤ S₀ ∧
      Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (v : G) : Set G))
        (Gv (v : G) ⊓ normalizer (Lv L (v : G) : Set G)) ∧
      R L (Kv (v : G)) S₀ (v : G) ≤ normalizer (Lv L (v : G) : Set G) ∧
      ⁅Lv L (v : G),R L (Kv (v : G)) S₀ (v : G)⁆ ≤ (Lv L (v : G)).pCoreIn 2 ∧
      R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) ∧
      IsFaithfulSignalizerType (Kv (v : G)) ∧
      generalizedFitting (Kv (v : G) ⊔ S₀ : Subgroup G) =
        pCore 2 (Kv (v : G) ⊔ S₀ : Subgroup G) := by
  let C := Kv (v : G)
  let A := Lv L (v : G)
  have hAC : A ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  have hX := (H.nonsingular_local_faithful_signalizer D v hv).2
  have hY := H.nonsingular_nonquasisimple_signalizer D v hv hnot
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  obtain ⟨P,hP⟩ := hs.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (v : G) ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  obtain ⟨S,hTS,hN,hR,hRC,hReq⟩ := exists_nonsingular_sylow_normalization T L (v : G)
    H.chosen.sylow_normalizes_component hAC e P hP hi
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ S₀
  have hJA : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) (map_subtype_le _)
  have hSC : S₀ ≤ normalizer (C : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv _))
  have hS : Chapter1.IsSylowIn 2 S₀ J :=
    (show Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) from ⟨S,rfl⟩).restrict le_sup_right hJA
  have hN' : Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (A : Set G))
      (J ⊓ normalizer (A : Set G)) :=
    (show Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (A : Set G))
      (Gv (v : G) ⊓ normalizer (A : Set G)) from hN).restrict
        (inf_le_inf le_sup_right le_rfl) (inf_le_inf hJA le_rfl)
  have hcore : J.pCoreIn 2 ≤ S₀ ⊓ normalizer (A : Set G) :=
    (core_le_R_of_sylow L C _ S (Kv_le_Gv _)).trans (le_inf inf_le_left hR)
  have hf := (SourceChains.source_A410 A C S₀ hAC hX.1 hY hSC hS hcore hN').2.2 hX
  have hcC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    hY.2.2 ▸ centralizer_generalizedFitting_le C
  have hcJ := centralizer_pCore_sup_le 2 C S₀ hcC (S.isPGroup'.map _) hSC
  exact ⟨S,hTS,hN,hR,hRC,hReq,hf,generalizedFitting_eq_pCore_of_selfCentralizing 2 hcJ⟩
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
omit [Finite G] in
/-- The source definition U is the ambient omega-center of the original two-core. -/
theorem U_eq_omegaCenter (C S : Subgroup G) :
    U C S = omegaOneCenterAmbient ((C ⊔ S).pCoreIn 2) := by
  unfold U
  rw [←map_omegaOneAmbient_injective _ ((C ⊔ S).pCoreIn 2).subtype_injective]
  rfl

/-- Source 12.6.13(1) and U=R₂(K_vS), conditional on the remaining 12.6.12 exclusion. -/
theorem SourceHypothesis.nonsingular_nonquasisimple_canonical_module
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let J := Kv (v : G) ⊔ S₀
      Tv T (v : G) ≤ S₀ ∧
      Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (v : G) : Set G))
        (Gv (v : G) ⊓ normalizer (Lv L (v : G) : Set G)) ∧
      R L (Kv (v : G)) S₀ (v : G) ≤ normalizer (Lv L (v : G) : Set G) ∧
      ⁅Lv L (v : G),R L (Kv (v : G)) S₀ (v : G)⁆ ≤ (Lv L (v : G)).pCoreIn 2 ∧
      R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) ∧
      IsFaithfulSignalizerType (Kv (v : G)) ∧
      generalizedFitting J = pCore 2 J ∧
      centralizer ((U (Kv (v : G)) S₀).subgroupOf J : Set J) = pCore 2 J ∧
      U (Kv (v : G)) S₀ = (reducedTwoSubgroup J).map J.subtype := by
  obtain ⟨S,hTS,hN,hRN,hRC,hReq,hf,hF⟩ := H.nonsingular_nonquasisimple_faithful_signalizer D v hv hnot hs hi
  let C := Kv (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ S₀
  let C₀ := C.subgroupOf J
  let P := S₀.subgroupOf J
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) (map_subtype_le _)
  have hSC : S₀ ≤ normalizer (C : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv _))
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hSC)
  obtain ⟨hc,_,_,hq,hsimple⟩ := H.nonsingular_canonical_component D v hv
  have hc₀ : C₀.IsCComponent := hc.subgroupOf_of_le le_sup_left hJG
  let : IsQuasisimple (C ⧸ pCore 2 C) := hq
  let : IsSimpleGroup (C ⧸ pCore 2 C) := hsimple
  let e : C₀ ≃* C := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let eq : (C₀ ⧸ pCore 2 C₀) ≃* (C ⧸ pCore 2 C) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (C₀ ⧸ pCore 2 C₀) := IsQuasisimple.of_mulEquiv eq.symm
  let : IsSimpleGroup (C₀ ⧸ pCore 2 C₀) := eq.isSimpleGroup
  have hz : center (C₀ ⧸ pCore 2 C₀) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (C₀ ⧸ pCore 2 C₀)) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  have hp : IsPPerfect 2 C₀ := (Kv_isPPerfect (v : G)).of_surjective e.symm.toMonoidHom e.symm.surjective
  have hmap : C₀.map J.subtype = C := map_subgroupOf_eq_of_le le_sup_left
  have hne : intrinsicSignalizerModule C₀ ≠ ⊥ := by
    intro he
    have hm := intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective C₀
    rw [hmap,he,Subgroup.map_bot] at hm
    exact hf.2 hm
  have hn : C₀ ≤ normalizer (pCore 2 J : Set J) := le_normalizer_of_normal
  have hcomm : ⁅C₀,pCore 2 J⁆ ≤ C₀.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal C₀ (pCore 2 J)
      hc₀.subnormal hp pCore_isPGroup hn).trans (map_mono (commutator_le_left _ _))
  have hm := (signalizerModule_ne_bot_iff_intrinsic C₀ (pCore 2 J) hp
    pCore_isPGroup hn (pCoreIn_le_of_subnormal 2 hc₀.subnormal) hcomm).mpr hne
  rw [signalizerModule_eq_commutator_omegaCenter,commutator_comm] at hm
  have hP : IsPGroup 2 P := (S.isPGroup'.map (Gv (v : G)).subtype).comap_of_injective
    J.subtype J.subtype_injective
  have hgen : C₀ ⊔ P = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,hmap,map_subgroupOf_eq_of_le (show S₀ ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨hker,hr⟩ := omegaCenter_reduced_of_simple_component C₀ P hc₀ hz hP hgen hm
  have hU : U C S₀ = (omegaOneCenterAmbient (pCore 2 J)).map J.subtype := by
    rw [U_eq_omegaCenter]
    exact omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective _
  refine ⟨S,hTS,hN,hRN,hRC,hReq,hf,hF,?_,hU.trans (congrArg (map J.subtype) hr)⟩
  rw [hU]
  change centralizer (((omegaOneCenterAmbient (pCore 2 J)).map J.subtype).comap J.subtype : Set J) = _
  rw [comap_map_eq_self_of_injective J.subtype_injective]
  exact hker
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
/-- At the original preferred point with nontrivial C_V(L), nonquasisimplicity is discharged. -/
theorem SourceHypothesis.exists_preferred_nonsingular_canonical_module_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      ¬ IsQuasisimple (Kv (w : G)) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      ∃ S : Sylow 2 (Gv (w : G)),
        let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
        let J := Kv (w : G) ⊔ S₀
        Tv T (w : G) ≤ S₀ ∧
        Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (w : G) : Set G))
          (Gv (w : G) ⊓ normalizer (Lv L (w : G) : Set G)) ∧
        R L (Kv (w : G)) S₀ (w : G) ≤ normalizer (Lv L (w : G) : Set G) ∧
        ⁅Lv L (w : G),R L (Kv (w : G)) S₀ (w : G)⁆ ≤ (Lv L (w : G)).pCoreIn 2 ∧
        R L (Kv (w : G)) S₀ (w : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (w : G)) ∧
        IsFaithfulSignalizerType (Kv (w : G)) ∧
        generalizedFitting J = pCore 2 J ∧
        centralizer ((U (Kv (w : G)) S₀).subgroupOf J : Set J) = pCore 2 J ∧
        U (Kv (w : G)) S₀ = (reducedTwoSubgroup J).map J.subtype := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,_,_,hsimple,hline,hfixed,_⟩ :=
    SourceHypothesis.exists_preferred_nonsingular_nontrivial_fixed_not_quasisimple.{_,0} H D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hline,hfixed hz,hsimple,
    H.nonsingular_nonquasisimple_canonical_module D w hw (hfixed hz) hs hi⟩
end CFSG.Quasithin.Chapter12.Section06

