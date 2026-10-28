module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ThompsonCases
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage

/-!
# The actual reduced action in the equal-residual branch

At the preferred nonsingular point, R₂(G_v) centralizes V_v because the
latter lies in O₂(G_v). The proved centralizer control places R₂(G_v) in
M_v, and its relative normality puts it in the selected Sylow subgroup T_v,
then in R_v. No inclusion of V_v in R₂(G_v) is assumed.

The fully moved V_v lies in the intrinsic signalizer module of L_v.
A.4.11 therefore makes L_v move R₂(G_v), using the actual A₆ quotient to
supply its chief-factor hypothesis. Thompson generation now gives an
FF-module on R₂(G_v); the original L_v-image lies in the subgroup generated
by best offenders and is isomorphic to A₆ through the original centralizer
quotient. The full proved B.5 classifier applies to this literal action.
The final theorem constructs these inputs at the same preferred escaping
point and discharges the Thompson-generation premise.

The comparison of the B.5 alternatives must still identify
[R₂(G_v),L_v] with V_v and contradict its established nonnormality.
Neither 12.6.11 nor the full 12.6.2/12.6.23 theorem family is asserted here.
The earlier T-invariance and TI inputs retain producer qt-d-1222-source
and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the final
paragraph of Lemma 12.6.11, printed p.825, using A.4.11 and B.5.1/6.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem reduced_map_normalized (A : Subgroup G) :
    A ≤ normalizer ((reducedTwoSubgroup A).map A.subtype : Set G) := by
  simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using
    (reducedTwoSubgroup A).le_normalizer_map A.subtype

/-- The actual reduced subgroup lies inside the selected T_v, and then R_v. -/
theorem SourceHypothesis.reduced_point_le_local_core
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (v : V)
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G))
    (hc : Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L) :
    (reducedTwoSubgroup (Gv (v : G))).map (Gv (v : G)).subtype ≤ Tv T (v : G) ∧
      (reducedTwoSubgroup (Gv (v : G))).map (Gv (v : G)).subtype ≤ Rv T L (v : G) := by
  let A := Gv (v : G)
  let U := (reducedTwoSubgroup A).map A.subtype
  have hUA : U ≤ A := map_subtype_le _
  have hUc : U ≤ centralizer (Vv L V (v : G) : Set G) := by
    rintro _ ⟨u,hu,rfl⟩ w hw
    obtain ⟨w,hqw,rfl⟩ := Vv_le_core_Gv_of_normalized H.chosen v hn hw
    exact congrArg A.subtype (reducedPSubgroup_le_centralizer_pCore 2 A hu w hqw)
  have hUM : U ≤ Mv L (v : G) := le_inf ((le_inf hUA hUc).trans hc) hUA
  have hnU := reduced_map_normalized A
  have hp : IsPGroup 2 U :=
    (pCore_isPGroup.to_le (reducedPSubgroup_le_pCore 2 A)).map A.subtype
  have hUT : U ≤ Tv T (v : G) := by
    obtain ⟨P,hP⟩ := hTv
    exact (le_pCoreIn_of_normalizes hp hUM (inf_le_right.trans hnU)).trans
      ((pCoreIn_le_sylow _ P).trans hP.le)
  exact ⟨hUT,le_pCoreIn_of_normalizes hp
    (hUT.trans (inf_le_inf le_sup_right le_rfl)) (inf_le_right.trans hnU)⟩

/-- The source V_v lies in the intrinsic signalizer module of L_v. -/
theorem OrthogonalMarking.moved_le_intrinsic
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L))
    (v : V) (hv : D.Nonsingular v) :
    Vv L V (v : G) ≤ ChapterA.Section04.intrinsicSignalizerModule (Lv L (v : G)) := by
  let W := Vv L V (v : G)
  let B := Lv L (v : G)
  have hr := D.local_residual_moved_isReduced chosen hq v hv
  have hWQ : W ≤ B.pCoreIn 2 := Vv_le_core_Lv chosen v
  have hWΩ : W ≤ omegaOneCenterAmbient (B.pCoreIn 2) := by
    intro w hw
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hWQ hw, ?_, ?_⟩
    · let := Vv_elementary chosen.normalizes (v : G)
      exact elemPow_eq_one_of_isElementaryAbelian _ hw
    · intro q hq
      obtain ⟨q,hq,rfl⟩ := hq
      exact congrArg B.subtype (hr.le_centralizer_pCore (show (⟨w,Vv_le_Lv chosen v hw⟩ : B) ∈ W.subgroupOf B from hw) q hq)
  rw [←D.local_moved_generated chosen v hv]
  unfold ChapterA.Section04.intrinsicSignalizerModule
  rw [ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter]
  change ⁅W,B⁆ ≤ ⁅B,omegaOneCenterAmbient (B.pCoreIn 2)⁆
  rw [commutator_comm B]
  exact commutator_mono hWΩ le_rfl

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- A.4.11 detects the actual L_v on the reduced module of its point centralizer. -/
theorem SourceHypothesis.reduced_point_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    ⁅(reducedTwoSubgroup (Gv (v : G))).map (Gv (v : G)).subtype,Lv L (v : G)⁆ ≠ ⊥ := by
  let A := Gv (v : G)
  let B := (Lv L (v : G)).subgroupOf A
  let eB := subgroupOfEquivOfLe (Lv_le_Gv L (v : G))
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  have hB : B.map A.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le (Lv_le_Gv L (v : G))
  have hp : IsPPerfect 2 B := (isPPerfect_embedded_pResidual 2 (CLv L (v : G))).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let eQ : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans e
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eQ.symm
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 B) := by
    apply (hasCentralPChiefFactorsAbove_iff_quotient _).mpr
    exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient ⊥ (by simp)
      (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  have hne : ChapterA.Section04.intrinsicSignalizerModule (Lv L (v : G)) ≠ ⊥ := by
    intro hz
    have hW : Vv L V (v : G) = ⊥ := bot_unique
      ((D.moved_le_intrinsic H.chosen H.source.quasisimple v hv).trans_eq hz)
    have hh := D.nonsingular_moved_card H.chosen v hv
    rw [hW,card_bot] at hh
    norm_num at hh
  have hneB : ChapterA.Section04.intrinsicSignalizerModule B ≠ ⊥ := by
    intro hz
    have hh := ChapterA.Section04.intrinsicSignalizerModule_map_of_injective A.subtype A.subtype_injective B
    rw [hB,hz,Subgroup.map_bot] at hh
    exact hne hh
  have hm := ChapterA.Section04.reduced_commutator_ne_bot_of_intrinsicModule_ne_bot B
    (inferInstance : B.Normal).isSubnormal hp hchief hneB
  intro hz
  apply hm
  apply (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
  rw [map_commutator,hB]
  exact hz

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Thompson generation supplies failure of factorization on the original R₂(G_v),
and places the original L_v-image in its full best-offender subgroup. -/
theorem SourceHypothesis.reduced_point_ff
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G))
    (hc : Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L)
    (hg : Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆) :
    let U := reducedTwoSubgroup (Gv (v : G))
    let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    IsFFModule ρ ∧
      ((Lv L (v : G)).subgroupOf (Gv (v : G))).map
        (ChapterB.InternalThompsonAction.actionMk U) ≤ offenderSubgroup ρ := by
  let A := Gv (v : G)
  let U := reducedTwoSubgroup A
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let B := (Lv L (v : G)).subgroupOf A
  let S := (Tv T (v : G)).subgroupOf A
  let J := elementaryAbelianMaxJ S
  have hBA : Lv L (v : G) ≤ A := Lv_le_Gv L _
  have hSA : Tv T (v : G) ≤ A := inf_le_right
  have hB : B.map A.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le hBA
  have hJ : J.map A.subtype = elementaryAbelianMaxJ (Tv T (v : G)) := by
    rw [←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,
      map_subgroupOf_eq_of_le hSA]
  have hgen : B = ⁅B,J⁆ := by
    apply map_injective A.subtype_injective
    rw [map_commutator,hB,hJ]
    exact hg
  have hUS : U ≤ S := by
    intro u hu
    exact (H.reduced_point_le_local_core v hTv hn hc).1 (mem_map_of_mem A.subtype hu)
  have hm : ⁅U,B⁆ ≠ ⊥ := by
    intro hz
    apply H.reduced_point_moved D v hv hn
    have hh := congrArg (map A.subtype) hz
    rwa [map_commutator,hB,Subgroup.map_bot] at hh
  have hJB : J.map q ≤ offenderSubgroup ρ := by
    rw [map_le_iff_le_comap]
    apply sSup_le
    intro E hE
    apply map_le_iff_le_comap.mp
    by_cases he : E.map q = ⊥
    · rw [he]
      exact bot_le
    · exact (NormalElementaryQuotient.maxElementary_isBestOffender U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) S E hUS hE he).le_offenderSubgroup ρ
  have hBO : B.map q ≤ offenderSubgroup ρ := by
    let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
    rw [hgen,map_commutator]
    exact (commutator_mono le_rfl hJB).trans (commutator_le_right _ _)
  refine ⟨?_,hBO⟩
  by_contra hff
  have hJker : J ≤ q.ker := by
    apply sSup_le
    intro E hE
    apply (map_eq_bot_iff E).mp
    by_contra he
    exact hff ((isFFModule_iff_exists_bestOffender ρ).mpr ⟨_,
      NormalElementaryQuotient.maxElementary_isBestOffender U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) S E hUS hE he⟩)
  have hBker : B ≤ q.ker := by
    rw [hgen]
    exact (commutator_mono le_rfl hJker).trans (commutator_le_right _ _)
  apply hm
  rw [commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  simpa only [q,ChapterB.InternalThompsonAction.actionMk,QuotientGroup.ker_mk'] using hBker

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The L_v-image on R₂(G_v) is its original A₆ quotient, not a family label. -/
theorem SourceHypothesis.reduced_point_actor
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    let U := reducedTwoSubgroup (Gv (v : G))
    Nonempty ((((Lv L (v : G)).subgroupOf (Gv (v : G))).map
      (ChapterB.InternalThompsonAction.actionMk U)) ≃* alternatingGroup (Fin 6)) := by
  let A := Gv (v : G)
  let U := reducedTwoSubgroup A
  let B := (Lv L (v : G)).subgroupOf A
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let eB := subgroupOfEquivOfLe (Lv_le_Gv L (v : G))
  have hB : B.map A.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le (Lv_le_Gv L (v : G))
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let eQ : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans e
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eQ.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro x hx
    have hc : eQ x ∈ center (alternatingGroup (Fin 6)) := by
      rw [mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z,rfl⟩ := eQ.surjective y
      simpa only [map_mul] using congrArg eQ (hx z)
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc
    exact mem_bot.mpr (eQ.injective (hc.trans eQ.map_one.symm))
  have hm : ⁅U,B⁆ ≠ ⊥ := by
    intro hz
    apply H.reduced_point_moved D v hv hn
    have hh := congrArg (map A.subtype) hz
    rwa [map_commutator,hB,Subgroup.map_bot] at hh
  exact ⟨(reducedQuasisimpleImageEquiv U B isPReduced_reducedPSubgroup hz hm).symm.trans eQ⟩

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual preferred equal-residual branch supplies all inputs to B.5:
the original reduced module lies in R_v, its action is FF, the L_v-image is
A₆ inside the full offender subgroup, and the complete adequate classifier
applies to that very action. The remaining comparison must identify its
L_v-moved subgroup with V_v. -/
theorem SourceHypothesis.exists_preferred_reduced_point_classification
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (Lv L (w : G) = Kv (w : G) →
        let A := Gv (w : G)
        let U := reducedTwoSubgroup A
        letI : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
        let ρ := ChapterB.InternalThompsonAction.action U
        let B := ((Lv L (w : G)).subgroupOf A).map
          (ChapterB.InternalThompsonAction.actionMk U)
        U.map A.subtype ≤ Rv T L (w : G) ∧
        ¬ ((Vv L V (w : G)).subgroupOf A).Normal ∧
        IsFFModule ρ ∧ B ≤ offenderSubgroup ρ ∧
        Nonempty (B ≃* alternatingGroup (Fin 6)) ∧
        ChapterB.SourceInduction.AdequateAlternative
          (ρ.comp (offenderSubgroup ρ).subtype)) := by
  obtain ⟨w,hw,he,hs,hi,hred⟩ :=
    H.exists_preferred_nonsingular_Kv_reductions D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,?_⟩
  intro heq
  have hn : Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [heq]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)
  have hc : Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L :=
    (inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _)).trans (hred heq).2.2.1
  have hJ : ¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L := by
    intro hJ
    exact H.small_thompson_moves_normal_overmodule D w hw hs hJ he hc
      (componentOrbit (Vv L V (w : G)) (Gv (w : G)))
      (le_componentOrbit _ _) (le_normalizer_componentOrbit _ _)
      (H.small_thompson_closure_centralized D w hw hTV hs hJ heq)
  have hg := (H.nonsingular_thompson_generation D w hw hTV hs hJ).2.1
  have hff := H.reduced_point_ff D w hw hs hn hc hg
  let A := Gv (w : G)
  let U := reducedTwoSubgroup A
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let ρ := ChapterB.InternalThompsonAction.action U
  have hsq : IsSQTK KnownSimple.IsKnownSimple A := H.source.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ w.property)
      (fun hh => nonsingular_ne_one D hw (Subtype.ext hh))))
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (ChapterB.InternalThompsonAction.ActionQuotient U) := {
    Cover := A
    kernel := centralizer (U : Set A)
    sqtk := hsq
    equiv := MulEquiv.refl _ }
  refine ⟨(H.reduced_point_le_local_core w hs hn hc).2,(hred heq).2.2.2,
    hff.1,hff.2,H.reduced_point_actor D w hw hn,?_⟩
  exact ChapterB.SourceInduction.offenderSubgroup_adequateAlternative ρ
    (ChapterB.InternalThompsonAction.action_faithful U)
    isPReduced_reducedPSubgroup.quotient_pCore_eq_bot c

end CFSG.Quasithin.Chapter12.Section06
