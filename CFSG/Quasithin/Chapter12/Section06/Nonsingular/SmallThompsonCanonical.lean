module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NonquasisimpleModule
public import Theory.Representation.NormalElementaryQuotient.ThompsonEscape

/-!
# The canonical module in the small Thompson branch

Assume the original J(T_v) lies in Q and K_v is not quasisimple.
The proved Sylow geometry identifies S=T_v and R=R_v. Since the literal
V_v lies in the omega-center of R_v and is fully moved by L_v, A.4.10(2)
gives V_v <= [U,K_v]. This proves 12.6.13(3) in this source branch.

The canonical-module theorem identifies U with the ambient image of
R_2(K_vT_v), whose centralizer is O_2(K_vT_v). If its faithful action were
not FF, the elementary Thompson subgroup would be normal in K_vT_v.
Source 12.6.8 places its ambient normalizer in M, contradicting K_v not
contained in M. Thus the original canonical action is FF. The normal-kernel
bound places the actual simple K_v/O_2(K_v) image in its full offender
subgroup, and the proved B.5 classifier applies to that same action.

At the preferred escaping point with nontrivial original C_V(L), the
previous original-action argument discharges nonquasisimplicity. The
small-Thompson condition remains an explicit branch to be excluded by
its local embedding analysis. The general 12.6.13(3), HS/J4 exclusions,
block construction, splitting and fixed-space elimination remain open;
neither 12.6.2 nor 12.6.23 is asserted here. Earlier T-invariance and TI
retain producer qt-d-1222-source and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, 12.6.13--15, printed p.826, A.4.10, p.60,
and B.2.5--7, p.76. All groups, actions and quotient maps are the literal
original ones from Section06.Setup.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Source 12.6.13(3) for the original small Thompson branch, via the actual A.4.10 chain. -/
theorem SourceHypothesis.small_thompson_moved_le_canonical_commutator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L) :
    Vv L V (v : G) ≤ ⁅U (Kv (v : G)) (Tv T (v : G)),Kv (v : G)⁆ := by
  let A := Lv L (v : G)
  let C := Kv (v : G)
  let P := Tv T (v : G)
  let J := C ⊔ P
  have hAC : A ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  have hX := (H.nonsingular_local_faithful_signalizer D v hv).2.1
  have hY := H.nonsingular_nonquasisimple_signalizer D v hv hnot
  obtain ⟨S,hTS,hN⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨hS,hR,_,_,_⟩ := H.nonsingular_small_thompson D v hv hs hJ S hTS
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hPC : P ≤ normalizer (C : Set G) := inf_le_right.trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv _))
  have hSyl : Chapter1.IsSylowIn 2 P (Gv (v : G)) := ⟨S,hS⟩
  have hP : Chapter1.IsSylowIn 2 P J := hSyl.restrict le_sup_right hJG
  have hNA : Chapter1.IsSylowIn 2 (P ⊓ normalizer (A : Set G))
      (J ⊓ normalizer (A : Set G)) := by
    have hN' : Chapter1.IsSylowIn 2 (P ⊓ normalizer (A : Set G))
        (Gv (v : G) ⊓ normalizer (A : Set G)) := by
      obtain ⟨N,hN⟩ := hN
      exact ⟨N,by simpa only [hS] using hN⟩
    exact hN'.restrict (inf_le_inf le_sup_right le_rfl) (inf_le_inf hJG le_rfl)
  have hcore : J.pCoreIn 2 ≤ Rv T L (v : G) := by
    have hh := core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _)
    rw [hR,hS] at hh
    exact hh
  have hRnorm := Rv_le_normalizer_Lv T L H.chosen.sylow_normalizes_component (v : G)
  have hcoreP : J.pCoreIn 2 ≤ P := by
    have hh := (core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _)).trans inf_le_left
    rwa [hS] at hh
  have hmod := (SourceChains.source_A410 A C P hAC hX hY hPC hP
    (le_inf hcoreP (hcore.trans hRnorm)) hNA).2.1
  have he : twoSectionCentralizer A P = Rv T L (v : G) := by
    have hrP : Rv T L (v : G) ≤ P := by
      rw [←hR]
      exact (R_le_S L C _ (v : G)).trans hS.le
    have heq := R_inf_Tv_eq_Tv_inf_coreQuotientCentralizer T L C _ (v : G)
      H.chosen.sylow_normalizes_component hAC hTS
    rw [hR,inf_of_le_left hrP] at heq
    rw [heq]
    ext r
    rw [mem_twoSectionCentralizer,mem_inf,mem_coreQuotientCentralizer_iff]
  rw [he,signalizerModule_eq_commutator_omegaCenter,
    signalizerModule_eq_commutator_omegaCenter,commutator_comm A] at hmod
  have hW : Vv L V (v : G) ≤ omegaOneCenterAmbient (Rv T L (v : G)) := by
    have hw := H.moved_le_omega_center_Rv D v hv hTV
    rw [←map_omegaOneAmbient_injective _ (Rv T L (v : G)).subtype_injective] at hw
    exact hw
  rw [U_eq_omegaCenter,commutator_comm _ C]
  exact (show Vv L V (v : G) = ⁅Vv L V (v : G),A⁆ from
    (D.local_moved_generated H.chosen v hv).symm).le.trans
      ((commutator_mono hW le_rfl).trans hmod)
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open ChapterA.Section04 Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The escaping small branch makes the canonical module FF, retaining its actual two-core kernel. -/
theorem SourceHypothesis.small_thompson_canonical_ff
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    let J := Kv (v : G) ⊔ Tv T (v : G)
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    generalizedFitting J = pCore 2 J ∧
      centralizer (E : Set J) = pCore 2 J ∧
      U (Kv (v : G)) (Tv T (v : G)) = E.map J.subtype ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) (Tv T (v : G)),Kv (v : G)⁆ ∧
      IsFFModule (ChapterB.InternalThompsonAction.action E) := by
  obtain ⟨S,hTS,_,_,_,_,_,hF,hker,hred⟩ :=
    H.nonsingular_nonquasisimple_canonical_module D v hv hnot hs hi
  obtain ⟨hS,_,_,_,hN⟩ := H.nonsingular_small_thompson D v hv hs hJ S hTS
  rw [hS] at hF hker hred hN
  let J := Kv (v : G) ⊔ Tv T (v : G)
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  have hcentral : centralizer (E : Set J) = pCore 2 J := by
    rw [hred] at hker
    change centralizer ((E.map J.subtype).comap J.subtype : Set J) = _ at hker
    rwa [comap_map_eq_self_of_injective J.subtype_injective] at hker
  refine ⟨hF,hcentral,hred,
    H.small_thompson_moved_le_canonical_commutator D v hv hTV hnot hs hJ,?_⟩
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hSyl : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Gv (v : G)) := ⟨S,hS⟩
  obtain ⟨P,hP⟩ := hSyl.restrict (show Tv T (v : G) ≤ J from le_sup_right) hJG
  have hNM : normalizer ((elementaryAbelianMaxJ (P : Subgroup J)).map J.subtype : Set G) ≤ M L := by
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,hP]
    exact hN
  exact NormalElementaryQuotient.ff_of_thompson_normalizer_escape J (M L) P E
    (hcentral.symm ▸ pCore_isPGroup) (fun h => he (le_sup_left.trans h)) hNM
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The faithful canonical action retains the original K_v/O₂(K_v) quotient. -/
theorem SourceHypothesis.nonsingular_canonical_component_image
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Subgroup G) (hSG : S ≤ Gv (v : G))
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔ S : Subgroup G) :
      Set (Kv (v : G) ⊔ S : Subgroup G)) = pCore 2 (Kv (v : G) ⊔ S : Subgroup G)) :
    Nonempty ((((Kv (v : G)).subgroupOf (Kv (v : G) ⊔ S)).map
      (ChapterB.InternalThompsonAction.actionMk
        (reducedTwoSubgroup (Kv (v : G) ⊔ S : Subgroup G)))) ≃* Star (Kv (v : G))) := by
  let C := Kv (v : G)
  let J := C ⊔ S
  let B := C.subgroupOf J
  let E := reducedTwoSubgroup J
  let q := ChapterB.InternalThompsonAction.actionMk E
  let f := q.subgroupMap B
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) hSG
  have hc : B.IsCComponent := (H.nonsingular_canonical_component D v hv).1.subgroupOf_of_le
    le_sup_left hJG
  have hk : f.ker = pCore 2 B := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk',hker]
    exact (pCore_subnormal_eq_comap 2 hc.subnormal).symm
  let e : B ≃* C := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective B)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)))⟩

/-- Failure of factorization contains the whole original simple component image. -/
theorem SourceHypothesis.small_thompson_canonical_offender_component
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    let J := Kv (v : G) ⊔ Tv T (v : G)
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    ((Kv (v : G)).subgroupOf J).map (ChapterB.InternalThompsonAction.actionMk E) ≤
      offenderSubgroup (ChapterB.InternalThompsonAction.action E) := by
  let C := Kv (v : G)
  let S := Tv T (v : G)
  let J := C ⊔ S
  let B := C.subgroupOf J
  let P := S.subgroupOf J
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let O := offenderSubgroup (ChapterB.InternalThompsonAction.action E)
  let N := O.comap q
  let : O.Normal := offenderSubgroup_normal _
  let : N.Normal := inferInstance
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hnB : J ≤ normalizer (C : Set G) :=
    hJG.trans ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  let : B.Normal := normal_subgroupOf_of_le_normalizer hnB
  have hB : B.IsCComponent := (H.nonsingular_canonical_component D v hv).1.subgroupOf_of_le
    le_sup_left hJG
  obtain ⟨_,_,_,hq,hsimple⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star C) := hq
  let : IsSimpleGroup (Star C) := hsimple
  let b : B ≃* C := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let eq : (B ⧸ pCore 2 B) ≃* Star C := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eq.symm
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eq.isSimpleGroup
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (B ⧸ pCore 2 B)) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  have hP : IsPGroup 2 P :=
    (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  have hgen : B ⊔ P = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show S ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨_,hker,_,_,hff⟩ := H.small_thompson_canonical_ff D v hv hTV hnot hs hi hJ he
  have hk : q.ker = pCore 2 J := (QuotientGroup.ker_mk' _).trans hker
  apply map_le_iff_le_comap.mpr
  by_contra hBN
  have hQN : pCore 2 J ≤ N := by
    rw [←hk]
    exact MonoidHom.ker_le_comap _ _
  have hb := (QuasisimpleKernel.normal_kernel_structure B P N hB hP hgen hQN hBN).1
  rw [hz,MonoidHom.comap_bot,QuotientGroup.ker_mk'] at hb
  have hN : N ≤ q.ker := by
    rw [hk]
    exact hb.trans (sup_le le_rfl (pCoreIn_le_of_subnormal 2 hB.subnormal))
  apply offenderSubgroup_ne_bot_of_ff _ hff
  apply bot_unique
  intro x hx
  obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (E : Set J)) x
  exact hN hx

/-- The small branch enters the proved B.5 classifier on its original canonical module,
with the actual simple component image, rather than a group-family label. -/
theorem SourceHypothesis.small_thompson_canonical_classification
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    let J := Kv (v : G) ⊔ Tv T (v : G)
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    let q := ChapterB.InternalThompsonAction.actionMk E
    let ρ := ChapterB.InternalThompsonAction.action E
    let B := ((Kv (v : G)).subgroupOf J).map q
    generalizedFitting J = pCore 2 J ∧
      centralizer (E : Set J) = pCore 2 J ∧
      U (Kv (v : G)) (Tv T (v : G)) = E.map J.subtype ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) (Tv T (v : G)),Kv (v : G)⁆ ∧
      IsFFModule ρ ∧ B ≤ offenderSubgroup ρ ∧
      Nonempty (B ≃* Star (Kv (v : G))) ∧
      ChapterB.SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) := by
  let J := Kv (v : G) ⊔ Tv T (v : G)
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let ρ := ChapterB.InternalThompsonAction.action E
  obtain ⟨hF,hker,hred,hm,hff⟩ := H.small_thompson_canonical_ff D v hv hTV hnot hs hi hJ he
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hsqG : IsSQTK KnownSimple.IsKnownSimple (Gv (v : G)) :=
    H.source.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ v.property)
        (fun hh => nonsingular_ne_one D hv (Subtype.ext hh))))
  have hsq : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp (hsqG.subgroup _)
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (ChapterB.InternalThompsonAction.ActionQuotient E) := {
    Cover := J
    kernel := centralizer (E : Set J)
    sqtk := hsq
    equiv := MulEquiv.refl _ }
  exact ⟨hF,hker,hred,hm,hff,
    H.small_thompson_canonical_offender_component D v hv hTV hnot hs hi hJ he,
    H.nonsingular_canonical_component_image D v hv _ inf_le_right hker,
    ChapterB.SourceInduction.offenderSubgroup_adequateAlternative ρ
      (ChapterB.InternalThompsonAction.action_faithful E)
      isPReduced_reducedPSubgroup.quotient_pCore_eq_bot c⟩

/-- The original preferred point with nontrivial fixed space discharges nonquasisimplicity
and carries the complete canonical action into B.5 in the small Thompson branch. -/
theorem SourceHypothesis.exists_preferred_nonsingular_small_canonical_classification_of_fixed
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
      (elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
        let J := Kv (w : G) ⊔ Tv T (w : G)
        let E := reducedTwoSubgroup J
        letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
        generalizedFitting J = pCore 2 J ∧
          centralizer (E : Set J) = pCore 2 J ∧
          U (Kv (w : G)) (Tv T (w : G)) = E.map J.subtype ∧
          Vv L V (w : G) ≤ ⁅U (Kv (w : G)) (Tv T (w : G)),Kv (w : G)⁆ ∧
          IsFFModule (ChapterB.InternalThompsonAction.action E) ∧
          ((Kv (w : G)).subgroupOf J).map (ChapterB.InternalThompsonAction.actionMk E) ≤
            offenderSubgroup (ChapterB.InternalThompsonAction.action E) ∧
          Nonempty ((((Kv (w : G)).subgroupOf J).map
            (ChapterB.InternalThompsonAction.actionMk E)) ≃* Star (Kv (w : G))) ∧
          ChapterB.SourceInduction.AdequateAlternative
            ((ChapterB.InternalThompsonAction.action E).comp
              (offenderSubgroup (ChapterB.InternalThompsonAction.action E)).subtype)) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,_,_,hsimple,hline,hfixed,_⟩ :=
    SourceHypothesis.exists_preferred_nonsingular_nontrivial_fixed_not_quasisimple.{_,0}
      H D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hline,hfixed hz,hsimple,
    fun hJ => H.small_thompson_canonical_classification D w hw hTV (hfixed hz) hs hi hJ hnot⟩
end CFSG.Quasithin.Chapter12.Section06
