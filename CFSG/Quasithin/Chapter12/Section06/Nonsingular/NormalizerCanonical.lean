module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.SmallThompsonExclusion
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.ThompsonComparison

/-!
# The canonical module in the contrary normalizer branch

Assume the original normalizer N_G(R_v) lies in M. Since T_v is Sylow
in M_v, the finite two-group normalizer condition forces R=R_v for every
selected Sylow S of G_v containing T_v. This does not identify S with T_v.
A.4.10 then gives V_v <= [U,K_v] under nonquasisimplicity. The canonical
module also lies in R_v, so it lies in T_v. The proved Thompson generation
and maximum-elementary counting therefore make its literal quotient action FF.

The actual K_v/O_2(K_v) image has a two-group quotient above it. Its simplicity
and the faithful canonical kernel give the full B.5.1 conclusion, with the
original component image and action. NormalizerLocal applies these results at
the preferred escaping point and retains the original quotient section.

These are the canonical-module inputs to the contrary branch of 12.6.17.
They do not assert general 12.6.13(3), 12.6.15, or normalizer escape.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
12.6.13--15 and 12.6.17, printed pp.826--827, using A.4.10 and B.2.4--7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Normalizer containment forces equality of the original two-signalizers. -/
theorem SourceHypothesis.nonsingular_R_eq_Rv_of_normalizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hN : normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) =
      Rv T L (v : G) := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let R₀ := R L (Kv (v : G)) S₀ (v : G)
  have hTvM : Tv T (v : G) ≤ Mv L (v : G) := (Chapter1.isSylowIn_iff.mp hs).2.1
  have hSM : S₀ ⊓ Mv L (v : G) = Tv T (v : G) :=
    (Chapter1.isSylowIn_iff.mp hs).2.2 _
      ((S.isPGroup'.map _).to_le inf_le_left) (le_inf hTS hTvM) inf_le_right
  obtain ⟨P,hP⟩ := hs.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (v : G) ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  obtain ⟨⟨e⟩,_,_,hLK⟩ := D.nonsingular_local_structure H.chosen H.source.quasisimple v hv
  have hcap := R_inf_Tv_eq_Rv T L (Kv (v : G)) S₀ (v : G)
    H.chosen.sylow_normalizes_component hLK hTS P hP
    (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) e)
  have hRvR : Rv T L (v : G) ≤ R₀ := hcap.symm.le.trans inf_le_left
  apply prime_overgroup_eq_of_normalizer_control (Rv T L (v : G)) R₀ (M L) hN
    ?_ R₀ ((S.isPGroup'.map _).to_le inf_le_left) hRvR le_rfl
  intro B _ hRB hBR hBM
  apply le_antisymm ?_ hRB
  have hBS : B ≤ S₀ := hBR.trans inf_le_left
  have hBT : B ≤ Tv T (v : G) := by
    rw [←hSM]
    exact le_inf hBS (le_inf hBM (hBS.trans (map_subtype_le _)))
  exact (le_inf hBR hBT).trans hcap.le

open ChapterA.Section04

/-- A.4.10 gives 12.6.13(3) whenever the original R equals R_v. -/
theorem SourceHypothesis.nonsingular_moved_le_canonical_of_R_eq
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (S : Sylow 2 (Gv (v : G)))
    (hN : Chapter1.IsSylowIn 2
      (((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ⊓
        normalizer (Lv L (v : G) : Set G))
      (Gv (v : G) ⊓ normalizer (Lv L (v : G) : Set G)))
    (hR : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) =
      Rv T L (v : G))
    (hReq : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) =
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ⊓
        coreQuotientCentralizer (Lv L (v : G))) :
    Vv L V (v : G) ≤
      ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆ := by
  let A := Lv L (v : G)
  let C := Kv (v : G)
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ P
  have hAC : A ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  have hX := (H.nonsingular_local_faithful_signalizer D v hv).2.1
  have hY := H.nonsingular_nonquasisimple_signalizer D v hv hnot
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) (map_subtype_le _)
  have hPC : P ≤ normalizer (C : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv _))
  have hSyl : Chapter1.IsSylowIn 2 P (Gv (v : G)) := ⟨S,rfl⟩
  have hP : Chapter1.IsSylowIn 2 P J := hSyl.restrict le_sup_right hJG
  have hNA : Chapter1.IsSylowIn 2 (P ⊓ normalizer (A : Set G))
      (J ⊓ normalizer (A : Set G)) :=
    hN.restrict (inf_le_inf le_sup_right le_rfl) (inf_le_inf hJG le_rfl)
  have hcore := core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _)
  have hcoreP : J.pCoreIn 2 ≤ P := hcore.trans inf_le_left
  rw [hR] at hcore
  have hcoreN := hcore.trans (Rv_le_normalizer_Lv T L H.chosen.sylow_normalizes_component (v : G))
  have hmod := (SourceChains.source_A410 A C P hAC hX hY hPC hP
    (le_inf hcoreP hcoreN) hNA).2.1
  have he : twoSectionCentralizer A P = Rv T L (v : G) := by
    rw [←hR,hReq]
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
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The contrary normalizer branch of 12.6.17 supplies the original FF module,
without identifying S with T_v. -/
theorem SourceHypothesis.nonsingular_normalizer_canonical_ff
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let J := Kv (v : G) ⊔ S₀
      let E := reducedTwoSubgroup J
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      Tv T (v : G) ≤ S₀ ∧
      Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (v : G) : Set G))
        (Gv (v : G) ⊓ normalizer (Lv L (v : G) : Set G)) ∧
      R L (Kv (v : G)) S₀ (v : G) = Rv T L (v : G) ∧
      generalizedFitting J = pCore 2 J ∧
      centralizer (E : Set J) = pCore 2 J ∧
      U (Kv (v : G)) S₀ = E.map J.subtype ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ ∧
      U (Kv (v : G)) S₀ ≤ Rv T L (v : G) ∧
      IsFFModule (ChapterB.InternalThompsonAction.action E) := by
  obtain ⟨S,hTS,hN,_,_,hReq,_,hF,hker,hred⟩ :=
    H.nonsingular_nonquasisimple_canonical_module D v hv hnot hs hi
  have hR := H.nonsingular_R_eq_Rv_of_normalizer D v hv hs hNM S hTS
  have hm := H.nonsingular_moved_le_canonical_of_R_eq D v hv hTV hnot S hN hR hReq
  let C := Kv (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ S₀
  let E := reducedTwoSubgroup J
  let B := (Lv L (v : G)).subgroupOf J
  let P := (Tv T (v : G)).subgroupOf J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  have hcentral : centralizer (E : Set J) = pCore 2 J := by
    rw [hred] at hker
    change centralizer ((E.map J.subtype).comap J.subtype : Set J) = _ at hker
    rwa [comap_map_eq_self_of_injective J.subtype_injective] at hker
  have hUR : U C S₀ ≤ Rv T L (v : G) := by
    have hcore := core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _)
    rw [hR] at hcore
    rw [U_eq_omegaCenter]
    exact (fun u hu => hcore ((mem_omegaOneCenterAmbient_iff _ _).mp hu).1)
  refine ⟨S,hTS,hN,hR,hF,hcentral,hred,hm,hUR,?_⟩
  have hBJ : Lv L (v : G) ≤ J := (H.nonsingular_canonical_component D v hv).2.1.trans le_sup_left
  have hPJ : Tv T (v : G) ≤ J := hTS.trans le_sup_right
  have hB : B.map J.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le hBJ
  obtain ⟨P₀,hP₀⟩ := hs.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (v : G) ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  have hRT : Rv T L (v : G) ≤ Tv T (v : G) := (pCoreIn_le_sylow _ P₀).trans hP₀.le
  have hEP : E ≤ P := by
    intro e he
    exact hRT (hUR (hred.symm ▸ mem_map_of_mem J.subtype he))
  have hgen : B = ⁅B,elementaryAbelianMaxJ P⁆ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,hB,←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hPJ]
    exact H.local_thompson_generation D v hv hTV hs
      (H.nonsingular_thompson_not_le_core_of_not_quasisimple D v hv hTV hnot hs hi he)
  have hWU : Vv L V (v : G) ≤ E.map J.subtype := by
    rw [hred] at hm
    exact hm.trans (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans (by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
        E.le_normalizer_map J.subtype)))
  have hmove : ⁅E,B⁆ ≠ ⊥ := by
    intro hz
    have hc : E.map J.subtype ≤ centralizer (Lv L (v : G) : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←hB,←map_commutator,hz,Subgroup.map_bot]
    have hw : Vv L V (v : G) = ⊥ := by
      rw [←D.local_moved_generated H.chosen v hv]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hWU.trans hc)
    have hcard := D.nonsingular_moved_card H.chosen v hv
    rw [hw,card_bot] at hcard
    norm_num at hcard
  exact ChapterB.ff_of_thompson_generated_movement E B P hEP hgen hmove
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- B.5.1 on the actual canonical action, retaining its literal component quotient. -/
theorem SourceHypothesis.nonsingular_canonical_quasisimple_of_ff
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Subgroup G) (hSG : S ≤ Gv (v : G)) (hS : IsPGroup 2 S)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔ S : Subgroup G) :
      Set (Kv (v : G) ⊔ S : Subgroup G)) = pCore 2 (Kv (v : G) ⊔ S : Subgroup G))
    (hff : let E := reducedTwoSubgroup (Kv (v : G) ⊔ S : Subgroup G)
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      IsFFModule (ChapterB.InternalThompsonAction.action E)) :
    let J := Kv (v : G) ⊔ S
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    let q := ChapterB.InternalThompsonAction.actionMk E
    let ρ := ChapterB.InternalThompsonAction.action E
    let B := ((Kv (v : G)).subgroupOf J).map q
    generalizedFitting (ChapterB.InternalThompsonAction.ActionQuotient E) = B ∧
      centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient E)) = ⊥ ∧
      B ≤ offenderSubgroup ρ ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp (offenderSubgroup ρ).subtype) (B.subgroupOf (offenderSubgroup ρ))) := by
  let C := Kv (v : G)
  let J := C ⊔ S
  let A := C.subgroupOf J
  let P := S.subgroupOf J
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let B := A.map q
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) hSG
  have hnA : J ≤ normalizer (C : Set G) :=
    hJG.trans ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnA
  let : B.Normal := (inferInstance : A.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := H.nonsingular_canonical_component_image D v hv S hSG hker
  obtain ⟨_,_,_,hq,hsi⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star C) := hq
  let : IsSimpleGroup (Star C) := hsi
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup B := e.isSimpleGroup
  have hP : IsPGroup 2 P :=
    hS.comap_subtype
  have hgen : A ⊔ P = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show S ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (ChapterB.InternalThompsonAction.ActionQuotient E ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (P.map q) (hP.map q) (by
      rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)])
  have hcore : pCore 2 (ChapterB.InternalThompsonAction.ActionQuotient E) = ⊥ :=
    isPReduced_reducedPSubgroup.quotient_pCore_eq_bot
  have hsqG : IsSQTK KnownSimple.IsKnownSimple (Gv (v : G)) :=
    H.source.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ v.property)
        (fun hh => nonsingular_ne_one D hv (Subtype.ext hh))))
  have hsqC : IsSQTK KnownSimple.IsKnownSimple C :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (Kv_le_Gv (v : G)))).mp (hsqG.subgroup _)
  have hsqStar : IsSQTK KnownSimple.IsKnownSimple (Star C) := by
    refine ⟨?_,hsqC.isKGroup.of_surjective (QuotientGroup.mk' (pCore 2 C))
      (QuotientGroup.mk'_surjective _)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 C) pCore_isPGroup]
    exact hsqC.stronglyQuasithin p hp ho
  have hclass := ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    (ChapterB.InternalThompsonAction.action E) B hquot hcore
    ((IsSQTK.equiv e).mpr hsqStar) (ChapterB.InternalThompsonAction.action_faithful E) hff
  exact ⟨generalizedFitting_eq_of_quasisimple_two_quotient B hquot hcore,
    centralizer_eq_bot_of_simple_two_quotient B (Group.IsPerfect.not_isMulCommutative B) hquot hcore,
    hclass⟩
end CFSG.Quasithin.Chapter12.Section06
