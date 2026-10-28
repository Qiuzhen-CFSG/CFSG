module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.SmallThompsonCanonical
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# The original local embedding in the small Thompson branch

Assume J(T_v) lies in Q and K_v escapes M. The original Sylow theorem
identifies S with T_v and R with R_v. Normalizer control for J(Q) then
places N_G(R_v) in M. Consequently O_2(K_vT_v) is properly contained in
R_v. The image R_v* in the literal two-core quotient is nontrivial, and
lifting its normalizer places that normalizer in M_v*.

The image of L_v is a proper subgroup of the image of K_v, retains its
A_6 two-core quotient, and is a local C-component for the image of T_v,
which is an actual Sylow subgroup. The original definition of R also
retains its action on L_v*/O_2(L_v*). On the faithful canonical module,
the simple component is the generalized Fitting subgroup and has trivial
centralizer. The proved B.5.1 classifier therefore supplies its full
quasisimple conclusion on the actual offender subgroup.

The preferred-point consumer discharges nonquasisimplicity when the
original C_V(L) is nontrivial. The remaining local-model exclusion of
12.6.14, HS/J4 exclusions, general 12.6.13(3), blocks, splitting and
fixed-space elimination remain open. Neither 12.6.2 nor 12.6.23 is asserted.
Earlier T-invariance and TI retain producer qt-d-1222-source and final
discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, Lemma 12.6.14, printed p.826, and B.5.1,
printed pp.99--103, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Normalizer uniqueness forces strict two-core containment in the literal R_v. -/
theorem SourceHypothesis.small_thompson_core_lt_local_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    (Kv (v : G) ⊔ Tv T (v : G)).pCoreIn 2 < Rv T L (v : G) ∧
      normalizer (Rv T L (v : G) : Set G) ≤ M L := by
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨hS,hR,_,hJR,_⟩ := H.nonsingular_small_thompson D v hv hs hJ S hTS
  have hN : normalizer (Rv T L (v : G) : Set G) ≤ M L := by
    apply (normalizer_le_normalizer_elementaryAbelianMaxJ _).trans
    rw [hJR]
    exact H.core_thompson_normalizer
  have hcore := core_le_R_of_sylow L (Kv (v : G)) (v : G) S (Kv_le_Gv _)
  rw [hR,hS] at hcore
  refine ⟨lt_of_le_of_ne hcore ?_,hN⟩
  intro heq
  apply he
  have hn : (Kv (v : G) ⊔ Tv T (v : G) : Subgroup G) ≤
      normalizer ((Kv (v : G) ⊔ Tv T (v : G)).pCoreIn 2 : Set G) :=
    (Kv (v : G) ⊔ Tv T (v : G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact le_sup_left.trans ((heq ▸ hn).trans hN)

/-- The nontrivial original R_v image has its quotient normalizer in M_v*. -/
theorem SourceHypothesis.small_thompson_local_image
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    let J := Kv (v : G) ⊔ Tv T (v : G)
    let R := (Rv T L (v : G)).subgroupOf J
    let q := QuotientGroup.mk' (pCore 2 J)
    (R.map q).comap q = R ∧ R.map q ≠ ⊥ ∧ IsPGroup 2 (R.map q) ∧
      normalizer (R.map q : Set (Star J)) ≤
        ((Mv L (v : G)).subgroupOf J).map q := by
  let J := Kv (v : G) ⊔ Tv T (v : G)
  let R := (Rv T L (v : G)).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  obtain ⟨hcore,hN⟩ := H.small_thompson_core_lt_local_centralizer D v hv hs hJ he
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨hS,hR,_,_,_⟩ := H.nonsingular_small_thompson D v hv hs hJ S hTS
  have hRT : Rv T L (v : G) ≤ Tv T (v : G) := by
    rw [←hR]
    exact (R_le_S L (Kv (v : G)) _ (v : G)).trans hS.le
  have hRJ : Rv T L (v : G) ≤ J := hRT.trans le_sup_right
  have hk : q.ker ≤ R := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hcore.le (mem_map_of_mem J.subtype hx)
  have hpre : (R.map q).comap q = R := comap_map_eq_self hk
  refine ⟨hpre,?_,(isPGroup_pCoreIn 2 _).comap_subtype.map q,?_⟩
  · intro hz
    have hle := (map_eq_bot_iff R).mp hz
    rw [QuotientGroup.ker_mk'] at hle
    apply hcore.not_ge
    intro x hx
    exact mem_map_of_mem J.subtype (hle (show (⟨x,hRJ hx⟩ : J) ∈ R from hx))
  · intro x hx
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 J) x
    have hy : y ∈ normalizer (R : Set J) := by
      have hh := (R.map q).le_normalizer_comap q (show y ∈ (normalizer (R.map q : Set (Star J))).comap q from hx)
      rwa [hpre] at hh
    have hyR : (y : G) ∈ normalizer (Rv T L (v : G) : Set G) := by
      rwa [←subgroupOf_normalizer_eq hRJ] at hy
    exact mem_map_of_mem q (show y ∈ (Mv L (v : G)).subgroupOf J from
      ⟨hN hyR,(sup_le (Kv_le_Gv _) inf_le_right) y.property⟩)
end CFSG.Quasithin.Chapter12.Section06

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual simple component selects the full quasisimple B.5 conclusion. -/
theorem SourceHypothesis.small_thompson_canonical_quasisimple_classification
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
    generalizedFitting (ChapterB.InternalThompsonAction.ActionQuotient E) = B ∧
      centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient E)) = ⊥ ∧
      B ≤ offenderSubgroup ρ ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp (offenderSubgroup ρ).subtype) (B.subgroupOf (offenderSubgroup ρ))) := by
  let C := Kv (v : G)
  let S := Tv T (v : G)
  let J := C ⊔ S
  let A := C.subgroupOf J
  let P := S.subgroupOf J
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let B := A.map q
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hnA : J ≤ normalizer (C : Set G) :=
    hJG.trans ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnA
  let : B.Normal := (inferInstance : A.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨_,hker,_,_,hff⟩ := H.small_thompson_canonical_ff D v hv hTV hnot hs hi hJ he
  obtain ⟨e⟩ := H.nonsingular_canonical_component_image D v hv S inf_le_right hker
  obtain ⟨_,_,_,hq,hsi⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star C) := hq
  let : IsSimpleGroup (Star C) := hsi
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup B := e.isSimpleGroup
  have hP : IsPGroup 2 P :=
    (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
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


namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original A_6 section, centralizer and full Sylow survive the two-core projection. -/
theorem SourceHypothesis.small_thompson_local_embedding
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    let J := Kv (v : G) ⊔ Tv T (v : G)
    let A := starImage J (Lv L (v : G))
    let B := starImage J (Kv (v : G))
    let R := starImage J (Rv T L (v : G))
    A < B ∧ Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) ∧
      R ≤ coreQuotientCentralizer A ∧
      A ≤ normalizer (R : Set (Star J)) ∧
      normalizer (R : Set (Star J)) ≤ normalizer (A : Set (Star J)) ∧
      ∃ P : Sylow 2 (Star J), (P : Subgroup (Star J)) = starImage J (Tv T (v : G)) ∧
        (P : Subgroup (Star J)) ≤ normalizer (R : Set (Star J)) := by
  let C := Kv (v : G)
  let J := C ⊔ Tv T (v : G)
  let A₀ := (Lv L (v : G)).subgroupOf J
  let B₀ := C.subgroupOf J
  let R₀ := (Rv T L (v : G)).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hAC : Lv L (v : G) ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  have hAJ : Lv L (v : G) ≤ J := hAC.trans le_sup_left
  have hTJ : Tv T (v : G) ≤ J := le_sup_right
  have hTG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hAM : Lv L (v : G) ≤ M L := (Lv_le_L L _).trans L.le_normalizer
  have hRM : Rv T L (v : G) ≤ M L := (pCoreIn_le 2 _).trans
    (inf_le_left.trans (sup_le L.le_normalizer H.chosen.sylow_normalizes_component))
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨hS,hR,_,_,_⟩ := H.nonsingular_small_thompson D v hv hs hJ S hTS
  have hRT : Rv T L (v : G) ≤ Tv T (v : G) := by
    rw [←hR]
    exact (R_le_S L C _ (v : G)).trans hS.le
  have hRJ : Rv T L (v : G) ≤ J := hRT.trans hTJ
  have hcore := (H.small_thompson_core_lt_local_centralizer D v hv hs hJ he).1.le
  have hkerM : q.ker ≤ (M L).subgroupOf J := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hRM (hcore (mem_map_of_mem J.subtype hx))
  have hlt : A₀.map q < B₀.map q := by
    refine lt_of_le_of_ne (map_mono (comap_mono hAC)) ?_
    intro heq
    have hmap : B₀.map q ≤ ((M L).subgroupOf J).map q := by
      rw [←heq]
      exact map_mono (comap_mono hAM)
    have hBM := map_le_map_iff.mp hmap
    rw [sup_eq_left.mpr hkerM] at hBM
    apply he
    intro c hc
    exact hBM (show (⟨c,mem_sup_left hc⟩ : J) ∈ B₀ from hc)
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let a := subgroupOfEquivOfLe hAJ
  let ea : (A₀ ⧸ pCore 2 A₀) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eA
  have hkA : IsPGroup 2 (q.subgroupMap A₀).ker := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hnR : LT T L ⊓ Gv (v : G) ≤ normalizer (Rv T L (v : G) : Set G) :=
    (LT T L ⊓ Gv (v : G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hR' : R L C (Tv T (v : G)) (v : G) = Rv T L (v : G) := by
    simpa only [hS] using hR
  have hRC : R₀.map q ≤ coreQuotientCentralizer (A₀.map q) := by
    rintro _ ⟨r,hr,rfl⟩
    have hh : (r : G) ∈ R L C (Tv T (v : G)) (v : G) := hR'.symm ▸ hr
    obtain ⟨y,hy,hyEq⟩ := hh.2
    have heq : y = r := Subtype.ext hyEq
    change q y ∈ coreQuotientCentralizer (starImage J (Lv L (v : G))) at hy
    rw [show starImage J (Lv L (v : G)) = A₀.map q from rfl] at hy
    exact heq ▸ hy
  have hAnR : A₀ ≤ normalizer (R₀ : Set J) := by
    rw [←subgroupOf_normalizer_eq hRJ]
    exact comap_mono ((le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _)).trans hnR)
  have hTnR : (Tv T (v : G)).subgroupOf J ≤ normalizer (R₀ : Set J) := by
    rw [←subgroupOf_normalizer_eq hRJ]
    exact comap_mono ((inf_le_inf le_sup_right le_rfl).trans hnR)
  have hMnA : (Mv L (v : G)).subgroupOf J ≤ normalizer (A₀ : Set J) := by
    rw [←subgroupOf_normalizer_eq hAJ]
    exact comap_mono (Mv_le_normalizer_Lv L (v : G))
  have hnA := (H.small_thompson_local_image D v hv hs hJ he).2.2.2.trans
    ((map_mono hMnA).trans (A₀.le_normalizer_map q))
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 (Tv T (v : G)) (Gv (v : G)) from
    ⟨S,hS⟩).restrict hTJ hTG
  have hPe : (P : Subgroup J) = (Tv T (v : G)).subgroupOf J := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective J.subtype_injective _).symm
  refine ⟨hlt,⟨((q.subgroupMap A₀).pCoreQuotientEquiv
    (q.subgroupMap_surjective A₀) hkA).symm.trans ea⟩,hRC,
    (map_mono hAnR).trans (R₀.le_normalizer_map q),hnA,
    P.mapSurjective (QuotientGroup.mk'_surjective _),?_,?_⟩
  · change (P : Subgroup J).map q = _
    rw [hPe]
    rfl
  · change (P : Subgroup J).map q ≤ _
    rw [hPe]
    exact (map_mono hTnR).trans (R₀.le_normalizer_map q)
end CFSG.Quasithin.Chapter12.Section06


namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The image of L_v belongs to the local C-component family for the literal Sylow image. -/
theorem SourceHypothesis.small_thompson_local_component
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    let J := Kv (v : G) ⊔ Tv T (v : G)
    let A := starImage J (Lv L (v : G))
    ∃ P : Sylow 2 (Star J), (P : Subgroup (Star J)) = starImage J (Tv T (v : G)) ∧
      A ∈ ChapterA.Section03.localCComponents (P : Subgroup (Star J)) := by
  let J := Kv (v : G) ⊔ Tv T (v : G)
  let A₀ := (Lv L (v : G)).subgroupOf J
  let A := starImage J (Lv L (v : G))
  let q := QuotientGroup.mk' (pCore 2 J)
  obtain ⟨_,⟨eA⟩,_,_,hn,P,hP,hPR⟩ := H.small_thompson_local_embedding D v hv hs hJ he
  let N := A ⊔ (P : Subgroup (Star J))
  let B := A.subgroupOf N
  have hAN : N ≤ normalizer (A : Set (Star J)) := sup_le A.le_normalizer (hPR.trans hn)
  let : B.Normal := normal_subgroupOf_of_le_normalizer hAN
  have hAJ : Lv L (v : G) ≤ J :=
    (H.nonsingular_canonical_component D v hv).2.1.trans le_sup_left
  let a : A₀ ≃* Lv L (v : G) := subgroupOfEquivOfLe hAJ
  have hpA : IsPPerfect 2 A :=
    ((isPPerfect_embedded_pResidual 2 (CLv L (v : G))).of_surjective
      a.symm.toMonoidHom a.symm.surjective).of_surjective
        (q.subgroupMap A₀) (q.subgroupMap_surjective A₀)
  let b : B ≃* A := subgroupOfEquivOfLe (show A ≤ N from le_sup_left)
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eA
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eB.symm
  exact ⟨P,hP,isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : B.Normal).isSubnormal
    (hpA.of_surjective b.symm.toMonoidHom b.symm.surjective)⟩
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Apply the local embedding and canonical classifier at the original preferred escaping point. -/
theorem SourceHypothesis.exists_preferred_small_thompson_local_analysis_of_fixed
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
        let A := starImage J (Lv L (w : G))
        let R := starImage J (Rv T L (w : G))
        let E := reducedTwoSubgroup J
        letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
        let q := ChapterB.InternalThompsonAction.actionMk E
        let ρ := ChapterB.InternalThompsonAction.action E
        let B := ((Kv (w : G)).subgroupOf J).map q
        J.pCoreIn 2 < Rv T L (w : G) ∧
          R ≠ ⊥ ∧ IsPGroup 2 R ∧
          normalizer (R : Set (Star J)) ≤ starImage J (Mv L (w : G)) ∧
          A < starImage J (Kv (w : G)) ∧
          Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) ∧
          R ≤ coreQuotientCentralizer A ∧
          A ≤ normalizer (R : Set (Star J)) ∧
          normalizer (R : Set (Star J)) ≤ normalizer (A : Set (Star J)) ∧
          (∃ P : Sylow 2 (Star J), (P : Subgroup (Star J)) = starImage J (Tv T (w : G)) ∧
            A ∈ ChapterA.Section03.localCComponents (P : Subgroup (Star J))) ∧
          generalizedFitting (ChapterB.InternalThompsonAction.ActionQuotient E) = B ∧
          centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient E)) = ⊥ ∧
          B ≤ offenderSubgroup ρ ∧
          Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp (offenderSubgroup ρ).subtype) (B.subgroupOf (offenderSubgroup ρ)))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,_,_,hsimple,hline,hfixed,_⟩ :=
    SourceHypothesis.exists_preferred_nonsingular_nontrivial_fixed_not_quasisimple.{_,0}
      H D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hfixed hz,hsimple,?_⟩
  intro hJ
  obtain ⟨hc,_⟩ := H.small_thompson_core_lt_local_centralizer D w hw hs hJ hnot
  obtain ⟨_,hr,hp,hn⟩ := H.small_thompson_local_image D w hw hs hJ hnot
  obtain ⟨hlt,ha,hRC,hAR,hRA,_⟩ := H.small_thompson_local_embedding D w hw hs hJ hnot
  exact ⟨hc,hr,hp,hn,hlt,ha,hRC,hAR,hRA,
    H.small_thompson_local_component D w hw hs hJ hnot,
    H.small_thompson_canonical_quasisimple_classification D w hw hTV (hfixed hz) hs hi hJ hnot⟩
end CFSG.Quasithin.Chapter12.Section06
