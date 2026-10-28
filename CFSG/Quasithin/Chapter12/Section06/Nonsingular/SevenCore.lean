module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalFF
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.CoreSplit

/-!
# The original A7 two-core and Sylow subgroup

The A6 section in the A7 socle has no nontrivial two-group section
centralizer. Applied through the literal star projection, this proves
R = O2(K_v S). Preferred-point control puts the whole core in T_v,
so the original intersection identity gives R = R_v. The S8 quotient
of LT gives |T_v:R_v|=16, while the A7 socle embeds the canonical quotient
in S7. Its Sylow bound therefore gives S=T_v without assuming equality.

The proved A7 cohomology theorem splits this same two-core over its
intrinsic natural moved module and the actual Sylow centralizer of K_v.
Finally LT=LR_v and source uniqueness kill the common centralizer
C_T(L) intersect C_(T_v)(K_v). PreferredSevenCore constructs every premise
at the unchanged preferred point with nontrivial original C_V(L).

Source: Aschbacher--Smith, proof of Theorem12.6.2 after12.6.18,
printed p.828, using C.1.13 and I.1.6, combined manuscript of1 March2004.
The original Q extension, remaining HS/J4 exclusions, general12.6.13(3)
and fixed-space elimination remain; neither12.6.2 nor12.6.23 is asserted.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem SourceHypothesis.nonsingular_seven_socle
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (e : Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let J := Kv (v : G) ⊔ S₀
    let B := starImage J (Kv (v : G))
    B = generalizedFitting (Star J) ∧ Nonempty (B ≃* alternatingGroup (Fin 7)) := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let C := Kv (v : G)
  let J := C ⊔ S₀
  let C₀ := C.subgroupOf J
  let P₀ := S₀.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := starImage J C
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) (map_subtype_le _)
  have hnC : J ≤ normalizer (C : Set G) :=
    hJG.trans ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer hnC
  let : B.Normal := (inferInstance : C₀.Normal).map q (QuotientGroup.mk'_surjective _)
  have hc : C₀.IsCComponent :=
    (H.nonsingular_canonical_component D v hv).1.subgroupOf_of_le le_sup_left hJG
  let b : C₀ ≃* C := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let c : B ≃* Star C := (cComponentTwoCoreQuotientEquiv hc).symm.trans
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b))
  let eB : B ≃* alternatingGroup (Fin 7) := c.trans e
  let : IsQuasisimple (Star C) := (H.nonsingular_canonical_component D v hv).2.2.2.1
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv c.symm
  have hp : IsPGroup 2 P₀ := (S.isPGroup'.map _).comap_subtype
  have hgen : C₀ ⊔ P₀ = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show S₀ ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (Star J ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (P₀.map q) (hp.map q) (by
      change C₀.map q ⊔ P₀.map q = ⊤
      rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)])
  have hF : B = generalizedFitting (Star J) :=
    (generalizedFitting_eq_of_quasisimple_two_quotient B hquot (pCore_quotient_pCore_eq_bot 2)).symm
  exact ⟨hF,⟨eB⟩⟩

/-- The canonical section centralizer R is exactly the two-core in the A7 case. -/
theorem SourceHypothesis.nonsingular_seven_R_eq_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (e : Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    R L (Kv (v : G)) S₀ (v : G) = (Kv (v : G) ⊔ S₀).pCoreIn 2 := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let C := Kv (v : G)
  let J := C ⊔ S₀
  let C₀ := C.subgroupOf J
  let P₀ := S₀.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := starImage J C
  let A₀ := (Lv L (v : G)).subgroupOf J
  let A := starImage J (Lv L (v : G))
  let R₀ := R L C S₀ (v : G)
  let R₁ := starImage J R₀
  obtain ⟨hF,⟨eB⟩⟩ := H.nonsingular_seven_socle D v hv S e
  have hAC := (H.nonsingular_canonical_component D v hv).2.1
  have hAJ : Lv L (v : G) ≤ J := hAC.trans le_sup_left
  obtain ⟨ea⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let a : A₀ ≃* Lv L (v : G) := subgroupOfEquivOfLe hAJ
  have hkA : IsPGroup 2 (q.subgroupMap A₀).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6) :=
    ((q.subgroupMap A₀).pCoreQuotientEquiv (q.subgroupMap_surjective A₀) hkA).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans ea)
  have hRp : IsPGroup 2 R₁ :=
    ((S.isPGroup'.map _).to_le (R_le_S L C S₀ _)).comap_subtype.map q
  have hRA : R₁ ≤ coreQuotientCentralizer A := by
    rintro x ⟨r,hr,rfl⟩
    obtain ⟨y,hy,he⟩ := hr.2
    have he' : y = r := Subtype.ext he
    subst y
    exact hy
  have hz : R₁ = ⊥ := seven_socle_two_section_centralizer B A R₁ hF eB
    (map_mono (comap_mono hAC)) eA hRp (by
      apply commutator_le.mpr
      intro r hr a ha
      exact ((mem_coreQuotientCentralizer_iff A r).mp (hRA hr)).2 a ha)
  apply le_antisymm
  · have hh := (map_eq_bot_iff (R₀.subgroupOf J)).mp hz
    rw [QuotientGroup.ker_mk'] at hh
    intro r hr
    have hrJ : r ∈ J := (show S₀ ≤ J from le_sup_right) (R_le_S L C S₀ _ hr)
    exact mem_map_of_mem J.subtype (hh (show (⟨r,hrJ⟩ : J) ∈ R₀.subgroupOf J from hr))
  · exact core_le_R_of_sylow L C _ S (Kv_le_Gv _)

/-- Preferred-point centralizer control places the whole canonical two-core in T_v. -/
theorem SourceHypothesis.nonsingular_core_le_Tv_of_moved_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hctrl : Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔
        (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
          (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hlocal : ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype),Lv L (v : G)⁆ = Vv L V (v : G)) :
    (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype).pCoreIn 2 ≤
      Tv T (v : G) := by
  let C := Kv (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ S₀
  let E := reducedTwoSubgroup J
  have hJE : J ≤ normalizer (E.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      E.le_normalizer_map J.subtype
  have hWU : Vv L V (v : G) ≤ U C S₀ := by
    rw [←hlocal,hred]
    exact le_normalizer_iff_commutator_le_left.mp
      ((H.nonsingular_canonical_component D v hv).2.1.trans (le_sup_left.trans hJE))
  have hQC : J.pCoreIn 2 ≤ centralizer (Vv L V (v : G) : Set G) := by
    intro r hr w hw
    have hwu := hWU hw
    rw [U_eq_omegaCenter] at hwu
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hwu).2.2 r hr).symm
  have hQS : J.pCoreIn 2 ≤ S₀ :=
    (core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _)).trans (R_le_S L C S₀ _)
  have hQM : J.pCoreIn 2 ≤ Mv L (v : G) :=
    le_inf ((le_inf (hQS.trans (map_subtype_le _)) hQC).trans hctrl)
      (hQS.trans (map_subtype_le _))
  have hEq : S₀ ⊓ Mv L (v : G) = Tv T (v : G) :=
    (Chapter1.isSylowIn_iff.mp hs).2.2 _
      ((S.isPGroup'.map _).to_le inf_le_left)
      (le_inf hTS (Chapter1.isSylowIn_iff.mp hs).2.1) inf_le_right
  exact (le_inf hQS hQM).trans_eq hEq

/-- Identify the original R_v with the canonical two-core, retaining the original Sylow placement. -/
theorem SourceHypothesis.nonsingular_seven_original_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (e : Star (Kv (v : G)) ≃* alternatingGroup (Fin 7))
    (hcore : (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).pCoreIn 2 ≤ Tv T (v : G)) :
    Rv T L (v : G) = (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).pCoreIn 2 := by
  obtain ⟨P,hP⟩ := hs.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  obtain ⟨a⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hh := R_inf_Tv_eq_Rv T L (Kv (v : G)) _ (v : G)
    H.chosen.sylow_normalizes_component (H.nonsingular_canonical_component D v hv).2.1
    hTS P hP (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) a)
  rw [H.nonsingular_seven_R_eq_core D v hv S e,inf_eq_left.mpr hcore] at hh
  exact hh.symm



omit [Finite G] in
private theorem centralizer_le_R (L K S : Subgroup G) (v : G) (hLK : Lv L v ≤ K) :
    S ⊓ centralizer (K : Set G) ≤ R L K S v := by
  let J := K ⊔ S
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := starImage J (Lv L v)
  rintro r ⟨hr,hc⟩
  have hrJ : r ∈ J := (show S ≤ J from le_sup_right) hr
  let r₀ : J := ⟨r,hrJ⟩
  have hz : q r₀ ∈ centralizer (A : Set (Star J)) := by
    rintro a ⟨x,hx,rfl⟩
    exact (map_mul q x r₀).symm.trans
      ((congrArg q (Subtype.ext (hc x (hLK hx)))).trans (map_mul q r₀ x))
  refine ⟨hr,r₀,(mem_coreQuotientCentralizer_iff A (q r₀)).mpr
    ⟨Subgroup.centralizer_le_normalizer _ hz,?_⟩,rfl⟩
  intro a ha
  have he : ⁅q r₀,a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hz a ha).symm
  rw [he]
  exact one_mem _

/-- The core and the selected Sylow have the same centralizer of K_v. -/
theorem SourceHypothesis.nonsingular_seven_core_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (e : Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    (Kv (v : G) ⊔ S₀).pCoreIn 2 ⊓ centralizer (Kv (v : G) : Set G) =
      S₀ ⊓ centralizer (Kv (v : G) : Set G) := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hR := H.nonsingular_seven_R_eq_core D v hv S e
  dsimp only at hR ⊢
  rw [←hR]
  exact le_antisymm (inf_le_inf (R_le_S L (Kv (v : G)) S₀ _) le_rfl)
    (le_inf (centralizer_le_R L (Kv (v : G)) S₀ (v : G)
      (H.nonsingular_canonical_component D v hv).2.1) inf_le_right)


/-- The original canonical core is the internal direct product of its moved layer and its block centralizer. -/
theorem nonsingular_seven_core_split
    (v : G) (S : Subgroup G) (hS : S ≤ Gv v)
    (hblock : ChapterC.IsAlternatingBlock (Kv v) 7)
    (hlayer : ⁅U (Kv v) S,Kv v⁆ = (ChapterC.blockU (Kv v)).map (Kv v).subtype)
    (hfixed : (⁅U (Kv v) S,Kv v⁆ : Subgroup G) ⊓ centralizer (Kv v : Set G) = ⊥) :
    (Kv v ⊔ S).pCoreIn 2 = ⁅U (Kv v) S,Kv v⁆ ⊔
      ((Kv v ⊔ S).pCoreIn 2 ⊓ centralizer (Kv v : Set G)) ∧
    Disjoint (⁅U (Kv v) S,Kv v⁆ : Subgroup G)
      ((Kv v ⊔ S).pCoreIn 2 ⊓ centralizer (Kv v : Set G)) ∧
    ⁅(⁅U (Kv v) S,Kv v⁆ : Subgroup G),
      (Kv v ⊔ S).pCoreIn 2 ⊓ centralizer (Kv v : Set G)⁆ = ⊥ := by
  have hn : Kv v ⊔ S ≤ normalizer (Kv v : Set G) :=
    (sup_le (Kv_le_Gv v) hS).trans
      ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv v)).mp (Kv_normalIn_Gv v))
  have hm : (⁅U (Kv v) S,Kv v⁆ : Subgroup G) ≤ Kv v := by
    rw [hlayer]
    exact map_subtype_le _
  refine ⟨?_,(disjoint_iff.mpr hfixed).mono_right inf_le_right,?_⟩
  · rw [hlayer]
    exact hblock.seven_normalizer_twoCore_eq_module_sup_centralizer le_sup_left hn
  · rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_right.trans (centralizer_le hm))


/-- The original S8 quotient gives the exact index |T_v:R_v|=16. -/
theorem SourceHypothesis.nonsingular_original_Tv_core_index
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hlt : Q T L < Rv T L (v : G)) :
    (Rv T L (v : G)).relIndex (Tv T (v : G)) = 16 := by
  obtain ⟨e,_⟩ := H.nonsingular_original_symmetric_quotient D v hv hlt
  let J := LT T L
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : (Q T L).subgroupOf J = f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hqt : (Q T L).relIndex (T : Subgroup G) = 128 := by
    rw [←relIndex_subgroupOf (show (T : Subgroup G) ≤ J from le_sup_right),hk,relIndex_ker]
    change Nat.card (P.mapSurjective hf) = 128
    rw [Sylow.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  obtain ⟨P₀,hP₀⟩ := hs.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  have hRT : Rv T L (v : G) ≤ Tv T (v : G) := (pCoreIn_le_sylow _ P₀).trans hP₀.le
  have hprod := relIndex_mul_relIndex (Q T L) (Rv T L (v : G)) (Tv T (v : G)) hlt.le hRT
  rw [H.nonsingular_original_core_index D v hv hlt] at hprod
  have hprod' := relIndex_mul_relIndex (Q T L) (Tv T (v : G)) (T : Subgroup G)
    (Q_le_Tv H.chosen v) inf_le_left
  rw [hi,hqt] at hprod'
  omega


/-- The same selected Sylow is T_v: the literal core quotient reaches the S7 two-part bound. -/
theorem SourceHypothesis.nonsingular_seven_sylow_eq_Tv
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hlt : Q T L < Rv T L (v : G))
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (e : Star (Kv (v : G)) ≃* alternatingGroup (Fin 7))
    (hcore : Rv T L (v : G) = (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).pCoreIn 2) :
    (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype = Tv T (v : G) := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let B := starImage J (Kv (v : G))
  let P₀ := S₀.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  obtain ⟨hF,⟨eB⟩⟩ := H.nonsingular_seven_socle D v hv S e
  obtain ⟨f,hf,_⟩ := alternatingGroup.SevenSolvableGeneration.exists_socle_embedding B hF eB
  let g := f.comp q
  have hk : g.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ hf,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 (P₀.map g) := ((S.isPGroup'.map _).comap_subtype).map g
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hcard : Nat.card (P₀.map g) ≤ 16 := by
    apply (card_le_of_le hP).trans_eq
    rw [Sylow.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hRS : (Rv T L (v : G)).relIndex S₀ ≤ 16 := by
    rw [hcore,←relIndex_subgroupOf (show S₀ ≤ J from le_sup_right)]
    have hh : (J.pCoreIn 2).subgroupOf J = pCore 2 J :=
      comap_map_eq_self_of_injective J.subtype_injective _
    rw [hh,←hk,relIndex_ker]
    exact hcard
  have hRT : Rv T L (v : G) ≤ Tv T (v : G) := by
    obtain ⟨P,hP⟩ := hs.restrict
      (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
      (inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
    exact (pCoreIn_le_sylow _ P).trans hP.le
  have hm := relIndex_mul_relIndex (Rv T L (v : G)) (Tv T (v : G)) S₀ hRT hTS
  rw [H.nonsingular_original_Tv_core_index D v hv hs hi hlt] at hm
  have hn : (Tv T (v : G)).relIndex S₀ ≠ 0 := index_ne_zero_of_finite
  have he : (Tv T (v : G)).relIndex S₀ = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp he) hTS



omit [IsElementaryAbelian 2 V] in
/-- The source join and uniqueness kill C_T(L) intersect C_G(K_v), without a separate normality premise. -/
theorem SourceHypothesis.nonsingular_common_centralizer_eq_bot_of_join
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (he : ¬ Kv (v : G) ≤ M L)
    (hjoin : L ⊔ Rv T L (v : G) = LT T L) :
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      centralizer (Kv (v : G) : Set G) = ⊥ := by
  have hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) =
      Q T L ⊓ centralizer (L : Set G) := by
    apply le_antisymm
    · exact le_inf
        ((inf_le_inf (show (T : Subgroup G) ≤ LT T L from le_sup_right)
          (centralizer_le H.chosen.le_component)).trans_eq (H.join_centralizer_eq_core hTV))
        inf_le_right
    · exact inf_le_inf ((Q_le_Tv H.chosen v).trans inf_le_left) le_rfl
  rw [hCT]
  let A := Q T L ⊓ centralizer (L : Set G)
  let B := A ⊓ centralizer (Kv (v : G) : Set G)
  have hAN : LT T L ≤ normalizer (A : Set G) :=
    (le_inf ((LT T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (LT T L))))
      ((sup_le L.le_normalizer H.chosen.sylow_normalizes_component).trans
        (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  have hLN : L ≤ normalizer (B : Set G) :=
    (le_centralizer_iff.mp (show B ≤ centralizer (L : Set G) from
      inf_le_left.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hRG : Rv T L (v : G) ≤ Gv (v : G) := (pCoreIn_le 2 _).trans inf_le_right
  have hRN : Rv T L (v : G) ≤ normalizer (B : Set G) :=
    (le_inf (((pCoreIn_le 2 _).trans inf_le_left).trans hAN)
      ((hRG.trans ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp
        (Kv_normalIn_Gv _))).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hBN : LT T L ≤ normalizer (B : Set G) := hjoin ▸ sup_le hLN hRN
  by_contra hne
  have hNM := H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
    (show B ≤ LT T L from inf_le_left.trans (inf_le_left.trans (pCoreIn_le 2 _))) hne hBN
  exact he ((le_centralizer_iff.mp (show B ≤ centralizer (Kv (v : G) : Set G) from
    inf_le_right)).trans ((Subgroup.centralizer_le_normalizer _).trans hNM))


end CFSG.Quasithin.Chapter12.Section06
