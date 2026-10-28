module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerCanonical

/-!
# The original local section in the contrary normalizer branch

Under N_G(R_v) <= M, the canonical two-core is strictly smaller than R_v:
equality would make K_v normalize R_v and put K_v in M. The literal image
R_v* is therefore nontrivial, and its quotient normalizer lies in M_v*.
The original A_6 section lies properly in K_v*, normalizes R_v*, and is
normalized by its normalizer. The image of T_v lies in that normalizer and
has index at most four in the image of the selected Sylow S.

The A_7 socle centralizer theorem excludes K_v* isomorphic to A_7 in this
branch. At the actual preferred point with nontrivial original C_V(L),
nonquasisimplicity is discharged and these conclusions are assembled with
the canonical FF action and its full B.5.1 marking. All quotient maps,
conjugation actions, V and C_V(L) are the original ones.

The remaining model comparison and its S_8 contradiction are still needed
for 12.6.17. The HS/J4 exclusions, general canonical-module arguments,
blocks, splitting and fixed-space elimination remain separate obligations;
neither 12.6.2 nor 12.6.23 follows from this conditional branch.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 12.6.17, printed p.827, and B.5.1, printed pp.99--103.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the contrary branch of 12.6.17, the literal R_v image is nontrivial
and its full quotient normalizer lies in the original M_v image. -/
theorem SourceHypothesis.nonsingular_normalizer_local_image
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let J := Kv (v : G) ⊔ S₀
    let R := (Rv T L (v : G)).subgroupOf J
    let q := QuotientGroup.mk' (pCore 2 J)
    (R.map q).comap q = R ∧ R.map q ≠ ⊥ ∧ IsPGroup 2 (R.map q) ∧
      normalizer (R.map q : Set (Star J)) ≤
        ((Mv L (v : G)).subgroupOf J).map q := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let R := (Rv T L (v : G)).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hR := H.nonsingular_R_eq_Rv_of_normalizer D v hv hs hNM S hTS
  have hc := core_le_R_of_sylow L (Kv (v : G)) (v : G) S (Kv_le_Gv _)
  rw [hR] at hc
  have hcore : J.pCoreIn 2 < Rv T L (v : G) := by
    refine lt_of_le_of_ne hc ?_
    intro heq
    apply he
    have hn : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
      J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
    exact le_sup_left.trans ((heq ▸ hn).trans hNM)
  have hRJ : Rv T L (v : G) ≤ J := by
    rw [←hR]
    exact inf_le_left.trans le_sup_right
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
      ⟨hNM hyR,(sup_le (Kv_le_Gv _) (map_subtype_le _)) y.property⟩)
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original local A₆ section and T_v retain the index-four Sylow bound
in the quotient used by the contrary normalizer branch of 12.6.17. -/
theorem SourceHypothesis.nonsingular_normalizer_local_embedding
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let J := Kv (v : G) ⊔ S₀
    let A := starImage J (Lv L (v : G))
    let B := starImage J (Kv (v : G))
    let R := starImage J (Rv T L (v : G))
    let P₀ := starImage J (Tv T (v : G))
    A < B ∧ Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) ∧
      R ≤ coreQuotientCentralizer A ∧
      A ≤ normalizer (R : Set (Star J)) ∧
      normalizer (R : Set (Star J)) ≤ normalizer (A : Set (Star J)) ∧
      P₀ ≤ normalizer (R : Set (Star J)) ∧
      ∃ P : Sylow 2 (Star J), (P : Subgroup (Star J)) = starImage J S₀ ∧
        P₀ ≤ (P : Subgroup (Star J)) ∧ P₀.relIndex (P : Subgroup (Star J)) ≤ 4 := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let C := Kv (v : G)
  let J := C ⊔ S₀
  let A₀ := (Lv L (v : G)).subgroupOf J
  let B₀ := C.subgroupOf J
  let R₀ := (Rv T L (v : G)).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hAC : Lv L (v : G) ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  have hAJ : Lv L (v : G) ≤ J := hAC.trans le_sup_left
  have hTJ : Tv T (v : G) ≤ J := hTS.trans le_sup_right
  have hTG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) (map_subtype_le _)
  have hAM : Lv L (v : G) ≤ M L := (Lv_le_L L _).trans L.le_normalizer
  have hRM : Rv T L (v : G) ≤ M L := (pCoreIn_le 2 _).trans
    (inf_le_left.trans (sup_le L.le_normalizer H.chosen.sylow_normalizes_component))
  have hR := H.nonsingular_R_eq_Rv_of_normalizer D v hv hs hNM S hTS
  obtain ⟨P₀,hP₀⟩ := hs.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (v : G) ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  have hRT : Rv T L (v : G) ≤ Tv T (v : G) := (pCoreIn_le_sylow _ P₀).trans hP₀.le
  have hRJ : Rv T L (v : G) ≤ J := hRT.trans hTJ
  have hcore := core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _)
  rw [hR] at hcore
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
  have hRC : R₀.map q ≤ coreQuotientCentralizer (A₀.map q) := by
    rintro _ ⟨r,hr,rfl⟩
    have hh : (r : G) ∈ R L C S₀ (v : G) := hR.symm ▸ hr
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
  have hnA := (H.nonsingular_normalizer_local_image D v hv hs he hNM S hTS).2.2.2.trans
    ((map_mono hMnA).trans (A₀.le_normalizer_map q))
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) from
    ⟨S,rfl⟩).restrict (show S₀ ≤ J from le_sup_right) hTG
  have hPe : (P : Subgroup J) = S₀.subgroupOf J := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective J.subtype_injective _).symm
  have hkT : q.ker ≤ (Tv T (v : G)).subgroupOf J := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hRT (hcore (mem_map_of_mem J.subtype hx))
  have hkS : q.ker ≤ S₀.subgroupOf J := hkT.trans (comap_mono hTS)
  refine ⟨hlt,⟨((q.subgroupMap A₀).pCoreQuotientEquiv
    (q.subgroupMap_surjective A₀) hkA).symm.trans ea⟩,hRC,
    (map_mono hAnR).trans (R₀.le_normalizer_map q),hnA,
    (map_mono hTnR).trans (R₀.le_normalizer_map q),
    P.mapSurjective (QuotientGroup.mk'_surjective _),?_,?_,?_⟩
  · change (P : Subgroup J).map q = _
    rw [hPe]
    rfl
  · change ((Tv T (v : G)).subgroupOf J).map q ≤ (P : Subgroup J).map q
    rw [hPe]
    exact map_mono (comap_mono hTS)
  · change (((Tv T (v : G)).subgroupOf J).map q).relIndex ((P : Subgroup J).map q) ≤ 4
    rw [hPe,relIndex_map_map,sup_eq_left.mpr hkT,sup_eq_left.mpr hkS,
      relIndex_subgroupOf (show S₀ ≤ J from le_sup_right)]
    simpa only [hi] using Tv_relIndex_le T (v : G) S₀ (S.isPGroup'.map _) hTS
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The contrary normalizer branch excludes A₇ through its actual socle
centralizer, before the remaining FF-model comparison. -/
theorem SourceHypothesis.nonsingular_normalizer_not_seven
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let C := Kv (v : G)
  let J := C ⊔ S₀
  let C₀ := C.subgroupOf J
  let P₀ := S₀.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := starImage J C
  let A := starImage J (Lv L (v : G))
  let R₀ := starImage J (Rv T L (v : G))
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
  obtain ⟨hlt,⟨eA⟩,hRA,_⟩ := H.nonsingular_normalizer_local_embedding D v hv hs hi he hNM S hTS
  obtain ⟨_,hR,hRp,_⟩ := H.nonsingular_normalizer_local_image D v hv hs he hNM S hTS
  apply hR
  apply seven_socle_two_section_centralizer B A R₀ hF eB hlt.le eA hRp
  apply commutator_le.mpr
  intro r hr a ha
  exact ((mem_coreQuotientCentralizer_iff A r).mp (hRA hr)).2 a ha
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At the preferred escaping point with nontrivial original fixed space,
the contrary branch of 12.6.17 has its actual FF action, B.5.1 marking,
and nontrivial local quotient image. Nonquasisimplicity is discharged. -/
theorem SourceHypothesis.exists_preferred_nonsingular_normalizer_analysis_of_fixed
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
      ¬ IsQuasisimple (Kv (w : G)) ∧
      (normalizer (Rv T L (w : G) : Set G) ≤ M L →
        (¬ Nonempty (Star (Kv (w : G)) ≃* alternatingGroup (Fin 7))) ∧
        ∃ S : Sylow 2 (Gv (w : G)),
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          let J := Kv (w : G) ⊔ S₀
          let E := reducedTwoSubgroup J
          letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
          let q := ChapterB.InternalThompsonAction.actionMk E
          let ρ := ChapterB.InternalThompsonAction.action E
          let B := ((Kv (w : G)).subgroupOf J).map q
          let R₀ := ((Rv T L (w : G)).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
          Tv T (w : G) ≤ S₀ ∧
          Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (w : G) : Set G))
            (Gv (w : G) ⊓ normalizer (Lv L (w : G) : Set G)) ∧
          R L (Kv (w : G)) S₀ (w : G) = Rv T L (w : G) ∧
          generalizedFitting J = pCore 2 J ∧
          centralizer (E : Set J) = pCore 2 J ∧
          U (Kv (w : G)) S₀ = E.map J.subtype ∧
          Vv L V (w : G) ≤ ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ ∧
          U (Kv (w : G)) S₀ ≤ Rv T L (w : G) ∧
          IsFFModule ρ ∧ R₀ ≠ ⊥ ∧
          normalizer (R₀ : Set (Star J)) ≤
            ((Mv L (w : G)).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ∧
          (let A := starImage J (Lv L (w : G))
           let C := starImage J (Kv (w : G))
           let P₀ := starImage J (Tv T (w : G))
           A < C ∧ Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) ∧
             R₀ ≤ coreQuotientCentralizer A ∧
             A ≤ normalizer (R₀ : Set (Star J)) ∧
             normalizer (R₀ : Set (Star J)) ≤ normalizer (A : Set (Star J)) ∧
             P₀ ≤ normalizer (R₀ : Set (Star J)) ∧
             ∃ P : Sylow 2 (Star J), (P : Subgroup (Star J)) = starImage J S₀ ∧
               P₀ ≤ (P : Subgroup (Star J)) ∧ P₀.relIndex (P : Subgroup (Star J)) ≤ 4) ∧
          generalizedFitting (ChapterB.InternalThompsonAction.ActionQuotient E) = B ∧
          centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient E)) = ⊥ ∧
          B ≤ offenderSubgroup ρ ∧
          Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp (offenderSubgroup ρ).subtype) (B.subgroupOf (offenderSubgroup ρ)))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,_⟩ :=
    H.exists_preferred_nonsingular_large_thompson_of_fixed D hTV hTI hz v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,fun hNM => ?_⟩
  refine ⟨H.nonsingular_normalizer_not_seven D w hw hs hi hnot hNM,?_⟩
  obtain ⟨S,hTS,hN,hR,hF,hker,hred,hm,hUR,hff⟩ :=
    H.nonsingular_normalizer_canonical_ff D w hw hTV hnq hs hi hnot hNM
  obtain ⟨_,hRne,_,hRN⟩ := H.nonsingular_normalizer_local_image D w hw hs hnot hNM S hTS
  exact ⟨S,hTS,hN,hR,hF,hker,hred,hm,hUR,hff,hRne,hRN,
    H.nonsingular_normalizer_local_embedding D w hw hs hi hnot hNM S hTS,
    H.nonsingular_canonical_quasisimple_of_ff D w hw _ (map_subtype_le _)
      (S.isPGroup'.map _) hker hff⟩
end CFSG.Quasithin.Chapter12.Section06
