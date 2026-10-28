module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerRankTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.SmallNormalizerFive
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Excluding SL₅(2) in the original contrary normalizer branch

Work with the actual quotient K_vS/O₂(K_vS). Its K_v image is simple,
normal, and self-centralizing. The original L_v and R_v images preserve
the A₆ section, nontrivial two-subgroup, and mutual normalizer containments.
Intersecting the quotient Sylow with the K_v image retains the original
index-at-most-four bound. The binary-five normalizer theorem excludes
SL₅(2), leaving an actual isomorphism K_v/O₂(K_v) ≃ SL₄(2).

The preferred-point application discharges nonquasisimplicity when the
original C_V(L) is nontrivial, and retains the original point, module,
fixed line, Sylow and R=R_v. The SL₄(2) extension and module comparison
still remain for 12.6.17. The HS/J₄ exclusions, general canonical-module
arguments, blocks, splitting and fixed-space elimination also remain;
neither 12.6.2 nor 12.6.23 is asserted. Earlier invariance/TI retain producer
qt-d-1222-source; final discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith 12.6.17, printed p.827, combined manuscript
of 1 March 2004.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem SourceHypothesis.nonsingular_normalizer_not_binary_five
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2)) := by
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
  let eB := c.trans (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5))
  obtain ⟨_,_,_,hq,hsi⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star C) := hq
  let : IsSimpleGroup (Star C) := hsi
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv c.symm
  let : IsSimpleGroup B := c.isSimpleGroup
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
  have hcent : centralizer (B : Set (Star J)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient B (Group.IsPerfect.not_isMulCommutative B)
      hquot (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨hlt,⟨eA⟩,_,hAR,hNR,hPN,P,hPe,hPP,hPi⟩ :=
    H.nonsingular_normalizer_local_embedding D v hv hs hi he hNM S hTS
  obtain ⟨_,hR,hRp,_⟩ := H.nonsingular_normalizer_local_image D v hv hs he hNM S hTS
  obtain ⟨eL⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let : Group.IsPerfect (Lv L (v : G)) := Lv_isPerfect_of_A6 L (v : G) eL
  let d := subgroupOfEquivOfLe ((H.nonsingular_canonical_component D v hv).2.1.trans
    (show C ≤ J from le_sup_left))
  let : Group.IsPerfect ((Lv L (v : G)).subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  let : Group.IsPerfect A := Group.IsPerfect.map q
  obtain ⟨P₁,hP₁⟩ := P.exists_subgroupOf_eq_of_normal B
  apply ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear.no_six_small_normalizer_five_socle
    B A R₀ eB hcent hlt.le eA hRp hR hAR hNR P₁
  rw [←subgroupOf_normalizer_eq hlt.le,hP₁]
  change ((normalizer (A : Set (Star J))).comap B.subtype).relIndex
    ((P : Subgroup (Star J)).subgroupOf B) ≤ 4
  rw [relIndex_comap,subgroupOf_map_subtype]
  exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans
    ((relIndex_le_of_le_left (hPN.trans hNR) index_ne_zero_of_finite).trans hPi)

theorem SourceHypothesis.nonsingular_normalizer_binary_four
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) :=
  (H.nonsingular_normalizer_binary_models D v hv hTV hnot hs hi he hNM).resolve_right
    (H.nonsingular_normalizer_not_binary_five D v hv hs hi he hNM)
end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem SourceHypothesis.exists_preferred_nonsingular_normalizer_binary_four_of_fixed
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
        ∃ S : Sylow 2 (Gv (w : G)),
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          let J := Kv (w : G) ⊔ S₀
          let R₀ := starImage J (Rv T L (w : G))
          Tv T (w : G) ≤ S₀ ∧
          Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (w : G) : Set G))
            (Gv (w : G) ⊓ normalizer (Lv L (w : G) : Set G)) ∧
          (Tv T (w : G)).relIndex S₀ ≤ 4 ∧
          R L (Kv (w : G)) S₀ (w : G) = Rv T L (w : G) ∧ R₀ ≠ ⊥ ∧
          Nonempty (Star (Kv (w : G)) ≃* SL(4,ZMod 2))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hmodel⟩ :=
    H.exists_preferred_nonsingular_normalizer_models_of_fixed D hTV hTI hz v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,fun hNM => ?_⟩
  obtain ⟨S,hTS,hN,hSi,hR,hRne,hmod⟩ := hmodel hNM
  exact ⟨S,hTS,hN,hSi,hR,hRne,hmod.resolve_right
    (H.nonsingular_normalizer_not_binary_five D w hw hs hi hnot hNM)⟩
end CFSG.Quasithin.Chapter12.Section06
