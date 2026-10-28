module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsSylow
public import Theory.GroupTheory.IndexTwoConjugateJoin
public import Theory.ElementaryAbelian.Join
/-!
# Noncentral commutators of the original HS conjugate pair

Retain the Sylow S from the nonsingular source construction, its original
index-two subgroup T_v, and an element s in S intersect K_v outside T_v.
The two conjugates of V_v are normal in T_v and their join is normalized
by S. If their commutator vanished in the literal HS central quotient,
their images would generate an elementary group of order at least sixteen
normalized by a full HS Sylow. The native bound of eight excludes this.
Thus the commutator survives the entire covering center.

The same s gives two mutually normalizing copies of the original V, still
inside T_v and both containing the original nonsingular point. Their
commutator is central in their join, but also escapes the covering center.
The preferred-point application retains the original R-centralizer
identity, its literal image, both normalizer intersections, the covering
catalogue and all preceding point data. It does not infer normalization
of V or V_v by S. The remaining coupled HS contradiction and J4 exclusion,
followed by the outstanding source discharge, remain necessary for the
full nonsingular-centralizer and fixed-space theorems.

Source: Aschbacher--Smith, 12.6.4--5 and the proof of 12.6.12,
printed pp.824--826; GLS3 Table 5.3m for the HS Sylow elementary bound.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original moved pair has a commutator surviving the full central quotient. -/
theorem SourceHypothesis.nonsingular_hs_selected_moved_pair
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (s : G) (hs : s ∈ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype ⊓ Kv (v : G))
    (hsT : s ∉ Tv T (v : G)) :
    let W := Vv L V (v : G)
    let W' := W.map (MulAut.conj s).toMonoidHom
    Tv T (v : G) ≤ normalizer (W' : Set G) ∧
      W ⊔ W' ≤ Tv T (v : G) ∧
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype ≤
        normalizer ((W ⊔ W' : Subgroup G) : Set G) ∧
      ⁅W,W'⁆ ≤ W ⊓ W' ∧
      ¬ ⁅W,W'⁆ ≤ (center (Kv (v : G))).map (Kv (v : G)).subtype := by
  let C := Kv (v : G)
  let A := Tv T (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let W := Vv L V (v : G)
  let W' := W.map (MulAut.conj s).toMonoidHom
  let J := W ⊔ W'
  obtain ⟨hidx,hAn,hNW,_⟩ := H.nonsingular_hs_selected_sylow_geometry D v hv hK hTV hi e S hTS
  have hAN : A ≤ normalizer (W : Set G) := fun x hx => (hNW.ge hx).2
  have hSAn : S₀ ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hTS).mp hAn
  have hAm : A.map (MulAut.conj s).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hSAn hs.1)
  have hAN' : A ≤ normalizer (W' : Set G) := by
    rw [show W' = W.map (MulAut.conj s).toMonoidHom from rfl,
      ←map_equiv_normalizer_eq W (MulAut.conj s)]
    have hh := map_mono (f := (MulAut.conj s).toMonoidHom) hAN
    rwa [hAm] at hh
  have hWA : W ≤ A := (Vv_le_V H.chosen.normalizes _).trans
    (le_inf H.chosen.le_sylow (V_le_Gv v))
  have hW'A : W' ≤ A := by
    rw [←hAm]
    exact map_mono hWA
  have hSJ : S₀ ≤ normalizer (J : Set G) :=
    le_normalizer_sup_conjugate_of_relIndex_two W A S₀ hTS hidx hAN s hs.1 hsT
  have hcomm : ⁅W,W'⁆ ≤ W ⊓ W' := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hW'A.trans hAN))
    (le_normalizer_iff_commutator_le_right.mp (hWA.trans hAN'))
  refine ⟨hAN',sup_le hWA hW'A,hSJ,hcomm,?_⟩
  intro hcentral
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hW'C : W' ≤ C := by
    have hc : C.map (MulAut.conj s).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer hs.2)
    rw [←hc]
    exact map_mono hWC
  have hJC : J ≤ C := sup_le hWC hW'C
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let U := W.subgroupOf C
  let U' := W'.subgroupOf C
  have hk : f.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcommC : ⁅U,U'⁆ ≤ f.ker := by
    rw [hk]
    intro x hx
    have hh := mem_map_of_mem C.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hWC,map_subgroupOf_eq_of_le hW'C] at hh
    obtain ⟨z,hz,hzx⟩ := hcentral hh
    exact (C.subtype_injective hzx) ▸ hz
  have hcommf : ⁅U.map f,U'.map f⁆ = ⊥ := by
    rw [←map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr hcommC
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map (MulAut.conj s).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWC
  let : IsElementaryAbelian 2 U' := IsElementaryAbelian.subgroupOf hW'C
  let : IsElementaryAbelian 2 (U.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 (U'.map f) := IsElementaryAbelian.map f
  have hJf : (J.subgroupOf C).map f = U.map f ⊔ U'.map f := by
    rw [show J = W ⊔ W' from rfl,subgroupOf_sup hWC hW'C,Subgroup.map_sup]
  have hJe : IsElementaryAbelian 2 ((J.subgroupOf C).map f) := by
    rw [hJf]
    exact IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcommf))
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hPn : (P : Subgroup C) ≤ normalizer (J.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hJC]
    intro x hx
    exact hSJ (hP ▸ mem_map_of_mem C.subtype hx).1
  have hb := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight
    (P.mapSurjective (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    ((J.subgroupOf C).map f) hJe
    ((map_mono hPn).trans (le_normalizer_map f))
  have hw : Nat.card (U.map f) = 16 := by
    rw [show U.map f = (U.map (QuotientGroup.mk' (center C))).map e.toMonoidHom from
      (map_map _ _ _).symm,card_map_of_injective e.injective]
    exact H.nonsingular_hs_moved_image_card D v hv ⟨e⟩
  have hle : Nat.card (U.map f) ≤ Nat.card ((J.subgroupOf C).map f) :=
    card_le_of_le (map_mono (f := f) (comap_mono (show W ≤ J from le_sup_left)))
  omega

/-- The same conjugator supplies two mutually normalizing original modules.
Their commutator is central in their join but escapes the covering center. -/
theorem SourceHypothesis.nonsingular_hs_selected_original_pair
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (s : G) (hs : s ∈ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype ⊓ Kv (v : G))
    (hsT : s ∉ Tv T (v : G)) :
    let V' := V.map (MulAut.conj s).toMonoidHom
    Tv T (v : G) ≤ normalizer (V' : Set G) ∧
      V ⊔ V' ≤ Tv T (v : G) ∧
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype ≤
        normalizer ((V ⊔ V' : Subgroup G) : Set G) ∧
      (v : G) ∈ V ⊓ V' ∧
      ⁅V,V'⁆ ≤ V ⊓ V' ∧
      ⁅V,V'⁆ ≤ centralizer ((V ⊔ V' : Subgroup G) : Set G) ∧
      ¬ ⁅V,V'⁆ ≤ (center (Kv (v : G))).map (Kv (v : G)).subtype := by
  let A := Tv T (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let V' := V.map (MulAut.conj s).toMonoidHom
  obtain ⟨hidx,hAn,_,_⟩ := H.nonsingular_hs_selected_sylow_geometry D v hv hK hTV hi e S hTS
  have hn : A ≤ normalizer (V : Set G) := inf_le_left.trans hTV
  have hSAn : S₀ ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hTS).mp hAn
  have hAm : A.map (MulAut.conj s).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hSAn hs.1)
  have hn' : A ≤ normalizer (V' : Set G) := by
    rw [show V' = V.map (MulAut.conj s).toMonoidHom from rfl,
      ←map_equiv_normalizer_eq V (MulAut.conj s)]
    have hh := map_mono (f := (MulAut.conj s).toMonoidHom) hn
    rwa [hAm] at hh
  have hVA : V ≤ A := le_inf H.chosen.le_sylow (V_le_Gv v)
  have hV'A : V' ≤ A := by
    rw [←hAm]
    exact map_mono hVA
  have hcomm : ⁅V,V'⁆ ≤ V ⊓ V' := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hV'A.trans hn))
    (le_normalizer_iff_commutator_le_right.mp (hVA.trans hn'))
  refine ⟨hn',sup_le hVA hV'A,
    le_normalizer_sup_conjugate_of_relIndex_two V A S₀ hTS hidx hn s hs.1 hsT,
    ⟨v.property,?_⟩,hcomm,?_,?_⟩
  · refine ⟨v,v.property,?_⟩
    have hc := mem_centralizer_singleton_iff.mp (map_subtype_le _ hs.1)
    change s * (v : G) * s⁻¹ = v
    rw [hc,mul_inv_cancel_right]
  · let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map (MulAut.conj s).toMonoidHom
    apply le_centralizer_iff.mp
    apply sup_le
    · exact le_centralizer_iff.mp
        ((hcomm.trans inf_le_left).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
    · exact le_centralizer_iff.mp
        ((hcomm.trans inf_le_right).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  · intro hc
    have hWW := (H.nonsingular_hs_selected_moved_pair D v hv hK hTV hi e S hTS s hs hsT).2.2.2.2
    apply hWW
    exact (commutator_mono (Vv_le_V H.chosen.normalizes _)
      (map_mono (Vv_le_V H.chosen.normalizes _))).trans hc


/-- At the preferred source point, the same selected S and an actual
component element give both original pairs and a noncentral commutator.
The HS exclusion itself remains an obligation of the source assembly. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_noncentral_pair
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ZV L V = ⊥ ∧ Nat.card V = 64 ∧
      ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
        Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
        V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
        ZV (Lv L (w : G)) (Vv L V (w : G)) = zpowers (w : G) ∧
        (w : G) ∈ Vv L V (w : G) ∧ IsQuasisimple (Kv (w : G)) ∧
        NonsingularHSJankoCoverModels (Kv (w : G)) ∧
        ∃ S : Sylow 2 (Gv (w : G)),
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          Tv T (w : G) ≤ S₀ ∧
          R L (Kv (w : G)) S₀ (w : G) ≤ normalizer (Lv L (w : G) : Set G) ∧
          ⁅Lv L (w : G), R L (Kv (w : G)) S₀ (w : G)⁆ ≤ (Lv L (w : G)).pCoreIn 2 ∧
          R L (Kv (w : G)) S₀ (w : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (w : G)) ∧
          (Tv T (w : G)).relIndex S₀ ≤ 2 ∧
          ((Tv T (w : G)).subgroupOf S₀).Normal ∧
          ∀ e : ((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* Sporadic.LeechRelated.HS.Carrier,
            let C := Kv (w : G)
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
            let B := ((Lv L (w : G)).subgroupOf C).map f
            (Tv T (w : G)).relIndex S₀ = 2 ∧
            S₀ ⊓ normalizer (Vv L V (w : G) : Set G) = Tv T (w : G) ∧
            Tv T (w : G) ⊔ (S₀ ⊓ C) = S₀ ∧
            ((R L C S₀ (w : G)).subgroupOf C).map f =
              (S₀.subgroupOf C).map f ⊓ coreQuotientCentralizer B ∧
            S₀ ⊓ normalizer (V : Set G) = Tv T (w : G) ∧
            ∃ s ∈ S₀ ⊓ C, s ∉ Tv T (w : G) ∧
              let V' := V.map (MulAut.conj s).toMonoidHom
              let W := Vv L V (w : G)
              let W' := W.map (MulAut.conj s).toMonoidHom
              V' ≠ V ∧ W' ≠ W ∧ V' ⊓ C = W' ∧
              Tv T (w : G) ≤ normalizer (V' : Set G) ∧
              V ⊔ V' ≤ Tv T (w : G) ∧
              S₀ ≤ normalizer ((V ⊔ V' : Subgroup G) : Set G) ∧
              (w : G) ∈ V ⊓ V' ∧
              ⁅V,V'⁆ ≤ V ⊓ V' ∧
              ⁅V,V'⁆ ≤ centralizer ((V ⊔ V' : Subgroup G) : Set G) ∧
              ¬ ⁅V,V'⁆ ≤ (center C).map C.subtype ∧
              Tv T (w : G) ≤ normalizer (W' : Set G) ∧
              W ⊔ W' ≤ Tv T (w : G) ∧
              S₀ ≤ normalizer ((W ⊔ W' : Subgroup G) : Set G) ∧
              ⁅W,W'⁆ ≤ W ⊓ W' ∧
              ¬ ⁅W,W'⁆ ≤ (center C).map C.subtype := by
  obtain ⟨hz,hcard,w,hw,he,hs,hi,hlt,hnot,hcentral,hline,hwV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hidx,hAn,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_selected_sylow D hTV hTI v hv he
  refine ⟨hz,hcard,w,hw,he,hs,hi,hlt,hnot,hcentral,hline,hwV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hidx,hAn,?_⟩
  intro e
  obtain ⟨hiS,hNW,hgen,hRimage,hNV,s,hsC,hsT,hVne,hWne,_,hinter⟩ := hmodel e
  obtain ⟨hnV,hVT,hSV,hvI,hVI,hVC,hVZ⟩ :=
    H.nonsingular_hs_selected_original_pair D w hw hK hTV hi e S hTS s hsC hsT
  exact ⟨hiS,hNW,hgen,hRimage,hNV,s,hsC,hsT,hVne,hWne,hinter,
    hnV,hVT,hSV,hvI,hVI,hVC,hVZ,
    H.nonsingular_hs_selected_moved_pair D w hw hK hTV hi e S hTS s hsC hsT⟩

end CFSG.Quasithin.Chapter12.Section06
