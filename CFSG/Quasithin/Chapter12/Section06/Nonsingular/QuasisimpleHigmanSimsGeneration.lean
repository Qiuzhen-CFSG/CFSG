module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsPair
public import Theory.GroupTheory.IndexTwoConjugateCommutator
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.CubicOrder

/-!
# Full HS component generation and movement of the original pair

Keep the Sylow S and component K_v at the original nonsingular point.
The image of L_v has order divisible by nine, whereas no proper overgroup
of a full HS Sylow has order divisible by nine. Thus L_v and S intersect K_v
generate K_v modulo its center. The full covering center already lies in
L_v, so this is generation of the original K_v, with no kernel discarded.

Consequently a two-subgroup inside K_v normalized by both L_v and S is
central in K_v. The index-two action on the previously constructed pairs
preserves their intersections and commutators as well as their joins.
Their noncentral commutator therefore forces L_v to move all three
subgroups for each pair. More generally, every S-invariant subgroup of
T_v containing that commutator is moved by L_v, even if it is not contained
in K_v: intersect it with the original K_v before applying the core bound.

The preferred-point consumer retains the same S, R, actual conjugator,
original V and V_v, full covering center, and literal quotient map.
These are restrictions on the surviving HS configuration, not its exclusion.
The ambient contradiction, J4 exclusion and remaining source discharge for
12.6.2 and 12.6.23 remain necessary.

Source: Aschbacher--Smith, 12.6.4--5 and the proof of 12.6.12,
printed pp.824--826; A.3.12(18), printed pp.47--48, for the HS Sylow
overgroup restriction, proved here using the existing native carrier API.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual local residual and the component intersection of the original
selected Sylow generate the full HS cover, including its entire center. -/
theorem SourceHypothesis.nonsingular_hs_component_generation
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G))) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    Lv L (v : G) ⊔ (S₀ ⊓ Kv (v : G)) = Kv (v : G) ∧
      Lv L (v : G) ⊔ S₀ = Kv (v : G) ⊔ S₀ := by
  let C := Kv (v : G)
  let A := (Lv L (v : G)).subgroupOf C
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have hAC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have h9 : 9 ∣ Nat.card (A.map f) := by
    rw [show A.map f = (A.map (QuotientGroup.mk' (center C))).map e.toMonoidHom from
      (map_map _ _ _).symm,card_map_of_injective e.injective]
    obtain ⟨_,⟨eA⟩,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 _))
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have htop : (A ⊔ (P : Subgroup C)).map f = ⊤ := by
    by_contra hproper
    exact Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_not_nine_dvd
      (P.mapSurjective hf) _ (map_mono le_sup_right) hproper
      (h9.trans (card_dvd_of_le (map_mono le_sup_left)))
  have hk : f.ker ≤ A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
      ←H.nonsingular_hs_fixed_line_eq_center D v hv hK ⟨e⟩]
    exact comap_mono (inf_le_left.trans (Vv_le_Lv H.chosen v))
  have hgen : A ⊔ (P : Subgroup C) = ⊤ := by
    have hh := congrArg (comap f) htop
    rwa [comap_map_eq_self (hk.trans le_sup_left),comap_top] at hh
  have hgenG := congrArg (map C.subtype) hgen
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAC,hP,←MonoidHom.range_eq_map,range_subtype] at hgenG
  refine ⟨hgenG,le_antisymm (sup_le_sup_right hAC _) ?_⟩
  change C ⊔ S₀ ≤ Lv L (v : G) ⊔ S₀
  rw [←hgenG]
  exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right

/-- A two-subgroup inside the original component, normalized by the same S
and by L_v, must lie in the full covering center. -/
theorem SourceHypothesis.nonsingular_hs_two_subgroup_central_of_normalized
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G))) (U : Subgroup G)
    (hU : IsPGroup 2 U) (hUC : U ≤ Kv (v : G))
    (hSU : (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype ≤ normalizer (U : Set G))
    (hLU : Lv L (v : G) ≤ normalizer (U : Set G)) :
    U ≤ (center (Kv (v : G))).map (Kv (v : G)).subtype := by
  let := hK
  have hn : Kv (v : G) ≤ normalizer (U : Set G) := by
    rw [←(H.nonsingular_hs_component_generation D v hv hK e S).1]
    exact sup_le hLU (inf_le_left.trans hSU)
  exact (le_pCoreIn_of_normalizes hU hUC hn).trans
    (map_mono (IsQuasisimple.pCore_le_center 2))

end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- For the same actual component conjugator, S preserves both intersections
and commutators. The local residual moves the intersection, commutator and
join of each pair, including the pair of full original modules V. -/
theorem SourceHypothesis.nonsingular_hs_selected_pair_movement
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
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let W := Vv L V (v : G)
    let W' := W.map (MulAut.conj s).toMonoidHom
    let V' := V.map (MulAut.conj s).toMonoidHom
    S₀ ≤ normalizer ((W ⊓ W' : Subgroup G) : Set G) ⊓
        normalizer ((⁅W,W'⁆ : Subgroup G) : Set G) ∧
      S₀ ≤ normalizer ((V ⊓ V' : Subgroup G) : Set G) ⊓
        normalizer ((⁅V,V'⁆ : Subgroup G) : Set G) ∧
      (∀ U : Subgroup G,
        ⁅W,W'⁆ ≤ U → U ≤ Tv T (v : G) → S₀ ≤ normalizer (U : Set G) →
        ¬ Lv L (v : G) ≤ normalizer (U : Set G)) ∧
      ¬ Lv L (v : G) ≤ normalizer ((W ⊓ W' : Subgroup G) : Set G) ∧
      ¬ Lv L (v : G) ≤ normalizer ((⁅W,W'⁆ : Subgroup G) : Set G) ∧
      ¬ Lv L (v : G) ≤ normalizer ((W ⊔ W' : Subgroup G) : Set G) ∧
      ¬ Lv L (v : G) ≤ normalizer ((V ⊓ V' : Subgroup G) : Set G) ∧
      ¬ Lv L (v : G) ≤ normalizer ((⁅V,V'⁆ : Subgroup G) : Set G) ∧
      ¬ Lv L (v : G) ≤ normalizer ((V ⊔ V' : Subgroup G) : Set G) := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let C := Kv (v : G)
  let W := Vv L V (v : G)
  let W' := W.map (MulAut.conj s).toMonoidHom
  let V' := V.map (MulAut.conj s).toMonoidHom
  obtain ⟨hidx,_,hNW,_⟩ := H.nonsingular_hs_selected_sylow_geometry D v hv hK hTV hi e S hTS
  have hWN : Tv T (v : G) ≤ normalizer (W : Set G) := fun x hx => (hNW.ge hx).2
  have hNSW := le_normalizer_inf_and_commutator_conjugate_of_relIndex_two
    W (Tv T (v : G)) S₀ hTS hidx hWN s hs.1 hsT
  have hNSV := le_normalizer_inf_and_commutator_conjugate_of_relIndex_two
    V (Tv T (v : G)) S₀ hTS hidx (inf_le_left.trans hTV) s hs.1 hsT
  obtain ⟨_,hWJT,hSWJ,hDI,hnot⟩ :=
    H.nonsingular_hs_selected_moved_pair D v hv hK hTV hi e S hTS s hs hsT
  obtain ⟨_,hVJT,hSVJ,_,hVI,_,_⟩ :=
    H.nonsingular_hs_selected_original_pair D v hv hK hTV hi e S hTS s hs hsT
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hDC : ⁅W,W'⁆ ≤ C := (hDI.trans inf_le_left).trans hWC
  have hSC : S₀ ≤ normalizer (C : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv (v : G)))
  have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hmove (U : Subgroup G) (hDU : ⁅W,W'⁆ ≤ U) (hUT : U ≤ Tv T (v : G))
      (hSU : S₀ ≤ normalizer (U : Set G)) :
      ¬ Lv L (v : G) ≤ normalizer (U : Set G) := by
    intro hLU
    apply hnot
    apply (le_inf hDU hDC).trans
    apply H.nonsingular_hs_two_subgroup_central_of_normalized D v hv hK e S (U ⊓ C)
    · exact T.isPGroup'.to_le (inf_le_left.trans (hUT.trans inf_le_left))
    · exact inf_le_right
    · exact (le_inf hSU hSC).trans inf_normalizer_le_normalizer_inf
    · exact (le_inf hLU (hLC.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hWIT : W ⊓ W' ≤ Tv T (v : G) := inf_le_left.trans (le_sup_left.trans hWJT)
  have hDIT : ⁅W,W'⁆ ≤ Tv T (v : G) := hDI.trans hWIT
  have hDV : ⁅W,W'⁆ ≤ ⁅V,V'⁆ :=
    commutator_mono (Vv_le_V H.chosen.normalizes _) (map_mono (Vv_le_V H.chosen.normalizes _))
  have hVIT : V ⊓ V' ≤ Tv T (v : G) := inf_le_left.trans (le_sup_left.trans hVJT)
  exact ⟨hNSW,hNSV,hmove,
    hmove (W ⊓ W') hDI hWIT (hNSW.trans inf_le_left),
    hmove ⁅W,W'⁆ le_rfl hDIT (hNSW.trans inf_le_right),
    hmove (W ⊔ W') (hDI.trans (inf_le_left.trans le_sup_left)) hWJT hSWJ,
    hmove (V ⊓ V') (hDV.trans hVI) hVIT (hNSV.trans inf_le_left),
    hmove ⁅V,V'⁆ hDV (hVI.trans hVIT) (hNSV.trans inf_le_right),
    hmove (V ⊔ V') (hDV.trans (hVI.trans (inf_le_left.trans le_sup_left))) hVJT hSVJ⟩

end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Apply full-component generation and forced pair movement at the original
preferred escaping point, retaining the same S, R, covering center and maps.
The HS exclusion itself remains open. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_generated_pair
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
            Lv L (w : G) ⊔ (S₀ ⊓ C) = C ∧
            Lv L (w : G) ⊔ S₀ = C ⊔ S₀ ∧
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
              ¬ ⁅W,W'⁆ ≤ (center C).map C.subtype ∧
              S₀ ≤ normalizer ((W ⊓ W' : Subgroup G) : Set G) ⊓
                normalizer ((⁅W,W'⁆ : Subgroup G) : Set G) ∧
              S₀ ≤ normalizer ((V ⊓ V' : Subgroup G) : Set G) ⊓
                normalizer ((⁅V,V'⁆ : Subgroup G) : Set G) ∧
              (∀ U : Subgroup G,
                ⁅W,W'⁆ ≤ U → U ≤ Tv T (w : G) → S₀ ≤ normalizer (U : Set G) →
                ¬ Lv L (w : G) ≤ normalizer (U : Set G)) ∧
              ¬ Lv L (w : G) ≤ normalizer ((W ⊓ W' : Subgroup G) : Set G) ∧
              ¬ Lv L (w : G) ≤ normalizer ((⁅W,W'⁆ : Subgroup G) : Set G) ∧
              ¬ Lv L (w : G) ≤ normalizer ((W ⊔ W' : Subgroup G) : Set G) ∧
              ¬ Lv L (w : G) ≤ normalizer ((V ⊓ V' : Subgroup G) : Set G) ∧
              ¬ Lv L (w : G) ≤ normalizer ((⁅V,V'⁆ : Subgroup G) : Set G) ∧
              ¬ Lv L (w : G) ≤ normalizer ((V ⊔ V' : Subgroup G) : Set G) := by
  obtain ⟨hz,hcard,w,hw,he,hs,hi,hlt,hnot,hcentral,hline,hwV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hidx,hAn,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_noncentral_pair D hTV hTI v hv he
  refine ⟨hz,hcard,w,hw,he,hs,hi,hlt,hnot,hcentral,hline,hwV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hidx,hAn,?_⟩
  intro e
  obtain ⟨hiS,hNW,hgen,hRimage,hNV,s,hsC,hsT,hVne,hWne,hinter,
    hnV,hVT,hSV,hvI,hVI,hVC,hVZ,hnW,hWT,hSW,hWI,hWZ⟩ := hmodel e
  obtain ⟨hgenC,hgenCS⟩ := H.nonsingular_hs_component_generation D w hw hK e S
  exact ⟨hiS,hNW,hgen,hRimage,hNV,hgenC,hgenCS,s,hsC,hsT,hVne,hWne,hinter,
    hnV,hVT,hSV,hvI,hVI,hVC,hVZ,hnW,hWT,hSW,hWI,hWZ,
    H.nonsingular_hs_selected_pair_movement D w hw hK hTV hi e S hTS s hsC hsT⟩

end CFSG.Quasithin.Chapter12.Section06
