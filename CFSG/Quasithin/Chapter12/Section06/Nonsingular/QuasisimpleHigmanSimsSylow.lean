module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsAction

/-!
# The original selected Sylow in the HS branch

Keep the Sylow S selected by 12.6.5. Its intersection with K_v maps to
an actual Sylow of HS. This subgroup cannot normalize the order-16 image
of V_v: the checked native bound for Sylow-normalized elementary subgroups
is eight. The strict source bound therefore forces [S:T_v]=2, identifies
S intersect N_G(V_v) with T_v, and gives S = T_v join (S intersect K_v).

At an escaping point the original equality V intersect K_v = V_v also
identifies S intersect N_G(V) with T_v. An element of S intersect K_v
therefore moves both original subgroups, while its conjugate of V remains
inside the original T_v. The same conjugator preserves their intersection.

The full central kernel lies in L_v. This lifts normalization from the
literal HS quotient and identifies the image of R intersect K_v with the
quotient centralizer intersection. The preferred-point consumer constructs
one S with all these conclusions and the original R-normalization and
commutator clauses. It retains the original V, fixed line, covering
catalogue and quotient map; the full cover action remains available from
the imported construction. No normalization of V or V_v by all of S is
assumed. The HS configuration still requires exclusion, as do J4 and the
remaining source inputs before 12.6.2 and 12.6.23 can be concluded.

Source: Aschbacher--Smith, 12.6.4--5 and 12.6.12, printed pp.824--826;
GLS3 Table 5.3m for the native HS Sylow elementary bound.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem intermediate_of_index_le_two (A B S : Subgroup G)
    (hAB : A ≤ B) (hBS : B ≤ S) (hi : A.relIndex S ≤ 2) :
    B = A ∨ B = S := by
  have hm := relIndex_mul_relIndex A B S hAB hBS
  have ha : A.relIndex B ≠ 0 := index_ne_zero_of_finite
  have hb : B.relIndex S ≠ 0 := index_ne_zero_of_finite
  have he : A.relIndex B = 1 ∨ B.relIndex S = 1 := by
    by_contra hh
    push Not at hh
    have ha2 : 2 ≤ A.relIndex B := by omega
    have hb2 : 2 ≤ B.relIndex S := by omega
    have := Nat.mul_le_mul ha2 hb2
    omega
  exact he.elim (fun h => .inl (le_antisymm (relIndex_eq_one.mp h) hAB))
    (fun h => .inr (le_antisymm hBS (relIndex_eq_one.mp h)))

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- No Sylow intersection with the original component normalizes its moved subgroup. -/
theorem SourceHypothesis.nonsingular_hs_component_sylow_not_normalizes_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G))) :
    ¬ ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype ⊓ Kv (v : G)) ≤
      normalizer (Vv L V (v : G) : Set G) := by
  let C := Kv (v : G)
  let W := (Vv L V (v : G)).subgroupOf C
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  intro hn
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  have hPn : (P : Subgroup C) ≤ normalizer (W : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    intro x hx
    exact hn (hP ▸ mem_map_of_mem C.subtype hx)
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWC
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hb := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight
    (P.mapSurjective hf) (W.map f) (IsElementaryAbelian.map f)
    ((map_mono hPn).trans (le_normalizer_map f))
  have hc : Nat.card (W.map f) = 16 := by
    rw [show W.map f = (W.map (QuotientGroup.mk' (center C))).map e.toMonoidHom from
      (map_map _ _ _).symm,card_map_of_injective e.injective]
    exact H.nonsingular_hs_moved_image_card D v hv ⟨e⟩
  omega

/-- The strict bound and native HS obstruction identify the exact normalizer
intersection in the same original S, and give its component supplement. -/
theorem SourceHypothesis.nonsingular_hs_selected_sylow_geometry
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    (Tv T (v : G)).relIndex S₀ = 2 ∧
      ((Tv T (v : G)).subgroupOf S₀).Normal ∧
      S₀ ⊓ normalizer (Vv L V (v : G) : Set G) = Tv T (v : G) ∧
      Tv T (v : G) ⊔ (S₀ ⊓ Kv (v : G)) = S₀ := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let A := Tv T (v : G)
  let N := normalizer (Vv L V (v : G) : Set G)
  have hnB : A ≤ normalizer (Lv L (v : G) : Set G) :=
    (inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans
      (Mv_le_normalizer_Lv L (v : G))
  have hn : A ≤ N := normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV) hnB
  have hnot := H.nonsingular_hs_component_sylow_not_normalizes_moved D v hv e S
  have hb := H.nonsingular_quasisimple_sylow_index_le_two D v hv hK hi S hTS
  have hne : A.relIndex S₀ ≠ 1 := by
    intro he
    exact hnot (inf_le_left.trans ((relIndex_eq_one.mp he).trans hn))
  have hpos : A.relIndex S₀ ≠ 0 := index_ne_zero_of_finite
  have hidx : A.relIndex S₀ = 2 := by change A.relIndex S₀ ≤ 2 at hb; omega
  refine ⟨hidx,H.nonsingular_quasisimple_Tv_normal_in_sylow D v hv hK hi S hTS,?_,?_⟩
  · rcases intermediate_of_index_le_two A (S₀ ⊓ N) S₀ (le_inf hTS hn) inf_le_left hb
      with he | he
    · exact he
    · exact (hnot (inf_le_left.trans ((show S₀ ≤ N from he ▸ (inf_le_right : S₀ ⊓ N ≤ N))))).elim
  · rcases intermediate_of_index_le_two A (A ⊔ (S₀ ⊓ Kv (v : G))) S₀
      le_sup_left (sup_le hTS inf_le_left) hb with he | he
    · exact (hnot ((he ▸ (show S₀ ⊓ Kv (v : G) ≤ A ⊔ (S₀ ⊓ Kv (v : G)) from
        le_sup_right)).trans hn)).elim
    · exact he


/-- At an escaping HS point the same S has precisely T_v as normalizer of
the original V as well. Its component supplies an actual conjugate of both
V and V_v, still contained in the original T_v. -/
theorem SourceHypothesis.nonsingular_hs_selected_sylow_conjugate
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ Kv (v : G) ≤ M L)
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    S₀ ⊓ normalizer (V : Set G) = Tv T (v : G) ∧
      ∃ s ∈ S₀ ⊓ Kv (v : G),
        s ∉ Tv T (v : G) ∧
        V.map (MulAut.conj s).toMonoidHom ≠ V ∧
        (Vv L V (v : G)).map (MulAut.conj s).toMonoidHom ≠ Vv L V (v : G) ∧
        V.map (MulAut.conj s).toMonoidHom ≤ Tv T (v : G) ∧
        V.map (MulAut.conj s).toMonoidHom ⊓ Kv (v : G) =
          (Vv L V (v : G)).map (MulAut.conj s).toMonoidHom := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let A := Tv T (v : G)
  let C := Kv (v : G)
  obtain ⟨_,hn,hW,_⟩ := H.nonsingular_hs_selected_sylow_geometry D v hv hK hTV hi e S hTS
  have hVC : V ⊓ C = Vv L V (v : G) :=
    (H.nonsingular_hs_original_geometry D v hv hK hTV hnot e).2.2.1
  have hSC : S₀ ≤ normalizer (C : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv (v : G)))
  have hNV : S₀ ⊓ normalizer (V : Set G) = A := by
    apply le_antisymm _ (le_inf hTS (inf_le_left.trans hTV))
    intro s hs
    apply hW.le
    refine ⟨hs.1,?_⟩
    rw [←hVC]
    exact inf_normalizer_le_normalizer_inf ⟨hs.2,hSC hs.1⟩
  refine ⟨hNV,?_⟩
  obtain ⟨s,hs,hsW⟩ := SetLike.not_le_iff_exists.mp
    (H.nonsingular_hs_component_sylow_not_normalizes_moved D v hv e S)
  have hsA : s ∉ A := fun hh => hsW (hW.ge hh).2
  have hsV : s ∉ normalizer (V : Set G) := fun hh => hsA (hNV.le ⟨hs.1,hh⟩)
  have hAn : S₀ ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hTS).mp hn
  have hAm : A.map (MulAut.conj s).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hAn hs.1)
  have hCm : C.map (MulAut.conj s).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (hSC hs.1)
  refine ⟨s,hs,hsA,(fun hh => hsV (mem_normalizer_iff_map_conj_eq.mpr hh)),
    (fun hh => hsW (mem_normalizer_iff_map_conj_eq.mpr hh)),?_,?_⟩
  · change V.map (MulAut.conj s).toMonoidHom ≤ A
    rw [←hAm]
    exact map_mono (le_inf H.chosen.le_sylow (V_le_Gv v))
  · change V.map (MulAut.conj s).toMonoidHom ⊓ C = _
    rw [←hCm,←map_inf _ _ _ (MulAut.conj s).injective,hVC]

/-- The original R survives the literal central projection as exactly the
intersection with the quotient centralizer of the actual A₆ local image.
Normalization is lifted using the full covering kernel inside L_v. -/
theorem SourceHypothesis.nonsingular_hs_R_component_image
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S₀ : Subgroup G)
    (hR : R L (Kv (v : G)) S₀ (v : G) =
      S₀ ⊓ coreQuotientCentralizer (Lv L (v : G))) :
    let C := Kv (v : G)
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
    let B := ((Lv L (v : G)).subgroupOf C).map f
    ((R L C S₀ (v : G)).subgroupOf C).map f =
      (S₀.subgroupOf C).map f ⊓ coreQuotientCentralizer B := by
  let C := Kv (v : G)
  let P := (Lv L (v : G)).subgroupOf C
  let W := (Vv L V (v : G)).subgroupOf C
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  have hPC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWC
  have hk : f.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkW : f.ker ≤ W := by
    rw [hk,←H.nonsingular_hs_fixed_line_eq_center D v hv hK ⟨e⟩]
    exact comap_mono inf_le_left
  have hkP : f.ker ≤ P := hkW.trans (comap_mono (Vv_le_Lv H.chosen v))
  have hp : IsPGroup 2 f.ker := (IsElementaryAbelian.isPGroup 2 W).to_le hkW
  have hcompare (x : C) :
      (x : G) ∈ coreQuotientCentralizer (Lv L (v : G)) ↔
        f x ∈ coreQuotientCentralizer (P.map f) := by
    have hsub (hn : x ∈ normalizer (P : Set C)) :
        x ∈ coreQuotientCentralizer P ↔
          (x : G) ∈ coreQuotientCentralizer (Lv L (v : G)) := by
      simpa only [P,map_subgroupOf_eq_of_le hPC,subtype_apply] using
        mem_coreQuotientCentralizer_iff_map C.subtype P
          (IsPGroup.ker_isPGroup_of_injective C.subtype_injective) hn
    constructor
    · intro hx
      have hn : x ∈ normalizer (P : Set C) := by
        rw [←subgroupOf_normalizer_eq hPC]
        exact coreQuotientCentralizer_le_normalizer _ hx
      exact (mem_coreQuotientCentralizer_iff_map f P hp hn).mp ((hsub hn).mpr hx)
    · intro hx
      have hn : x ∈ normalizer (P : Set C) := by
        have hm := le_normalizer_comap f
          (show x ∈ (normalizer (P.map f : Set Sporadic.LeechRelated.HS.Carrier)).comap f from
            coreQuotientCentralizer_le_normalizer _ hx)
        rwa [comap_map_eq_self hkP] at hm
      exact (hsub hn).mp ((mem_coreQuotientCentralizer_iff_map f P hp hn).mpr hx)
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hr := hR.le hx
    exact ⟨mem_map_of_mem f hr.1,(hcompare x).mp hr.2⟩
  · rintro ⟨⟨x,hx,rfl⟩,hy⟩
    exact ⟨x,hR.ge ⟨hx,(hcompare x).mpr hy⟩,rfl⟩

/-- At the source-preferred escaping point choose the original local Sylow
once. Its R, strict index, normality, HS quotient intersections and actual
conjugator all refer to this same witness. The HS and J₄ exclusions remain. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_selected_sylow
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
              V.map (MulAut.conj s).toMonoidHom ≠ V ∧
              (Vv L V (w : G)).map (MulAut.conj s).toMonoidHom ≠ Vv L V (w : G) ∧
              V.map (MulAut.conj s).toMonoidHom ≤ Tv T (w : G) ∧
              V.map (MulAut.conj s).toMonoidHom ⊓ C =
                (Vv L V (w : G)).map (MulAut.conj s).toMonoidHom := by
  obtain ⟨hz,hcard,w,hw,he,hs,hi,hlt,hnot,hcentral,hline,hwV,hK,hmodels⟩ :=
    H.exists_preferred_nonsingular_quasisimple_escape D hTV hTI v hv he
  obtain ⟨S,hTS,hR,hcomm,hReq⟩ := H.local_normalization_of_nonsingular D w hw hs hi
  refine ⟨hz,hcard,w,hw,he,hs,hi,hlt,hnot,hcentral,hline,hwV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,
    H.nonsingular_quasisimple_sylow_index_le_two D w hw hK hi S hTS,
    H.nonsingular_quasisimple_Tv_normal_in_sylow D w hw hK hi S hTS,?_⟩
  intro e
  obtain ⟨hidx,_,hNW,hgen⟩ := H.nonsingular_hs_selected_sylow_geometry D w hw hK hTV hi e S hTS
  exact ⟨hidx,hNW,hgen,H.nonsingular_hs_R_component_image D w hw hK e _ hReq,
    H.nonsingular_hs_selected_sylow_conjugate D w hw hK hTV hnot hi e S hTS⟩

end CFSG.Quasithin.Chapter12.Section06
