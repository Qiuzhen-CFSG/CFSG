module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerEscape

/-!
# The original symmetric quotient and residual supplement

Normality of L in LT and its actual A8 two-core quotient identify its
image in LT/Q as a self-centralizing normal A8. When Q<R_v, the original
A6 section normalizes a nontrivial two-subgroup in this quotient. The
symmetric-eight extension theorem therefore identifies LT/Q with S8 and
R_v/Q with a transposition subgroup. L and R_v consequently generate LT,
and the original relative index |R_v:Q| is exactly two.

The preferred-point application obtains strictness from normalizer escape
when the original C_V(L) is nontrivial. The terminal application removes
its separate index premise. Blocks, splitting, the remaining quasisimple
exclusions and fixed-space elimination are still required: neither12.6.2
nor12.6.23 is asserted. Earlier invariance/TI retain qt-d-1222-source and
final discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith, 12.6.18(4) and the conclusion of12.6.2,
printed pp.827--828, combined manuscript of1 March2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual LT/Q quotient and the literal transposition image of R_v. -/
theorem SourceHypothesis.nonsingular_original_symmetric_quotient
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hlt : Q T L < Rv T L (v : G)) :
    ∃ e : Star (LT T L) ≃* Equiv.Perm (Fin 8),
      (starImage (LT T L) L).map e.toMonoidHom = alternatingGroup (Fin 8) ∧
      ∃ t : Equiv.Perm (Fin 8), t.IsSwap ∧
        (starImage (LT T L) (Rv T L (v : G))).map e.toMonoidHom = zpowers t := by
  let J := LT T L
  let C := L.subgroupOf J
  let P := (T : Subgroup G).subgroupOf J
  let A₀ := (Lv L (v : G)).subgroupOf J
  let R₀ := (Rv T L (v : G)).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := C.map q
  let A := A₀.map q
  let R₁ := R₀.map q
  have hLJ : L ≤ J := le_sup_left
  have hAJ : Lv L (v : G) ≤ J := (Lv_le_L L _).trans hLJ
  have hRJ : Rv T L (v : G) ≤ J := (pCoreIn_le 2 _).trans inf_le_left
  have hJM : J ≤ M L := sup_le L.le_normalizer H.chosen.sylow_normalizes_component
  let : C.Normal := normal_subgroupOf_of_le_normalizer hJM
  let : B.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  have hcM := H.source.toHypothesis1221.sylow_normalized_component
    H.chosen.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hc : C.IsCComponent := hcM.subgroupOf_of_le hLJ hJM
  let c : C ≃* L := subgroupOfEquivOfLe hLJ
  let eB : B ≃* alternatingGroup (Fin 8) := (cComponentTwoCoreQuotientEquiv hc).symm.trans
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (D.coreQuotientEquiv H.chosen H.source.quasisimple))
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 8)) := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup B := eB.isSimpleGroup
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hgen : C ⊔ P = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLJ,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hp : IsPGroup 2 P := T.isPGroup'.comap_subtype
  have hquot : IsPGroup 2 (Star J ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (P.map q) (hp.map q) (by
      rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)])
  have hcent : centralizer (B : Set (Star J)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient B (Group.IsPerfect.not_isMulCommutative B)
      hquot (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨ea⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let a : A₀ ≃* Lv L (v : G) := subgroupOfEquivOfLe hAJ
  have hk : IsPGroup 2 (q.subgroupMap A₀).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6) :=
    ((q.subgroupMap A₀).pCoreQuotientEquiv (q.subgroupMap_surjective A₀) hk).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans ea)
  have h5 : 5 ∣ Nat.card A := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 A))
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hR : R₁ ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff R₀).mp he
    rw [QuotientGroup.ker_mk'] at hh
    have hm := map_mono (f := J.subtype) hh
    rw [map_subgroupOf_eq_of_le hRJ] at hm
    exact hlt.not_ge hm
  have hn : A ≤ normalizer (R₁ : Set (Star J)) := by
    apply le_trans (map_mono (show A₀ ≤ normalizer (R₀ : Set J) from ?_))
      (R₀.le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRJ]
    have hlocal : LT T L ⊓ Gv (v : G) ≤ normalizer (Rv T L (v : G) : Set G) :=
      (LT T L ⊓ Gv (v : G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    exact fun x hx => hlocal ⟨hAJ hx,Lv_le_Gv _ _ hx⟩
  obtain ⟨e,_,he,t,ht,hr,_⟩ :=
    Theory.SpecificGroups.Alternating.EightSectionExtension.exists_symmetric_equiv
      B A R₁ eB hcent (map_mono (comap_mono (Lv_le_L L _))) h5
      ((isPGroup_pCoreIn 2 _).comap_subtype.map q) hR hn
  exact ⟨e,he,t,ht,hr⟩

/-- Strict enlargement of the original core has index exactly two. -/
theorem SourceHypothesis.nonsingular_original_core_index
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hlt : Q T L < Rv T L (v : G)) :
    (Q T L).relIndex (Rv T L (v : G)) = 2 := by
  obtain ⟨e,_,t,ht,hr⟩ := H.nonsingular_original_symmetric_quotient D v hv hlt
  let J := LT T L
  let q := QuotientGroup.mk' (pCore 2 J)
  have hRJ : Rv T L (v : G) ≤ J := (pCoreIn_le 2 _).trans inf_le_left
  have hk : (Q T L).subgroupOf J = q.ker := by
    rw [QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective J.subtype_injective _
  rw [←relIndex_subgroupOf hRJ,hk,relIndex_ker]
  change Nat.card (starImage J (Rv T L (v : G))) = 2
  rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,hr,Nat.card_zpowers]
  exact ht.orderOf

/-- Source12.6.18(4), retaining the original L, T and R_v. -/
theorem SourceHypothesis.nonsingular_original_join
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hlt : Q T L < Rv T L (v : G)) :
    L ⊔ Rv T L (v : G) = LT T L := by
  obtain ⟨e,hB,t,ht,hr⟩ := H.nonsingular_original_symmetric_quotient D v hv hlt
  let J := LT T L
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  let W := (L ⊔ Rv T L (v : G)).subgroupOf J
  have hRJ : Rv T L (v : G) ≤ J := (pCoreIn_le 2 _).trans inf_le_left
  have hWJ : L ⊔ Rv T L (v : G) ≤ J := sup_le le_sup_left hRJ
  have hAlt : alternatingGroup (Fin 8) ≤ W.map f := by
    rw [←hB,starImage,map_map]
    exact map_mono (comap_mono le_sup_left)
  have htrans : t ∈ W.map f := by
    have hle : zpowers t ≤ W.map f := by
      rw [←hr,starImage,map_map]
      exact map_mono (comap_mono le_sup_right)
    exact hle (mem_zpowers t)
  have htop : W.map f = ⊤ := by
    apply top_unique
    intro p _
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
    · exact hAlt (Equiv.Perm.mem_alternatingGroup.mpr hp)
    · have hpt : p*t ∈ W.map f := hAlt (Equiv.Perm.mem_alternatingGroup.mpr (by
        rw [map_mul,hp,ht.sign_eq]; norm_num))
      simpa only [mul_inv_cancel_right] using (W.map f).mul_mem hpt ((W.map f).inv_mem htrans)
  have hk : f.ker ≤ W := by
    intro x hx
    have he : QuotientGroup.mk' (pCore 2 J) x = 1 := e.injective
      (hx.trans e.map_one.symm)
    have hmem : x ∈ pCore 2 J := (QuotientGroup.eq_one_iff x).mp he
    exact mem_sup_right (hlt.le (mem_map_of_mem J.subtype hmem))
  have hW : W = ⊤ := by
    rw [←comap_map_eq_self hk,htop,comap_top]
  have hh := congrArg (map J.subtype) hW
  rwa [map_subgroupOf_eq_of_le hWJ,←MonoidHom.range_eq_map,range_subtype] at hh

/-- The preferred escaping point supplies the original symmetric quotient,
its transposition image, the exact core index and the source join identity. -/
theorem SourceHypothesis.exists_preferred_nonsingular_original_extension_of_fixed
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
      ¬ normalizer (Rv T L (w : G) : Set G) ≤ M L ∧
      Q T L < Rv T L (w : G) ∧
      (Q T L).relIndex (Rv T L (w : G)) = 2 ∧
      L ⊔ Rv T L (w : G) = LT T L ∧
      ∃ e : Star (LT T L) ≃* Equiv.Perm (Fin 8),
        (starImage (LT T L) L).map e.toMonoidHom = alternatingGroup (Fin 8) ∧
        ∃ t : Equiv.Perm (Fin 8), t.IsSwap ∧
          (starImage (LT T L) (Rv T L (w : G))).map e.toMonoidHom = zpowers t := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,hr⟩ :=
    H.exists_preferred_nonsingular_normalizer_escape_of_fixed D hTV hTI hz v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,hr,
    H.nonsingular_original_core_index D w hw hr,
    H.nonsingular_original_join D w hw hr,
    H.nonsingular_original_symmetric_quotient D w hw hr⟩

/-- The terminal consumer's exact index follows from normalizer escape.
Its elementary-core, local-core and displacement premises still need the
source block and splitting arguments. -/
theorem SourceHypothesis.nonsingular_terminal_contradiction_of_normalizer_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (S : Subgroup G)
    (v : V) (hv : D.Nonsingular v)
    (he : ¬ Kv (v : G) ≤ M L)
    (hn : ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (hcore : Rv T L (v : G) = (Kv (v : G) ⊔ S).pCoreIn 2)
    (hQ : IsElementaryAbelian 2 (Q T L))
    (r : G) (hr : r ∈ Rv T L (v : G))
    (hcomm : ⁅Rv T L (v : G), zpowers r⁆ = zpowers (v : G)) : False := by
  have hlt : Q T L < Rv T L (v : G) := lt_of_le_of_ne (Q_le_Rv H.chosen v)
    (fun heq => hn (heq ▸ H.core_normalizer_le))
  exact H.nonsingular_terminal_contradiction D S v hv he hcore hQ
    (H.nonsingular_original_core_index D v hv hlt) r hr hcomm
end CFSG.Quasithin.Chapter12.Section06
