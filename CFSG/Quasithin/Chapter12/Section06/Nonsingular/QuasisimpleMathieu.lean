module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleSource
public import Theory.Mathieu.M22.Properties.LargeElementaryPerfectNormalizer

/-!
# The M₂₂ exclusion for the original nonsingular residual

Conjugation by the original V descends faithfully from the perfect K_v to
its central quotient. Its image has order at least 32, by the proved corank
of C_V(K_v). The literal L_v image normalizes this elementary subgroup:
L_v normalizes V, and both act through the same ambient normalizer map.
Its A₆ two-core quotient survives the central projection, so its order is
divisible by nine. The intrinsic M₂₂ perfect-normalizer obstruction now
excludes that central quotient, without replacing V by V/C_V(L).

The preferred-point application reduces the earlier seven-row catalogue
to six rows. Their exclusions, the original blocks and splitting, and the
fixed-space elimination remain required for 12.6.2 and 12.6.23. Earlier
T-invariance and TI retain producer qt-d-1222-source and final discharge
owner qt-d-12634-source.

Source: Aschbacher--Smith, Lemma 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original V-action and surviving A₆ local image exclude the M₂₂
central quotient. The action uses K_v/Z(K_v) and the canonical projection. -/
theorem SourceHypothesis.nonsingular_not_mathieu22_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.Mathieu.M22) := by
  let C := Kv (v : G)
  let := hK
  rintro ⟨e⟩
  let N := normalizer (C : Set G)
  have hCN : Gv (v : G) ≤ N :=
    (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)
  have hVN : V ≤ N := (V_le_Gv v).trans hCN
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _ eA
  have hLN : Lv L (v : G) ≤ N := hLC.trans C.le_normalizer
  let : Group.IsPerfect (Lv L (v : G)) := Lv_isPerfect_of_A6 L _ eA
  let f : N →* MulAut Sporadic.Mathieu.M22 :=
    (MulAut.centralQuotientAction e).comp C.normalizerMonoidHom
  let aV := C.normalizerMonoidHom.comp (inclusion hVN)
  let rV := f.comp (inclusion hVN)
  let rL := f.comp (inclusion hLN)
  let E := rV.range
  let B := rL.range
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_surjective rV.rangeRestrict rV.rangeRestrict_surjective
  let : Group.IsPerfect B := Group.IsPerfect.range rL
  have hn : B ≤ normalizer (E : Set (MulAut Sporadic.Mathieu.M22)) := by
    dsimp only [B,E,rV,rL]
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,inclusion_range]
    apply (map_mono (f := f) ?_).trans (le_normalizer_map f)
    rw [←subgroupOf_normalizer_eq hVN]
    exact comap_mono ((Lv_le_L L _).trans H.chosen.normalizes)
  have hk : rV.ker = (centralizer (C : Set G)).subgroupOf V := by
    ext x
    change MulAut.centralQuotientAction e (aV x) = 1 ↔ _
    rw [← (MulAut.centralQuotientAction e).map_one,
      (MulAut.centralQuotientAction_injective e).eq_iff]
    change inclusion hVN x ∈ C.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hc : Nat.card E = (centralizer (C : Set G)).relIndex V := by
    change Nat.card rV.range = _
    rw [←index_ker,hk]
    rfl
  have hE : 32 ≤ Nat.card E := by
    have hr := H.nonsingular_component_centralizer_corank D v hv
    rw [←hc] at hr
    exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans (Nat.pow_log_le_self 2 Nat.card_pos.ne')
  let q := QuotientGroup.mk' (center C)
  let j := MulAut.conj.comp e.toMonoidHom
  have hj : Function.Injective j :=
    (MulAut.conj_injective_of_center_eq_bot Sporadic.Mathieu.m22_center_eq_bot).comp e.injective
  have hrL : rL = j.comp (q.comp (inclusion hLC)) := by
    apply MonoidHom.ext
    intro l
    change MulAut.centralQuotientAction e (C.normalizerMonoidHom (inclusion hLN l)) = _
    have hinner : C.normalizerMonoidHom (inclusion hLN l) = MulAut.conj (inclusion hLC l) := by
      ext x
      rfl
    rw [hinner,MulAut.centralQuotientAction_conj]
    rfl
  have h9 : 9 ∣ Nat.card B := by
    dsimp only [B]
    rw [hrL,MonoidHom.range_comp,card_map_of_injective hj,
      MonoidHom.range_comp,inclusion_range]
    obtain ⟨_,⟨eQ⟩,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 _))
    rw [Nat.card_congr eQ.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  exact Sporadic.Mathieu.M22LargeElementary.no_perfect_large_elementary_normalizer B E hn hE h9

/-- Removing M₂₂ leaves six concrete central-quotient possibilities. -/
theorem SourceHypothesis.nonsingular_quasisimple_models_after_mathieu22
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    let C := (Kv (v : G)) ⧸ center (Kv (v : G))
    ClassicalGroup.IsPSL C 5 2 ∨
      (∃ name : ClassificationModels.SporadicName,
        (name = .m24 ∨ name = .hs ∨ name = .he ∨ name = .ru ∨ name = .j4) ∧
          Nonempty (C ≃* name.Carrier)) := by
  rcases H.nonsingular_quasisimple_finite_models D v hv hK with h | ⟨name,hn,he⟩
  · exact .inl h
  · right
    refine ⟨name,?_,he⟩
    rcases hn with rfl | hn
    · exact (H.nonsingular_not_mathieu22_centralQuotient D v hv hK he).elim
    · exact hn

/-- Apply the M₂₂ exclusion to the original preferred escaping point, retaining
its Sylow position, literal component, V and C_V(L). The earlier invariance
and TI inputs still have producer qt-d-1222-source and final discharge owner
qt-d-12634-source. This partial catalogue does not assert 12.6.2 or 12.6.23. -/
theorem SourceHypothesis.exists_preferred_nonsingular_models_after_mathieu22
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ((Kv (w : G)).subgroupOf (Gv (w : G))).IsCComponent ∧
      IsQuasisimple (Star (Kv (w : G))) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      (IsQuasisimple (Kv (w : G)) →
        let C := (Kv (w : G)) ⧸ center (Kv (w : G))
        ClassicalGroup.IsPSL C 5 2 ∨
          (∃ name : ClassificationModels.SporadicName,
            (name = .m24 ∨ name = .hs ∨ name = .he ∨ name = .ru ∨ name = .j4) ∧
              Nonempty (C ≃* name.Carrier))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple⟩ :=
    H.exists_preferred_nonsingular_component_escape D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,
    H.nonsingular_quasisimple_models_after_mathieu22 D w hw⟩

end CFSG.Quasithin.Chapter12.Section06
