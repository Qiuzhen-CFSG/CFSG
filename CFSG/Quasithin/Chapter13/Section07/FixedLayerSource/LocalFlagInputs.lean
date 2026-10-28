module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.NaturalLift
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.LocalExclusion
public import Theory.GroupTheory.PResidual.NormalClosureCover

/-!
# Original local actor inputs for the fixed-layer flag

The original two-core O₂(LT) lies in T and is normalized by L₁T. The image
of L₁ is nontrivial and two-perfect, so the local quotient image is not a
two-group. Its two-residual lies in that same L₁ image. These are the
literal source inputs to the doubled-natural line-parabolic calculation.

Source: Aschbacher–Smith13.7.16(2), printed p.944.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterF.Section09.Setup Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
 {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_fixed_layer_local_inputs
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let π := QuotientGroup.mk' (pCore 2 H)
    let S := ((T : Subgroup G).subgroupOf H).map π
    let P := ((F.L₁ ⊔ (T : Subgroup G)).subgroupOf H).map π
    let N := ((L ⊔ (T : Subgroup G)).pCoreIn 2 |>.subgroupOf H).map π
    S ≤ P ∧ P ≤ normalizer N ∧ N ≤ S ∧ ¬ IsPGroup 2 P ∧
      (pResidual 2 P).map P.subtype ≤ (F.L₁.subgroupOf H).map π := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := (F.L₁.subgroupOf H).map π
  let S := ((T : Subgroup G).subgroupOf H).map π
  let P := ((F.L₁ ⊔ (T : Subgroup G)).subgroupOf H).map π
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let N := (Q.subgroupOf H).map π
  have hTH : (T : Subgroup G) ≤ H := h.T_le_H
  have hLH : F.L₁ ≤ H := le_sup_left.trans h.local_le
  have hL1L : F.L₁ ≤ L := (map_subtype_le _).trans inf_le_left
  have hQT : Q ≤ (T : Subgroup G) := h.sylow_centralizer.symm.le.trans inf_le_left
  have hQH : Q ≤ H := hQT.trans h.T_le_H
  have hPQ : F.L₁ ⊔ (T : Subgroup G) ≤ normalizer Q :=
    (sup_le (hL1L.trans le_sup_left) le_sup_right).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hPN : P ≤ normalizer N := by
    apply (map_mono (f := π) ?_).trans ((Q.subgroupOf H).le_normalizer_map π)
    rw [←subgroupOf_normalizer_eq hQH]
    exact comap_mono hPQ
  have hTN : (T : Subgroup G) ≤ normalizer F.L₁ := by
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image
      (F.L ⊓ F.Gz) (pResidual 2 (F.L ⊓ F.Gz : Subgroup G)))
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq,map_inf _ _ _ (MulAut.conj t).injective,
      mem_normalizer_iff_map_conj_eq.mp (h.normalizes_L ht),
      mem_normalizer_iff_map_conj_eq.mp
        (F.Gz.le_normalizer (h.H_centralizes (h.T_le_H ht)))]
  have hPJ : P ≤ normalizer J := by
    apply (map_mono (f := π) ?_).trans ((F.L₁.subgroupOf H).le_normalizer_map π)
    rw [←subgroupOf_normalizer_eq hLH]
    exact comap_mono (sup_le F.L₁.le_normalizer hTN)
  have hJP : J ≤ P := map_mono (comap_mono le_sup_left)
  have hSP : S ≤ P := map_mono (comap_mono le_sup_right)
  have hgen : J ⊔ S = P := by
    rw [←Subgroup.map_sup,←subgroupOf_sup hLH hTH]
  have hpJ : IsPPerfect 2 J := by
    have hp := isPPerfect_embedded_pResidual 2 (F.L ⊓ F.Gz)
    have hp' := hp.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
    exact hp'.of_surjective (π.subgroupMap (F.L₁.subgroupOf H)) (π.subgroupMap_surjective _)
  have hJn : J ≠ ⊥ := by
    intro hz
    apply PlusAction.local_residual_not_le_kernel d h hne
    rw [hk]
    intro x hx
    have he : π ⟨x,hLH hx⟩ ∈ J := mem_map_of_mem π hx
    rw [hz,mem_bot] at he
    exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp he)
  have hnP : ¬ IsPGroup 2 P := by
    intro hP
    have hh := hpJ.hom_eq_one_of_isPGroup (hP.to_le hJP) (MonoidHom.id J)
    apply hJn
    apply bot_unique
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hh ⟨x,hx⟩)
  have hS2 : IsPGroup 2 S := T.isPGroup'.comap_subtype.map π
  refine ⟨hSP,hPN,map_mono (comap_mono hQT),hnP,?_⟩
  let : (J.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPJ
  have hquot : IsPGroup 2 (P ⧸ J.subgroupOf P) :=
    isPGroup_quotient_of_sup_eq_top (J.subgroupOf P) (S.subgroupOf P) hS2.comap_subtype
      (by rw [←subgroupOf_sup hJP hSP,hgen,subgroupOf_self])
  have hr : pResidual 2 P ≤ J.subgroupOf P := sInf_le ⟨inferInstance,hquot⟩
  exact (map_mono hr).trans_eq (map_subgroupOf_eq_of_le hJP)
end CFSG.Quasithin.Chapter13.Section07
