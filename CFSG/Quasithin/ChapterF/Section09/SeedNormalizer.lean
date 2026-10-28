module
public import Theory.GroupTheory.Commutator.MovedSeedNormalizer
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PResidual.PerfectCover
public import CFSG.Quasithin.ChapterF.Section09.Commutator

/-!
# The actual centralizer and normalizers in F.9.5(3)

The original moved-seed identity V₊=V₁[U_H,V] identifies the subgroup
preserved by the quotient actor normalizer. Its image has order two,
so its normalizer is its centralizer. Hypothesis F.9.1(c) and
V₊=V∩O₂(H) give both actual normalizer equalities. The pullback statement
retains every representative under H→H/O₂(H), and restriction to any K
therefore gives exactly C_{K*}(V*)=N_K(V)*.

A separate normalization theorem uses the explicit bound N_H(V)≤N_G(L)
to normalize the original point-centralizer residual L₁. That bound is
supplied by Chapter13 in the A₅ application; it is not assumed in F.9.5(3).
Source: Aschbacher–Smith F.9.5(1–3), printed p.319, and13.5.21(ii), p.923.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

theorem star_module_ne_bot_iff_not_le_core :
    (D.V.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) ≠ ⊥ ↔ ¬ D.V ≤ D.QH := by
  rw [ne_eq,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  apply not_congr
  constructor
  · intro hv v hvV
    exact mem_map_of_mem D.H.subtype (hv (show (⟨v,h.V_le_H hvV⟩:D.H)∈D.V.subgroupOf D.H from hvV))
  · intro hv v hvV
    obtain ⟨q,hq,he⟩ := hv hvV
    exact (show q=v from Subtype.ext he) ▸ hq

theorem star_module_card_two (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) :
    Nat.card ((D.V.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) = 2 := by
  rw [←relIndex_ker,QuotientGroup.ker_mk']
  have he := relIndex_map_map_of_injective (pCore 2 D.H) (D.V.subgroupOf D.H) D.H.subtype_injective
  rw [map_subgroupOf_eq_of_le h.V_le_H] at he
  rw [←he]
  change D.QH.relIndex D.V = 2
  rw [←inf_relIndex_left D.V D.QH,h.seed_eq_intersection_of_not_le_core hi hn,hi]

theorem normalizer_seed_eq_normalizer_module
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) :
    D.H ⊓ normalizer (D.Vplus : Set G) = D.H ⊓ normalizer (D.V : Set G) := by
  apply le_antisymm h.normalizer_control
  refine le_inf inf_le_left ?_
  rw [←h.seed_eq_intersection_of_not_le_core hi hn]
  exact (le_inf inf_le_right (inf_le_left.trans (H_normalizes_QH (D := D)))).trans
    inf_normalizer_le_normalizer_inf

theorem star_centralizer_preimage
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) :
    (centralizer ((D.V.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) :
      Set (D.H ⧸ pCore 2 D.H))).comap (QuotientGroup.mk' (pCore 2 D.H)) =
      (normalizer (D.V : Set G)).subgroupOf D.H := by
  let := h.UH_normal
  let := h.point_normal
  have hseed : D.Vplus.subgroupOf D.H = D.V₁.subgroupOf D.H ⊔
      ⁅D.UH.subgroupOf D.H,D.V.subgroupOf D.H⁆ := by
    apply map_injective D.H.subtype_injective
    rw [Subgroup.map_sup,map_commutator,map_subgroupOf_eq_of_le h.plus_le_H,
      map_subgroupOf_eq_of_le h.point_le_H,map_subgroupOf_eq_of_le h.UH_le_H,
      map_subgroupOf_eq_of_le h.V_le_H]
    exact h.seed_eq_point_sup_commutator hi hn
  have hc : ⁅D.UH.subgroupOf D.H,pCore 2 D.H⁆ ≤ D.V₁.subgroupOf D.H := by
    apply (map_le_map_iff_of_injective D.H.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le h.UH_le_H,
      map_subgroupOf_eq_of_le h.point_le_H]
    exact h.commutator_UH_QH_le_point
  have hpres := normalizer_quotient_preserves_moved_seed
    (D.UH.subgroupOf D.H) (D.V.subgroupOf D.H) (pCore 2 D.H)
    (D.V₁.subgroupOf D.H) hc
  rw [←hseed,←subgroupOf_normalizer_eq h.plus_le_H] at hpres
  apply le_antisymm
  · intro x hx
    have hxP := hpres ((comap_mono (Subgroup.centralizer_le_normalizer _)) hx)
    exact (h.normalizer_control ⟨x.property,hxP⟩).2
  · rw [subgroupOf_normalizer_eq h.V_le_H]
    apply map_le_iff_le_comap.mp
    exact ((D.V.subgroupOf D.H).le_normalizer_map _).trans
      (normalizer_le_centralizer_of_card_two _ (h.star_module_card_two hi hn))

/-- F.9.5(3), with the original quotient and both normalizer images. -/
theorem star_centralizer_eq_normalizer_images
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) :
    centralizer ((D.V.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) :
      Set (D.H ⧸ pCore 2 D.H)) =
      ((D.H ⊓ normalizer (D.Vplus : Set G)).subgroupOf D.H).map
        (QuotientGroup.mk' (pCore 2 D.H)) ∧
    centralizer ((D.V.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) :
      Set (D.H ⧸ pCore 2 D.H)) =
      ((D.H ⊓ normalizer (D.V : Set G)).subgroupOf D.H).map
        (QuotientGroup.mk' (pCore 2 D.H)) := by
  have he := congrArg (map (QuotientGroup.mk' (pCore 2 D.H)))
    (h.star_centralizer_preimage hi hn)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
  have hv : (D.H ⊓ normalizer (D.V : Set G)).subgroupOf D.H =
      (normalizer (D.V : Set G)).subgroupOf D.H := by ext x; simp
  rw [h.normalizer_seed_eq_normalizer_module hi hn,hv]
  exact ⟨he,he⟩

theorem star_relative_centralizer_eq_normalizer_image
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) (K : Subgroup G) :
    (K.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) ⊓
      centralizer ((D.V.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) :
        Set (D.H ⧸ pCore 2 D.H)) =
      ((K ⊓ normalizer (D.V : Set G)).subgroupOf D.H).map
        (QuotientGroup.mk' (pCore 2 D.H)) := by
  ext x
  constructor
  · rintro ⟨⟨k,hk,rfl⟩,hc⟩
    have hnK : k∈(normalizer (D.V:Set G)).subgroupOf D.H :=
      (h.star_centralizer_preimage hi hn) ▸ hc
    exact ⟨k,⟨hk,hnK⟩,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    refine ⟨mem_map_of_mem _ hk.1,?_⟩
    change k ∈ (centralizer ((D.V.subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H)) : Set (D.H ⧸ pCore 2 D.H))).comap
        (QuotientGroup.mk' (pCore 2 D.H))
    rw [h.star_centralizer_preimage hi hn]
    exact hk.2

theorem module_normalizer_normalizes_local
    (hm : D.H ⊓ normalizer (D.V : Set G) ≤ normalizer (D.L : Set G)) :
    D.H ⊓ normalizer (D.V : Set G) ≤ normalizer (D.L₁ : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (D.L ⊓ D.Gz) (pResidual 2 (D.L ⊓ D.Gz : Subgroup G)))
  exact (le_inf hm (inf_le_left.trans (h.H_centralizes.trans D.Gz.le_normalizer))).trans
    inf_normalizer_le_normalizer_inf

theorem local_normal_of_module_normalizer
    (hm : D.H ⊓ normalizer (D.V : Set G) ≤ normalizer (D.L : Set G)) :
    (D.L₁.subgroupOf (D.H ⊓ normalizer (D.V : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer (h.module_normalizer_normalizes_local hm)

theorem star_centralizer_normalizes_local
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH)
    (hm : D.H ⊓ normalizer (D.V : Set G) ≤ normalizer (D.L : Set G)) :
    centralizer ((D.V.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) :
      Set (D.H ⧸ pCore 2 D.H)) ≤
      normalizer ((D.L₁.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) :
        Set (D.H ⧸ pCore 2 D.H)) := by
  rw [(h.star_centralizer_eq_normalizer_images hi hn).2]
  apply le_trans (map_mono ?_) ((D.L₁.subgroupOf D.H).le_normalizer_map _)
  rw [←subgroupOf_normalizer_eq (le_sup_left.trans h.local_le)]
  exact comap_mono (h.module_normalizer_normalizes_local hm)
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
