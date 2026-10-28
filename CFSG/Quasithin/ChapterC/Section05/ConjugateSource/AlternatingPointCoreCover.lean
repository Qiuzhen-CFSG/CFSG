module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointCoreAction
public import Theory.Representation.BinaryAlternatingFiveBorel.NormalizedTwoSubgroup

/-!
# Covering a paired point two-group by its two marked point cores

An invariant two-subgroup acts in each five-letter normalizer through the
marked Klein four. Matching these two images with point-core elements
leaves precisely the common module centralizer. The argument keeps that
centralizer explicit, so it also applies before its residual central factor
has been eliminated.

Source: Aschbacher–Smith, proof of 14.6.9(l), printed p.1027.
-/
public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open AlternatingFiveBorel
variable {G : Type*} [Group G] [Finite G] {R K L C W A : Subgroup G}

omit [Finite G] in
/-- The full normalizer action of a normalized two-group is in the marked four-group. -/
theorem AlternatingPairSetup.point_twoGroup_action_le
    (h : AlternatingPairSetup R K L)
    (hmark : ∀ k : K, (k : G) ∈ C ↔
      h.action (Subgroup.inclusion le_sup_left k) 4 = 4)
    (q : normalizer (K : Set G) →* FivePerm)
    (hcompat : ∀ s : (K ⊔ ChapterB.baumann R : Subgroup G),
      q (Subgroup.inclusion (sup_le K.le_normalizer h.normalizes) s) = h.action s)
    (hW : IsPGroup 2 W) (_hWN : W ≤ normalizer (K : Set G))
    (hn : K ⊓ C ≤ normalizer (W : Set G)) :
    (W.subgroupOf (normalizer (K : Set G))).map q ≤
      (pCore 2 B).map borelToPerm := by
  let P := W.subgroupOf (normalizer (K : Set G))
  apply normalizes_twoSubgroup_le_core _ (hW.comap_subtype.map q)
  intro a
  have ha : a.val.val ∈ (K.subgroupOf (K ⊔ ChapterB.baumann R)).map h.action :=
    h.block_image.symm ▸ a.val.property
  obtain ⟨k,hk,he⟩ := ha
  have hkc : (k : G) ∈ C := (hmark ⟨k,hk⟩).mpr (he ▸ a.property)
  let kN : normalizer (K : Set G) := ⟨k,K.le_normalizer hk⟩
  have hkN : kN ∈ normalizer (P : Set (normalizer (K : Set G))) := by
    intro w
    exact hn ⟨hk,hkc⟩ w
  have hqk : q kN = a.val.val := (hcompat k).trans he
  change a.val.val ∈ normalizer ((P.map q : Subgroup FivePerm) : Set FivePerm)
  rw [←hqk]
  exact P.le_normalizer_map q (mem_map_of_mem q hkN)

/-- Matching both marked actions leaves the literal common module centralizer. -/
theorem AlternatingPairSetup.paired_point_core_cover
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (hmark : ∀ k : K, (k : G) ∈ C ↔
      h.action (Subgroup.inclusion le_sup_left k) 4 = 4)
    (hmark' : ∀ k : L, (k : G) ∈ C ↔
      h'.action (Subgroup.inclusion le_sup_left k) 4 = 4)
    (hW : IsPGroup 2 W) (hWR : W ≤ R)
    (hWN : W ≤ normalizer (K : Set G) ⊓ normalizer (L : Set G))
    (hn : (K ⊓ C) ⊔ (L ⊓ C) ≤ normalizer (W : Set G))
    (hPKR : (K ⊓ C).pCoreIn 2 ≤ R) (hPLR : (L ⊓ C).pCoreIn 2 ≤ R)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) ≤ A) :
    W ≤ ((K ⊓ C).pCoreIn 2 ⊔ (L ⊓ C).pCoreIn 2) ⊔ A := by
  obtain ⟨q,hqker,hqc⟩ := h.exists_normalizer_action
  obtain ⟨q',hqker',hqc'⟩ := h'.exists_normalizer_action
  have hi := h.point_twoGroup_action_le hmark q hqc hW
    (hWN.trans inf_le_left) (le_sup_left.trans hn)
  have hi' := h'.point_twoGroup_action_le hmark' q' hqc' hW
    (hWN.trans inf_le_right) (le_sup_right.trans hn)
  intro w hw
  let wN : normalizer (K : Set G) := ⟨w,(hWN hw).1⟩
  let wN' : normalizer (L : Set G) := ⟨w,(hWN hw).2⟩
  obtain ⟨a,ha,hea⟩ := hi (mem_map_of_mem q (show wN ∈ W.subgroupOf _ from hw))
  obtain ⟨a',ha',hea'⟩ := hi' (mem_map_of_mem q' (show wN' ∈ W.subgroupOf _ from hw))
  obtain ⟨k,hkq⟩ := h.point_core_action_lift hmark q hqc a ha
  obtain ⟨l,hlq⟩ := h'.point_core_action_lift hmark' q' hqc' a' ha'
  have hkK : (k : G) ∈ K := (pCoreIn_le 2 _ k.property).1
  have hlL : (l : G) ∈ L := (pCoreIn_le 2 _ l.property).1
  have hkL : (k : G) ∈ centralizer (sourceModule L : Set G) :=
    (centralizer_le (map_subtype_le _)) (h'.commute hkK)
  have hlK : (l : G) ∈ centralizer (sourceModule K : Set G) :=
    (centralizer_le (map_subtype_le _)) (h.commute hlL)
  let kN : normalizer (K : Set G) := ⟨k,K.le_normalizer hkK⟩
  let lN : normalizer (K : Set G)  := ⟨l,Subgroup.centralizer_le_normalizer _ (h.commute hlL)⟩
  let kN' : normalizer (L : Set G)  := ⟨k,Subgroup.centralizer_le_normalizer _ (h'.commute hkK)⟩
  let lN' : normalizer (L : Set G) := ⟨l,L.le_normalizer hlL⟩
  have hlzero : q lN = 1 := hqker.ge hlK
  have hkzero : q' kN' = 1 := hqker'.ge hkL
  have hres : (k : G)⁻¹ * ((l : G)⁻¹ * w) ∈ A := by
    apply hfull
    refine ⟨R.mul_mem (R.inv_mem (hPKR k.property))
      (R.mul_mem (R.inv_mem (hPLR l.property)) (hWR hw)),?_⟩
    have hc : centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) =
        centralizer (sourceModule K : Set G) ⊓ centralizer (sourceModule L : Set G) := by
      apply le_antisymm
      · exact le_inf (centralizer_le (show sourceModule K ≤ sourceModule K ⊔ sourceModule L from le_sup_left))
          (centralizer_le (show sourceModule L ≤ sourceModule K ⊔ sourceModule L from le_sup_right))
      · apply le_centralizer_iff.mpr
        exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
    rw [hc]
    constructor
    · have hz : kN⁻¹ * (lN⁻¹ * wN) ∈ q.ker := by
        change q (kN⁻¹ * (lN⁻¹ * wN)) = 1
        rw [map_mul,map_inv,map_mul,map_inv,hlzero,inv_one,one_mul,hkq,←hea]
        exact inv_mul_cancel _
      exact hqker.le hz
    · have hz : kN'⁻¹ * (lN'⁻¹ * wN') ∈ q'.ker := by
        change q' (kN'⁻¹ * (lN'⁻¹ * wN')) = 1
        rw [map_mul,map_inv,map_mul,map_inv,hkzero,inv_one,one_mul,hlq,←hea']
        exact inv_mul_cancel _
      exact hqker'.le hz
  have hlk : (l : G) * (k : G) ∈ (K ⊓ C).pCoreIn 2 ⊔ (L ⊓ C).pCoreIn 2 := by
    simpa only [sup_comm] using
      (mul_mem_sup l.property k.property : (l : G) * (k : G) ∈
        (L ⊓ C).pCoreIn 2 ⊔ (K ⊓ C).pCoreIn 2)
  have hm := mul_mem_sup hlk hres
  simpa only [mul_assoc,mul_inv_cancel_left] using hm

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
