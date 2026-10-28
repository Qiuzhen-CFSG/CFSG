module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceComplementNormalizer
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The exact center of the original complement normalizer

The complement is centerless PSL₂(8), while the normalizer excess is the
original core's central involution. Thus the full normalizer has exactly
that same center. This identifies the central correction subgroup needed
by the original eight-endpoint reflection construction.
-/

noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceComplementCenter

private theorem center_join_central
    {E : Type*} [Group E] (K Z : Subgroup E)
    (hZ : Z ≤ center E) (hK : center K = ⊥) : centerIn (K ⊔ Z) = Z := by
  let : Z.Normal := ⟨by
    intro z hz g
    have hh := (mem_center_iff.mp (hZ hz) g)
    simpa only [hh,mul_inv_cancel_right] using hz⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨k,hk,z,hz,hxz⟩ := mem_sup_of_normal_right.mp hx.1
    have hxC : x ∈ centralizer (K : Set E) := fun y hy =>
      hx.2 y ((show K ≤ K ⊔ Z from le_sup_left) hy)
    have hzC : z ∈ centralizer (K : Set E) := fun y _ => mem_center_iff.mp (hZ hz) y
    have hkC : k ∈ centralizer (K : Set E) := by
      have he : k = x*z⁻¹ := eq_mul_inv_of_mul_eq hxz
      rw [he]
      exact (centralizer (K : Set E)).mul_mem hxC ((centralizer (K : Set E)).inv_mem hzC)
    have hkc : (⟨k,hk⟩ : K) ∈ center K := mem_center_iff.mpr fun y =>
      Subtype.ext (hkC y y.property)
    have hk1 : k = 1 := congrArg Subtype.val (hK.le hkc)
    have hzx : z = x := by simpa only [hk1,one_mul] using hxz
    rwa [← hzx]
  · intro z hz
    refine ⟨(show Z ≤ K ⊔ Z from le_sup_right) hz,?_⟩
    intro x _
    exact mem_center_iff.mp (hZ hz) x

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The full original complement normalizer has exactly the original
extraspecial-core central line as its center. -/
public theorem source_complement_normalizer_center (K : Subgroup H)
    (hK : (pCore 2 H).IsComplement' K) :
    centerIn (normalizer (K : Set H)) = (centerIn (H.pCoreIn 2)).subgroupOf H := by
  let Q := H.pCoreIn 2
  let Z := (centerIn Q).subgroupOf H
  let _ := (source_core_structure hG T hempty hM hu hmany hcard e H hH eR).1
  have hz2 : Nat.card (centerIn Q) = 2 := by
    rw [centerIn_eq_map_center,card_map_of_injective Q.subtype_injective]
    exact IsExtraspecial.center_order_p 2 Q
  have hHQ : H ≤ normalizer (Q : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hzC := centerIn_centralizes_of_card_two hz2 hHQ
  have hZ : Z ≤ center H := by
    intro z hz
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (hzC hz x x.property)
  let f := hK.symm.QuotientMulEquiv.symm.trans
    (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
  have hcK : center K = ⊥ := by
    apply bot_unique
    intro k hk
    have hc : f k ∈ center (Theory.PSL2.BinaryGroup 3) := (centerCongr f ⟨k,hk⟩).property
    have hf : f k = 1 := (Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot
      (F := GaloisField 2 3)).le hc
    exact f.injective (hf.trans (map_one f).symm)
  rw [(SourceComplementNormalizer.source_complement_normalizer
    hG T hempty hM hu hmany hcard e H hH eR K hK).2]
  exact center_join_central K Z hZ hcK

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceComplementCenter
