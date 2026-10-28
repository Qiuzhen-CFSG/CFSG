module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceExtraspecial
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CoreAction

/-!
# The original partner core and its ambient normalizer

The source extraspecial core has center equal to the original central
involutions. Thus the original partner Mc centralizes that center. Its
characteristic-two core lies inside the extraspecial core, forcing equality.
The full ambient normalizer is then exactly Mc. No marked triality
realization or ambient group recognition is used.

Source: Aschbacher--Smith 14.2.16 and 14.2.18, printed pp.986--987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePartnerCore
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

/-- The center of the original full H core is the original central involution group. -/
theorem first_core_center : centerIn (H.pCoreIn 2) = centralInvolutions T := by
  have hHC := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).2
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZH : centralInvolutions T ≤ H := (centralInvolutions_le_sylow T).trans hH.1.1.2
  have hZQ : centralInvolutions T ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 1) (by simpa using hZ))
      hZH (hHC.trans (Subgroup.centralizer_le_normalizer _))
  have hZC : centralInvolutions T ≤ centerIn (H.pCoreIn 2) := by
    intro z hz
    refine ⟨hZQ hz,?_⟩
    intro q hq
    exact (hHC (pCoreIn_le 2 H hq) z hz).symm
  have hC : Nat.card (centerIn (H.pCoreIn 2)) = 2 := by
    let := (source_core_structure hG T hempty hM hu hmany hcard e H hH eR).1
    rw [centerIn_eq_map_center,card_map_of_injective (H.pCoreIn 2).subtype_injective]
    exact IsExtraspecial.center_order_p 2 (H.pCoreIn 2)
  exact (eq_of_le_of_card_ge hZC (by omega)).symm

/-- The original partner is the ambient centralizer of the original core center. -/
theorem partner_centralizer :
    Mc = centralizer (centerIn (H.pCoreIn 2) : Set G) := by
  rw [first_core_center hG T hempty hM hu hmany hcard e H hH eR]
  exact (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The full original cores of Mc and H coincide in the ambient group. -/
theorem partner_core_eq : Mc.pCoreIn 2 = H.pCoreIn 2 := by
  have hHM : H ≤ Mc := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hQMc : H.pCoreIn 2 ≤ Mc := (pCoreIn_le 2 H).trans hHM
  let R := (H.pCoreIn 2).subgroupOf Mc
  let j : R ≃* H.pCoreIn 2 := subgroupOfEquivOfLe hQMc
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv j.symm
    (source_core_structure hG T hempty hM hu hmany hcard e H hH eR).1
  have hQR : pCore 2 Mc ≤ R := by
    intro q hq
    exact source_partner_core_le hG hempty hM hu hmany hcard e hH ⟨q,hq,rfl⟩
  have hcenter : (center R).map R.subtype ≤ center Mc := by
    rintro _ ⟨x,hx,rfl⟩
    have hxC : ((x : Mc) : G) ∈ centerIn (H.pCoreIn 2) := by
      rw [centerIn_eq_map_center]
      exact ⟨j x,(centerCongr j ⟨x,hx⟩).property,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hy : (y : G) ∈ centralizer (centerIn (H.pCoreIn 2) : Set G) := by
      rw [←partner_centralizer hG T hempty hM hu hmany hcard e H hH eR]
      exact y.property
    exact (hy _ hxC).symm
  have he := pCore_eq_of_extraspecial_overgroup R hQR hcenter
    (source_partner_characteristic_two hG hempty hM hu hmany hcard e hH)
  have hm := congrArg (Subgroup.map Mc.subtype) he
  rw [map_subgroupOf_eq_of_le hQMc] at hm
  exact hm

/-- The ambient normalizer of the original full H core is exactly Mc. -/
theorem first_core_normalizer_eq : normalizer (H.pCoreIn 2 : Set G) = Mc := by
  have hc : Nat.card (centerIn (H.pCoreIn 2)) = 2 := by
    rw [first_core_center hG T hempty hM hu hmany hcard e H hH eR]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hn : normalizer (H.pCoreIn 2 : Set G) ≤
      normalizer (centerIn (H.pCoreIn 2) : Set G) := normalizes_centerIn le_rfl
  have hle : normalizer (H.pCoreIn 2 : Set G) ≤ Mc := by
    rw [partner_centralizer hG T hempty hM hu hmany hcard e H hH eR]
    exact hn.trans (Subgroup.normalizer_le_centralizer_of_card_two _ hc)
  apply le_antisymm hle
  rw [←partner_core_eq hG T hempty hM hu hmany hcard e H hH eR]
  exact Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePartnerCore
